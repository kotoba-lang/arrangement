(ns arrangement.datalog
  "Conjunctive multi-clause Datalog join over `arrangement.query`'s single
  triple-pattern router -- the Datomic-shaped `:find`/`:where` surface this
  substrate was missing (`arrangement.query`/`kotobase-peer.core/q` are both
  single-`[s p o]`-pattern only, no variable binding across clauses).

  A clause is `[e a v]` where each position is a bound value, a logic
  variable (a symbol whose name starts with `?`, e.g. `?x`), or the
  wildcard `_`. `q` binds variables left-to-right across `:where` clauses
  via nested-loop join (each clause's still-unbound variables become
  wildcards in the pattern handed to `arrangement.query/query`; already-
  bound variables are substituted in as concrete values and re-checked
  against each candidate row), and projects the `:find` variables.

  ADR-2607061200 staged roadmap, Stage 2: negation (`(not [e a v])`
  clauses) and aggregation (`(count ?v)`/`(sum ?v)`/etc. in `:find`).
  Stage 3/4 (this landing): recursive rules -- Datomic-shaped `:rules`
  (`[[(rule-name ?a ?b) clause ...] ...]`, invoked from `:where` as
  `(rule-name ?x ?y)`), evaluated to a least fixpoint via semi-naive
  iteration. All three compose on top of the Stage 1 join without
  changing it, per the roadmap's own plan.

  **Negation and `visible?`** (security-relevant, not just a semantics
  choice): a `(not [e a v])` clause is evaluated through the exact same
  `visible?`-filtered `arrangement.query/query` as every positive clause.
  A caller-redacted fact and a genuinely absent fact are therefore
  indistinguishable to `not` -- `visible?` is a first-class effect
  (ADR-2607050500), so a query must never be able to infer a hidden fact's
  *presence* by testing its *absence*. This is why negation is NOT
  implemented as \"run the positive query, then set-difference against
  the unfiltered db\" -- that would leak exactly this way. Rule bodies
  thread the same `visible?` through every clause they contain (triple,
  `not`, or nested rule invocation), so this guarantee holds recursively.

  **Safe negation**: every logic variable inside a `(not [e a v])` clause
  must already be bound by an earlier positive clause IN THE SAME `:where`
  OR rule body (checked statically, before any join or fixpoint runs) --
  `not` only ever narrows an existing binding, it can never itself
  introduce or enumerate a variable's values. `_` (wildcard) is exempt --
  it doesn't bind, so `(not [?x :flag _])` (\"no flag fact of any value\")
  is always safe. `(not (rule-name ...))` -- negating a RULE invocation,
  not a plain triple pattern -- is deliberately NOT supported: combining
  recursion and negation soundly requires stratification (a rule may
  never negate itself, even transitively), which this landing does not
  implement; throws a clear error instead of silently misbehaving.

  **Rules and fixpoint**: `:rules` groups multiple named definitions,
  each `[(rule-name ?param ...) clause ...]` -- a rule name may have
  several definitions (each an alternative/OR branch, e.g. a recursive
  rule's base case and inductive case are two definitions of the same
  name). A `:where` (or another rule body's) clause `(rule-name ?arg ...)`
  joins against that rule's CURRENT materialized tuple set exactly like a
  triple clause joins against `db` -- arg positions may be bound values,
  logic variables (bound or not yet bound), or `_`.

  Evaluated via semi-naive least-fixpoint iteration: seed round derives
  whatever every rule's non-recursive (base-case) definitions produce
  from `db` alone; each subsequent round re-evaluates every definition
  once per rule-invocation clause position within it, using that
  position's rule's DELTA (newly-derived-last-round tuples) and every
  other rule-invocation's FULL (all tuples derived so far) -- the
  standard semi-naive rewriting, chosen over naive re-evaluation from the
  start so this doesn't need a later rewrite once real datasets make
  naive's full-recompute-every-round cost matter. Guaranteed to terminate
  (derivation is monotonic -- tuples are only ever added -- over `db`'s
  finite domain); a defensive iteration cap throws if the fixpoint
  somehow fails to converge, rather than looping forever.

  ADR-2607061200 query-language follow-up (this landing): `:in` (extra
  positional query parameters beyond `db`/`visible?`), predicate/function
  `:where` clauses (`[(> ?age 18)]`, `[(str ?a ?b) ?c]`, a WHITELISTED
  function registry -- see `query-fns` -- not arbitrary code execution),
  and `or`/`or-join` (union across alternative derivations). `not-join`
  (generalized negation over a multi-clause conjunction with explicit
  variable scoping, vs. today's single-triple `not`) is deliberately NOT
  included here -- a further follow-up, not a hidden gap."
  (:require [arrangement.core :as arr]
            [arrangement.query :as query]
            [arrangement.source :as source]
            [datom.source :as ds]
            [clojure.string :as str]
            [clojure.set :as set]))

(defn- scan*
  "Resolve one clause pattern against `db`, which may be EITHER a materialized
  db (the historical argument) or anything satisfying
  `datom.source/IPatternSource`.

  This one function is what puts the whole Datalog engine on top of the seam.
  Every clause resolution in this namespace goes through it, so swapping a
  cursor source in for a materialized db changes the cost of a join without
  changing a line of join logic — which is the point of having had a seam at
  all. `visible?` is applied identically in both branches; a source that
  filtered differently from `arrangement.query/query` would let a negation
  observe a fact a positive clause cannot see."
  [db pattern visible?]
  (if (satisfies? ds/IPatternSource db)
    (into #{} (filter visible?) (ds/scan db pattern))
    (query/query db pattern visible?)))

(defn- lvar?
  "True for a Datalog logic variable: a symbol whose name starts with `?`.
  `_` is the wildcard, not a variable -- it never binds."
  [x]
  (and (symbol? x) (not= x '_) (= \? (first (name x)))))

(defn- wildcard? [x] (= x '_))

(defn- substitute
  "`clause` position -> concrete `arrangement.query` pattern position: a
  wildcard or an unbound variable becomes `nil` (query's own wildcard);
  a bound variable becomes its current value; anything else passes through
  as the literal it already is."
  [term binding]
  (cond
    (wildcard? term) nil
    (lvar? term)     (get binding term)
    :else            term))

(defn- unify-positional
  "Extend `binding` with `terms`'s variables against one matched `values`
  seq (same order/count as `terms`). Returns the extended binding, or nil
  if a variable bound earlier in this same clause conflicts with another
  position's value (e.g. `[?x :likes ?x]` against a row where s != o).
  Used for both triple clauses (`terms`/`values` are `[e a v]`/`[s p o]`)
  and rule invocations (`terms`/`values` are the invocation's args/a
  matched tuple in the rule's own param order)."
  [binding terms values]
  (reduce (fn [b [term v]]
            (cond
              (or (wildcard? term) (not (lvar? term))) b
              (contains? b term) (if (= (get b term) v) b (reduced nil))
              :else (assoc b term v)))
          binding
          (map vector terms values)))

(defn- not-clause?
  "`(not [e a v])` -- a `:where` element that isn't itself a triple pattern
  but a negation of one. Distinguished from a positive `[e a v]` clause by
  being a seq (list) headed by the symbol `not`, vs. a vector."
  [x]
  (and (seq? x) (= 'not (first x))))

(defn- negated-pattern [not-clause] (second not-clause))

(def ^:private reserved-clause-heads
  "Symbols that head a special-form clause (`not`/`or`/`or-join`) rather
  than a rule invocation -- `rule-invocation?` excludes all of these, not
  just `not` (a clause `(or ...)` is not an attempted call to a rule
  literally named `or`)."
  #{'not 'or 'or-join 'and})

(defn- rule-invocation?
  "`(rule-name ?arg ...)` -- a `:where`/rule-body element that's neither a
  triple-pattern vector nor a special-form clause (`not`/`or`/`or-join`),
  but an invocation of a name declared in `:rules`."
  [x]
  (and (seq? x) (symbol? (first x)) (not (contains? reserved-clause-heads (first x)))))

(defn- rule-name [invocation] (first invocation))
(defn- rule-args [invocation] (vec (rest invocation)))

(defn- clause-lvars [pattern] (into #{} (filter lvar?) pattern))

(def ^:private query-fns
  "The WHITELISTED function registry predicate/function `:where` clauses
  may call (`[(fn-sym arg...)]` / `[(fn-sym arg...) result-var]`) --
  deliberately a fixed whitelist, not arbitrary code execution: a query is
  caller-supplied data in this codebase's threat model, same reasoning as
  `visible?`/rule invocations being data too, never `eval`'d source."
  {'<              <
   '>              >
   '<=             <=
   '>=             >=
   '=              =
   'not=           not=
   '+              +
   '-              -
   '*              *
   '/              /
   'str            str
   'count          count
   'ground         identity
   ;; String predicates. Deliberately NOT regex: a caller-supplied pattern is
   ;; a ReDoS vector, and a query is caller-supplied data in this codebase's
   ;; threat model (the same reasoning that makes this a whitelist at all).
   ;; These three are linear in their inputs and cannot backtrack.
   'starts-with?   str/starts-with?
   'ends-with?     str/ends-with?
   'includes?      str/includes?
   'lower-case     str/lower-case
   'upper-case     str/upper-case})

(defn- predicate-clause?
  "`[(fn-sym arg...)]` or `[(fn-sym arg...) result-var]` -- a `:where`
  element that's a VECTOR whose first element is itself a seq (the
  function-call form), distinguishing it from a plain `[e a v]` triple
  pattern (whose first element is never a seq)."
  [x]
  (and (vector? x) (seq? (first x))))

(defn- clause-fn-call [pred-clause] (first pred-clause))
(defn- clause-result-binding [pred-clause] (second pred-clause))
(defn- fn-call-sym [fn-call] (first fn-call))
(defn- fn-call-args [fn-call] (vec (rest fn-call)))

(defn- eval-fn-call [binding fn-call]
  (let [fsym (fn-call-sym fn-call)
        f (get query-fns fsym)]
    (when-not f
      (throw (ex-info "arrangement.datalog: unknown or disallowed function in query clause -- see query-fns for the whitelist"
                      {:fn fsym})))
    (apply f (map #(substitute % binding) (fn-call-args fn-call)))))

(defn- and-clause?
  "A multi-clause branch inside `or`/`or-join`, written the way Datomic writes
  it: `(and [?e :a 1] [?e :b 2])`.

  A branch used to be one clause, which meant a branch could not both BIND a
  variable and CONSTRAIN it -- so `(or-join [?e] (and [?e :age ?a] [(> ?a 18)]))`
  was inexpressible and every comparison inside a disjunction had to be
  refused. `and` is the form that makes a branch a conjunction; it is only
  meaningful inside `or`/`or-join`, where a branch position exists."
  [x] (and (seq? x) (= 'and (first x))))

(defn- and-clauses [x] (vec (rest x)))

(defn- or-clause? [x] (and (seq? x) (= 'or (first x))))
(defn- or-branches [x] (vec (rest x)))
(defn- or-join-clause? [x] (and (seq? x) (= 'or-join (first x))))
(defn- or-join-vars [x] (vec (second x)))
(defn- or-join-branches [x] (vec (rest (rest x))))

(defn- check-clause-safety!
  "Static pass over a `:where` vector or a rule body, in order (optionally
  seeded with `initial-bound`, used to check an `or`/`or-join` branch
  against whatever's already bound OUTSIDE it): every lvar inside a
  `(not [e a v])` clause, or every ARG lvar inside a predicate/function
  clause, must already have been bound by an earlier POSITIVE clause (a
  plain triple, a rule invocation, or a function clause's own result
  binding -- all bind the same way). Throws on the first violation
  instead of running an unsafe (unboundedly enumerable) negation/
  function-call, or if a `not`'s negated form isn't a plain triple
  pattern at all (negating a rule invocation isn't supported -- see ns
  docstring). `not`/predicate clauses never contribute new bindings; a
  function clause's `result-var` does. `or` checks every branch against
  the SAME outer `bound-so-far` (branches are alternatives, not
  sequential) and does not itself extend `bound-so-far` (branches aren't
  required to bind the same variables); `or-join` additionally makes its
  declared shared-vars available afterward."
  ([clauses] (check-clause-safety! clauses #{}))
  ([clauses initial-bound]
   (reduce (fn [bound-so-far clause]
             (cond
               (not-clause? clause)
               (let [pattern (negated-pattern clause)]
                 (when-not (vector? pattern)
                   (throw (ex-info "arrangement.datalog: negation of a rule invocation is not supported -- only (not [e a v]) triple patterns"
                                   {:clause clause})))
                 (let [unbound (set/difference (clause-lvars pattern) bound-so-far)]
                   (when (seq unbound)
                     (throw (ex-info "arrangement.datalog: unsafe negation -- variable(s) not bound by an earlier positive clause"
                                     {:clause clause :unbound unbound})))
                   bound-so-far))

               (predicate-clause? clause)
               (let [fn-call (clause-fn-call clause)
                     result-binding (clause-result-binding clause)
                     unbound (set/difference (clause-lvars (fn-call-args fn-call)) bound-so-far)]
                 ;; Checked HERE and not only in `eval-fn-call`, which never
                 ;; runs when no binding reaches the clause: a query naming a
                 ;; function that does not exist used to succeed silently
                 ;; whenever the result set was empty, which is the worst place
                 ;; to be lenient — it is exactly the case where a typo looks
                 ;; like a correct answer of "nothing matched".
                 (when-not (contains? query-fns (fn-call-sym fn-call))
                   (throw (ex-info "arrangement.datalog: unknown or disallowed function in query clause -- see query-fns for the whitelist"
                                   {:fn (fn-call-sym fn-call) :clause clause})))
                 (when (seq unbound)
                   (throw (ex-info "arrangement.datalog: unsafe function/predicate clause -- variable(s) not bound by an earlier clause"
                                   {:clause clause :unbound unbound})))
                 (if (lvar? result-binding) (conj bound-so-far result-binding) bound-so-far))

               (or-clause? clause)
               ;; An `and` branch is checked as the conjunction it is, so a
               ;; clause inside it may rely on one earlier in the SAME branch.
               (do (doseq [branch (or-branches clause)]
                     (check-clause-safety! (if (and-clause? branch) (and-clauses branch) [branch])
                                           bound-so-far))
                   bound-so-far)

               (or-join-clause? clause)
               (do (doseq [branch (or-join-branches clause)]
                     (check-clause-safety! (if (and-clause? branch) (and-clauses branch) [branch])
                                           bound-so-far))
                   (into bound-so-far (or-join-vars clause)))

               :else (into bound-so-far (clause-lvars clause))))
           initial-bound
           clauses)))

(def ^:private hash-join-row-budget
  "Prefer ONE broad scan plus an in-memory hash join over N keyed scans when
  the clause's whole relation is no larger than this multiple of N.

  Both sides of that comparison are real costs. A keyed scan is cheap per row
  but has a fixed cost per call -- and over `datom.source/IPatternSource` it
  may be a network round trip -- so N of them is N fixed costs. A broad scan
  is one fixed cost and `card` rows. Below the budget the single scan wins.

  4 is where the measured workload sits on either side without being near the
  line (kotobase-peer bench/results/2026-08-01-ic09-diagnosis.edn, LDBC SNB
  SF1 subset): `[?msg \"hasCreator\" ?f2]` is 7,355 rows against <=9,892
  distinct keys, so it hashes; `[?f1 \"knows\" ?f2]` is 361,246 rows against
  882 keys, so it does not -- and it must not, because that broad scan takes
  a second on its own. A starting point chosen to put those two on opposite
  sides, not a tuned constant."
  4)

(defn- broad-pattern
  "The clause with every variable and wildcard nil -- its literal constants
  only. Every substituted pattern for this clause is a specialization of it,
  so one scan of this returns a superset of what all of them would."
  [clause]
  (mapv (fn [t] (if (or (lvar? t) (wildcard? t)) nil t)) clause))

(defn- bound-positions
  "Indices where a substituted pattern pinned a value the broad pattern left
  open -- the columns a hash index for this pattern has to be keyed on."
  [pattern clause]
  (let [broad (broad-pattern clause)]
    (into [] (keep-indexed (fn [i v] (when (and (some? v) (nil? (nth broad i))) i))) pattern)))

(defn- hash-join-rows
  "One broad scan, indexed by whichever columns the substituted patterns
  pinned, then a lookup per distinct pattern. Groups whose patterns pin
  DIFFERENT columns each get their own index -- that only happens when
  bindings reaching this clause carry different variables (an `or` branch,
  say), and it stays correct rather than needing to be excluded."
  [groups clause db visible?]
  (let [rows (into [] (map (fn [q] [(:s q) (:p q) (:o q)])) (scan* db (broad-pattern clause) visible?))
        indexes (into {}
                      (map (fn [positions]
                             [positions (group-by (fn [r] (mapv #(nth r %) positions)) rows)]))
                      (distinct (map (fn [[pattern _]] (bound-positions pattern clause)) groups)))]
    (into #{}
          (mapcat (fn [[pattern group]]
                    (let [positions (bound-positions pattern clause)
                          key (mapv #(nth pattern %) positions)
                          matched (if (seq positions)
                                    (get (get indexes positions) key)
                                    rows)]
                      (mapcat (fn [binding]
                                (keep #(unify-positional binding clause %) matched))
                              group))))
          groups)))

(declare join-clause)

(defn- join-branch
  "One `or`/`or-join` branch against `bindings`: a conjunction when it is
  `(and ...)`, a single clause otherwise. Threading the bindings through the
  conjunction is what lets a branch bind a variable in one clause and constrain
  it in the next."
  [bindings branch db visible? extension-for cardinality]
  (if (and-clause? branch)
    (reduce (fn [bs c] (join-clause bs c db visible? extension-for cardinality))
            bindings
            (and-clauses branch))
    (join-clause bindings branch db visible? extension-for cardinality)))

(defn- join-clause
  "One step of the join: for every binding so far,
  - `(not [e a v])`: drop the binding iff the fully-substituted pattern
    has ANY `visible?`-filtered match against `db` -- keep it otherwise.
  - `(rule-name ?arg ...)`: resolve against `(extension-for rule-name)`
    (a set of tuples in that rule's own param order, supplied by the
    fixpoint driver or, for a rule-free query, `q` itself) exactly like a
    triple clause resolves against `db`.
  - `[(fn-sym arg...)]`: keep the binding iff the (whitelisted, see
    `query-fns`) function call returns truthy -- a predicate, binds
    nothing new.
  - `[(fn-sym arg...) result-var]`: compute the function call and unify
    `result-var` against it -- a function clause, binds `result-var`.
  - `(or clause1 clause2 ...)`: union of resolving EACH branch against
    the current bindings independently (an alternative/OR derivation,
    not a conjunction).
  - `(or-join [?shared...] clause1 clause2 ...)`: like `or`, but only
    `?shared` propagates back out of each branch (see `or-join-step`) --
    branches may use their own internal variable names for everything
    else.
  - `[e a v]`: resolve against `db` via `arrangement.query/query`.
  Triple and negation cases query through the same `visible?`-filtered
  `arrangement.query/query`, so a negation can never observe a fact
  `visible?` would hide (see the ns docstring)."
  ([bindings clause db visible? extension-for]
   (join-clause bindings clause db visible? extension-for nil))
  ([bindings clause db visible? extension-for cardinality]
  (cond
    (not-clause? clause)
    (let [pattern (negated-pattern clause)]
      (into #{}
            (remove (fn [binding]
                      (seq (scan* db (mapv #(substitute % binding) pattern) visible?))))
            bindings))

    (rule-invocation? clause)
    (let [args (rule-args clause)
          extension (extension-for (rule-name clause))]
      (into #{}
            (mapcat (fn [binding]
                      (let [substituted (mapv #(substitute % binding) args)
                            matches? (fn [tuple]
                                       (every? true? (map (fn [want got] (or (nil? want) (= want got)))
                                                           substituted tuple)))]
                        (keep #(unify-positional binding args %)
                              (filter matches? extension)))))
            bindings))

    (predicate-clause? clause)
    (let [fn-call (clause-fn-call clause)
          result-binding (clause-result-binding clause)]
      (if result-binding
        (into #{}
              (keep (fn [binding]
                      (unify-positional binding [result-binding] [(eval-fn-call binding fn-call)])))
              bindings)
        (into #{} (filter (fn [binding] (eval-fn-call binding fn-call))) bindings)))

    (or-clause? clause)
    (into #{} (mapcat (fn [branch] (join-branch bindings branch db visible? extension-for cardinality)))
          (or-branches clause))

    (or-join-clause? clause)
    (let [shared-vars (set (or-join-vars clause))
          branches (or-join-branches clause)]
      (into #{}
            (mapcat (fn [binding]
                      (into #{}
                            (mapcat (fn [branch]
                                      (into #{}
                                            (map (fn [extended]
                                                   (reduce (fn [b v]
                                                             (if (contains? extended v) (assoc b v (get extended v)) b))
                                                           binding
                                                           shared-vars)))
                                            (join-branch #{binding} branch db visible? extension-for cardinality))))
                            branches)))
            bindings))

    :else
    ;; One `scan*` per DISTINCT substituted pattern, not one per binding.
    ;;
    ;; Measured (kotobase-peer bench/results/2026-08-01-ic09-diagnosis.edn,
    ;; ADR-2608021000): LDBC SNB IC09's two-hop expansion spent 35.6 s of its
    ;; 45.3 s inside this function. The planner was not the problem -- it chose
    ;; the right clause order, and its cardinality probes were 8% of the time.
    ;; The cost was that a step carrying ~31,750 bindings issued ~31,750
    ;; separate `scan*` calls, each building its own result set and running
    ;; `visible?` over it, while those bindings substitute down to at most a
    ;; few thousand distinct patterns.
    ;;
    ;; Bindings sharing a substituted pattern now share one scan and are
    ;; unified against its rows individually, so the returned set is identical
    ;; row for row. This changes how often the source is asked, not what is
    ;; asked or what comes back -- which matters most for `IPatternSource`,
    ;; where every scan may be a network round trip.
    (let [groups (group-by (fn [binding] (mapv #(substitute % binding) clause)) bindings)
          card (get cardinality clause)]
      ;; ONE broad scan plus a hash join when the clause's whole relation is
      ;; small relative to the number of keyed scans it would replace;
      ;; otherwise a keyed scan per distinct pattern.
      ;;
      ;; Batching to one scan per distinct pattern (the previous change) took
      ;; IC09's two-hop join from 35.6 s to 2.1 s, but left it index-nested-
      ;; loop against Neo4j's 246 ms on the same data. The remaining shape is
      ;; a step that issues thousands of keyed scans against a relation with
      ;; only a few thousand rows in it -- reading the whole thing once is
      ;; strictly less work than reading most of it in pieces.
      ;;
      ;; `cardinality` is the planner's own per-clause row estimate, which it
      ;; already computes to order the clauses; without it (rule bodies, or a
      ;; caller that did not plan) this stays on the keyed path, which is the
      ;; safe default -- a broad scan of a large relation is exactly the
      ;; mistake the budget exists to avoid.
      (if (and card (<= card (* hash-join-row-budget (count groups))))
        (hash-join-rows groups clause db visible?)
        (into #{}
              (mapcat (fn [[pattern group]]
                        (let [rows (scan* db pattern visible?)]
                          (mapcat (fn [binding]
                                    (keep #(unify-positional binding clause [(:s %) (:p %) (:o %)])
                                          rows))
                                  group))))
              groups))))))

;; ── recursive rules: parsing + semi-naive fixpoint ──────────────────────────

(defn- parse-rules
  "`:rules` (`[[(rule-name ?a ?b) clause ...] ...]`) -> `{rule-name
  [{:params [?a ?b] :body [clause ...]} ...]}` -- a rule name maps to
  EVERY definition given for it (multiple definitions = alternative/OR
  derivations, e.g. a recursive rule's base case + inductive case).
  Validates every definition of the same name declares the same param
  COUNT (arity) -- Datomic itself requires this, and it's what lets a
  `:where`/body invocation be checked without knowing which definition
  will end up firing."
  [rules]
  (let [grouped (reduce (fn [acc [[rname & params] & body]]
                          (update acc rname (fnil conj []) {:params (vec params) :body (vec body)}))
                        {}
                        rules)]
    (doseq [[rname defs] grouped]
      (let [arities (into #{} (map (comp count :params)) defs)]
        (when (> (count arities) 1)
          (throw (ex-info "arrangement.datalog: rule definitions for the same name must all declare the same arity"
                          {:rule rname :arities arities})))))
    grouped))

(defn- check-unknown-rules!
  "Static pass: every `(rule-name ...)` invocation anywhere in `:where` or
  any rule body must name a rule actually defined in `:rules` -- throws
  immediately instead of silently joining against an empty extension."
  [clauses parsed-rules]
  (doseq [clause clauses
          :when (rule-invocation? clause)]
    (let [rname (rule-name clause)]
      (when-not (contains? parsed-rules rname)
        (throw (ex-info "arrangement.datalog: unknown rule invoked -- not defined in :rules"
                        {:rule rname})))
      (let [{:keys [params]} (first (get parsed-rules rname))]
        (when (not= (count params) (count (rule-args clause)))
          (throw (ex-info "arrangement.datalog: rule invoked with the wrong number of arguments"
                          {:rule rname :expected (count params) :got (count (rule-args clause))})))))))

(defn- eval-body-variant
  "Evaluate `body` (a conjunction of clauses) against `db`, where the
  rule-invocation clause at index `delta-idx` (if any) resolves against
  `delta-map`, and every OTHER rule-invocation clause resolves against
  `full-map` -- the semi-naive rewriting: one variant per rule-invocation
  position, so a round only re-derives combinations touching at least one
  tuple newly discovered LAST round, never recomputing purely-old ones."
  [db visible? body full-map delta-map delta-idx]
  (reduce
   (fn [bindings [i clause]]
     (join-clause bindings clause db visible?
                  (fn [rname] (if (= i delta-idx) (get delta-map rname #{}) (get full-map rname #{})))
                  nil))
   #{{}}
   (map-indexed vector body)))

(defn- project-params [bindings params]
  (into #{} (map (fn [binding] (mapv #(get binding %) params))) bindings))

(defn- rule-invocation-indices [body]
  (into [] (keep-indexed (fn [i clause] (when (rule-invocation? clause) i))) body))

(def ^:private max-fixpoint-iterations
  "Defensive cap, not a tuning knob: derivation is monotonic over `db`'s
  finite domain, so a correct fixpoint always converges long before this.
  Existing only to fail loudly (not hang) if it somehow doesn't."
  10000)

(defn- fixpoint
  "Semi-naive least fixpoint over every rule in `parsed-rules`. Returns
  `{rule-name #{tuple ...}}`, each tuple in that rule's own param order --
  ready to hand to `join-clause`'s `extension-for` for the top-level
  `:where` (or a caller evaluating one rule body against another's
  results, though this landing only nests rules through `:where`/bodies,
  never re-enters `fixpoint` itself)."
  [db visible? parsed-rules]
  (let [seed (reduce (fn [acc [rname defs]]
                       (assoc acc rname
                              (into #{} (mapcat (fn [{:keys [params body]}]
                                                  (project-params (eval-body-variant db visible? body {} {} -1) params)))
                                    defs)))
                     {}
                     parsed-rules)]
    (loop [full seed, delta seed, iterations 0]
      (when (> iterations max-fixpoint-iterations)
        (throw (ex-info "arrangement.datalog: fixpoint did not converge within the iteration cap"
                        {:iterations iterations})))
      (if (every? empty? (vals delta))
        full
        (let [candidates
              (reduce (fn [acc [rname defs]]
                        (assoc acc rname
                               (into #{}
                                     (mapcat (fn [{:keys [params body]}]
                                               (let [idxs (rule-invocation-indices body)]
                                                 (mapcat (fn [delta-idx]
                                                           (project-params (eval-body-variant db visible? body full delta delta-idx) params))
                                                         idxs))))
                                     defs)))
                      {}
                      parsed-rules)
              new-delta (into {} (map (fn [[rname _]]
                                        [rname (set/difference (get candidates rname #{}) (get full rname #{}))]))
                              parsed-rules)
              full' (merge-with set/union full new-delta)]
          (recur full' new-delta (inc iterations)))))))

(def ^:private aggregate-fns
  "Datomic-shaped `:find` aggregates. Each reduces the seq of one aggregate
  variable's bound values across a group of bindings. `min`/`max` on an
  empty group are `nil` (\"no minimum exists\"), not a thrown arity error;
  `avg` forces double division (`(double (count vals))`) so JVM/cljs/nbb
  agree -- integer `/` gives a Clojure ratio on JVM but a float on cljs."
  {'count          count
   'count-distinct (fn [vals] (count (distinct vals)))
   'sum            (fn [vals] (reduce + 0 vals))
   'avg            (fn [vals] (when (seq vals) (/ (reduce + 0 vals) (double (count vals)))))
   'min            (fn [vals] (when (seq vals) (apply min vals)))
   'max            (fn [vals] (when (seq vals) (apply max vals)))})

(defn- agg-find?
  "`(count ?v)`/`(sum ?v)`/etc. -- a `:find` element that isn't a plain
  projected variable but an aggregate over one."
  [x]
  (and (seq? x) (contains? aggregate-fns (first x))))

(defn- agg-fn [x] (get aggregate-fns (first x)))
(defn- agg-var [x] (second x))

(defn- form-lvars
  "Every logic variable anywhere in `form`, at any nesting depth. Deliberately
  structural rather than clause-aware: a triple, a `not`, an `or-join`, a
  function call and a rule invocation all just contain symbols, and
  over-approximating (keeping a variable that turns out not to be needed) is
  always safe while under-approximating drops a binding a later clause was
  going to join on."
  [form]
  (cond
    (lvar? form) #{form}
    (coll? form) (into #{} (mapcat form-lvars) form)
    :else #{}))

(defn- prune-bindings
  "Drop variables no remaining clause and no output needs.

  A binding set is a set, so removing a column MERGES bindings that differed
  only in it. That is the point: measured (kotobase-peer
  bench/results/2026-08-02-ic02-diagnosis.edn), LDBC IC09 carried 55,335
  bindings into a step that only ever used 8,130 distinct values of one
  variable -- the other 47,000 existed solely because two earlier variables
  were still along for the ride, and every one of them cost a substitution, a
  scan or a hash lookup, and a unification.

  `needed` must include every variable of every REMAINING clause (including
  ones nested in `or`/`not`/rule invocations) plus every `:find` element, or
  this silently deletes a join key."
  [bindings needed]
  (if (or (empty? bindings)
          (every? needed (keys (first bindings))))
    bindings
    (into #{} (map #(select-keys % needed)) bindings)))

(defn- project
  "`bindings` -> `:find`-ordered rows. With no aggregate `:find` elements,
  this is the original per-binding projection (a plain set of tuples, one
  per binding). With any aggregate element, the non-aggregate `:find`
  elements become GROUP-BY columns: bindings are partitioned by their
  values at those columns, and each aggregate column is computed once per
  group. An all-aggregate `:find` (no group-by columns) is Datomic's
  ungrouped-aggregate shape -- exactly one output row, computed over every
  binding as a single implicit group (so e.g. `(count ?e)` over zero
  matches is `#{[0]}`, not `#{}`)."
  [bindings find]
  (if (some agg-find? find)
    (let [group-vars (into [] (remove agg-find?) find)
          row (fn [group-bindings]
                (mapv (fn [f]
                        (if (agg-find? f)
                          ((agg-fn f) (mapv #(get % (agg-var f)) group-bindings))
                          (get (first group-bindings) f)))
                      find))]
      (if (empty? group-vars)
        #{(row bindings)}
        (into #{}
              (map (fn [[_ group-bindings]] (row group-bindings)))
              (group-by (fn [binding] (mapv #(get binding %) group-vars)) bindings))))
    (into #{} (map (fn [binding] (mapv #(get binding %) find))) bindings)))

(defn- flatten-clauses
  "`or`/`or-join` branches, flattened alongside their own clause -- so a
  static pass over the result also sees any rule invocation nested
  inside a branch, not just top-level `:where`/rule-body clauses."
  [clauses]
  (mapcat (fn [clause]
            (cond
              (or-clause? clause) (cons clause (flatten-clauses (or-branches clause)))
              (or-join-clause? clause) (cons clause (flatten-clauses (or-join-branches clause)))
              :else [clause]))
          clauses))

(defn- order-spec
  "Normalize `:order-by` into `[[find-position direction] ...]`. Each element
  is a `:find` element (a plain var, or an aggregate form written exactly as
  it appears in `:find`), optionally wrapped as `[element :asc|:desc]`.
  Ordering by something not in `:find` is rejected rather than silently
  ignored -- the rows being ordered ARE the projection, so a key outside it
  does not exist at this point."
  [find order-by]
  (mapv (fn [element]
          (let [[k dir] (if (and (vector? element) (#{:asc :desc} (second element)))
                          element
                          [element :asc])
                ;; portable index lookup -- this ns is .cljc and
                ;; `.indexOf` with a java.util.List hint does not exist on cljs
                idx (or (first (keep-indexed (fn [i e] (when (= e k) i)) find)) -1)]
            (when (neg? idx)
              (throw (ex-info "arrangement.datalog: :order-by key is not in :find"
                              {:key k :find find})))
            [idx dir]))
        order-by))

(defn- compare-rows [spec a b]
  (reduce (fn [_ [idx dir]]
            (let [c (compare (nth a idx) (nth b idx))
                  c (if (= dir :desc) (- c) c)]
              (if (zero? c) 0 (reduced c))))
          0 spec))

(defn- order+limit
  "Apply `:order-by` / `:limit` to a projected result.

  RETURN TYPE: without either key this returns the SET `project` produced,
  exactly as before. With either key it returns a VECTOR, because an ordered
  result is a sequence and a set cannot carry order -- a caller asking for
  ordering is asking for the thing a set cannot represent. `:limit` alone
  also returns a vector; without `:order-by` WHICH rows come back is
  unspecified (the set's iteration order), so a bare `:limit` is only
  meaningful for `count`-style probes, not for top-N.

  WHAT THIS IS NOT: the limit is applied to the finished projection, so the
  join still does all of its work. It makes top-N EXPRESSIBLE -- the caller
  no longer sorts the whole result in host code -- but it does not yet make
  it cheaper. Pushing a limit into the join needs the ordering clause to
  drive iteration, which is possible here because the value-ordered index
  already yields `[p o s]` in `o` order; that is a separate change and is
  not claimed by this one."
  [rows find order-by limit]
  (if (and (empty? order-by) (nil? limit))
    rows
    (let [spec (order-spec find order-by)
          ordered (if (seq spec)
                    (vec (sort #(compare-rows spec %1 %2) rows))
                    (vec rows))]
      (if limit (vec (take limit ordered)) ordered))))

(defn- plain-triple?
  "A positive `[e a v]` clause -- not a `not`, `or`, `or-join`, rule
  invocation, or function/predicate call. Those are seq-shaped or shorter;
  a plain triple is a 3-vector whose first position is not a call form."
  [clause]
  (and (vector? clause) (= 3 (count clause)) (not (seq? (first clause)))))

(defn- run-clauses
  "Fold `clauses` over `bindings`, pruning between steps exactly as `q` does.
  Extracted so the ordered-driver path below runs the REMAINING clauses through
  the same code as the ordinary path -- a second copy of the join loop is how
  the two would drift."
  [bindings clauses db visible? extension-for cardinality find prune?]
  (reduce (fn [bs [i clause]]
            (let [bs' (join-clause bs clause db visible? extension-for cardinality)]
              (if prune?
                (prune-bindings bs' (into (form-lvars find)
                                          (form-lvars (subvec (vec clauses) (inc i)))))
                bs')))
          bindings
          (map-indexed vector clauses)))

(defn- ordered-driver
  "The clause an ordered scan can be driven from, as
  `{:clause .. :attr .. :subject-var .. :key-var .. :desc? ..}`, or nil.

  Requirements, each one load-bearing:
  - a `:limit`, and an `:order-by` whose FIRST key is a plain variable (later
    keys only break ties inside a value group, which this always drains whole);
  - that variable is bound by exactly ONE `:where` clause -- otherwise the
    value a group fixes is not the value the row sorts by;
  - in that clause's VALUE position, with a literal attribute and a variable
    subject, so `:pos` can enumerate the distinct values;
  - every `:where` clause is a plain triple. A `not`/`or`/rule/function clause
    can bind or reject in ways this scan cannot reason about in value order.

  When any of these fails the caller runs the ordinary path, which is always
  correct and never slower than it was."
  [where find order-by limit]
  (when (and limit (seq order-by) (every? plain-triple? where))
    (let [k (let [e (first order-by)] (if (vector? e) (first e) e))
          desc? (let [e (first order-by)] (and (vector? e) (= :desc (second e))))]
      (when (and (lvar? k) (some #{k} find))
        (let [carriers (filter (fn [[_ a v]] (and (= v k) (string? a))) where)]
          (when (and (= 1 (count carriers))
                     (= 1 (count (filter (fn [c] (contains? (clause-lvars c) k)) where))))
            (let [[sv a _] (first carriers)]
              (when (lvar? sv)
                {:clause (first carriers) :attr a :subject-var sv :key-var k :desc? desc?}))))))))

(defn q
  "`{:find [?var ...] :in [?param ...] :where [[e a v] ...] :rules [...]}`
  over `db`. `visible?` is required and threaded into every underlying
  `arrangement.query/query` call, same convention as `arrangement.query`
  itself (ADR-2607050500). Returns a set of `:find`-ordered vectors --
  `nil` for any plain `:find` var a clause never bound (e.g. wildcard-only
  clauses).

  `:where` clauses may be:
    - `(not [e a v])` (see ns docstring for the `visible?`/safety contract)
    - `(rule-name ?arg ...)`, invoking a `:rules` definition
    - `[(fn-sym arg...)]` / `[(fn-sym arg...) result-var]`, a whitelisted
      predicate/function call (see `query-fns`)
    - `(or clause ...)` / `(or-join [?shared ...] clause ...)`, union
      across alternative derivations
  `:find` elements may be `(count ?v)`, `(count-distinct ?v)`, `(sum ?v)`,
  `(avg ?v)`, `(min ?v)`, or `(max ?v)` alongside plain variables, which
  then act as GROUP-BY columns (see `project`).

  `:in` (optional) declares extra query parameters -- `inputs` (a 4th,
  optional arg, positional, same order as `:in`) supplies their values.
  `'$` in `:in` is accepted as a no-op placeholder for `db` itself
  (already passed separately); every other symbol consumes one value
  from `inputs`, pre-bound before `:where` runs.

  `:rules` (optional; omit or `[]` for plain Stage 1/2 queries, unchanged)
  is `[[(rule-name ?param ...) clause ...] ...]` -- see ns docstring for
  the fixpoint/semi-naive contract, safety, and the `visible?` guarantee
  extending recursively into rule bodies.

  `:order-by` / `:limit` (optional) make top-N expressible in the query
  instead of in host code. `:order-by` is a vector of `:find` elements,
  each optionally `[element :asc|:desc]` (default `:asc`); a key that is
  not in `:find` is an error, not a no-op. Supplying either key changes
  the return type from a SET to a VECTOR, because an ordered result is a
  sequence. `:limit` without `:order-by` returns an unspecified subset --
  useful for probes, not for top-N.

  `:clause-cardinality` (optional) is `{clause estimated-rows}` -- a
  planner's own per-clause row estimate, which it already computes in
  order to choose a clause order. When a clause's whole relation is small
  relative to the number of keyed scans a join step would issue for it,
  the executor reads that relation ONCE and hash-joins instead. Omit it
  and every step stays on the keyed path, which is the safe default: a
  broad scan of a large relation is the mistake the budget avoids, and a
  hint that is absent is not a hint that is wrong. It never changes an
  answer -- see `hash-join-rows` and the equivalence tests.

  These are applied to the finished projection: the join still does all
  of its work, so this makes top-N SAYABLE, not yet cheaper. Every LDBC
  SNB complex read is a \"most recent N\" query, and until this existed a
  caller had to materialize the whole join and sort it in host code
  (kotobase-peer bench/results/2026-08-01-ldbc-snb-interactive.edn did
  exactly that, and said so). Pushing the limit into the join is a
  separate change -- see `order+limit`."
  ([db query visible?] (q db query visible? []))
  ([db {:keys [find where rules in order-by limit clause-cardinality]} visible? inputs]
   (let [in-syms (vec (remove #{'$} (or in [])))
         initial-binding (into {} (map vector in-syms inputs))
         parsed-rules (parse-rules (or rules []))
         all-clauses (flatten-clauses (into where (mapcat :body) (mapcat val parsed-rules)))]
     (check-clause-safety! where (set in-syms))
     (doseq [[_ defs] parsed-rules] (doseq [{:keys [body]} defs] (check-clause-safety! body)))
     (check-unknown-rules! all-clauses parsed-rules)
     (let [full (fixpoint db visible? parsed-rules)
           extension-for #(get full % #{})
           ;; With an aggregate in :find, binding MULTIPLICITY is observable --
           ;; `project` computes each aggregate over the bindings in its group,
           ;; so two bindings differing only in a column nobody reads are two
           ;; rows to `(count ?x)`. Pruning would merge them and change the
           ;; answer, so it is off entirely in that case rather than
           ;; conditionally per column.
           prune? (not (some agg-find? find))
           driver (when prune? (ordered-driver where find order-by limit))]
       (if driver
         ;; ORDERED DRIVE. Walk the driver clause's distinct values in sort
         ;; order, join each value's rows through the remaining clauses, and
         ;; stop once `limit` distinct output rows exist. Sound because every
         ;; row produced from a value group sorts by that value, groups are
         ;; walked in order, and a group is always drained whole -- so once
         ;; `limit` rows are in hand, nothing unvisited can outrank them, and
         ;; secondary sort keys only reorder within a group already complete.
         ;;
         ;; Why it is worth the branch: measured (kotobase-peer
         ;; bench/results/2026-08-02-ldbc-snb-after-join-work.edn), LDBC IC02
         ;; matches 910 of 7,355 messages, so a date-ordered walk stopping at
         ;; 20 touches roughly 160 rows instead of joining all 7,355 -- and
         ;; every LDBC SNB complex read is a most-recent-N query.
         (let [{:keys [clause attr subject-var key-var desc?]} driver
               rest-clauses (vec (remove #{clause} where))
               values (sort (if desc? #(compare %2 %1) compare)
                            (arr/values-for-predicate db attr))
               enough? (fn [rows] (>= (count rows) limit))]
           (order+limit
            (reduce (fn [rows v]
                      (if (enough? rows)
                        (reduced rows)
                        (let [seed (into #{}
                                         (map (fn [{:keys [s]}]
                                                (assoc initial-binding subject-var s key-var v)))
                                         (scan* db [nil attr v] visible?))
                              bs (run-clauses seed rest-clauses db visible?
                                              extension-for clause-cardinality find prune?)]
                          (into rows (project bs find)))))
                    #{} values)
            find order-by limit))
         (let [bindings (run-clauses #{initial-binding} (vec where) db visible?
                                     extension-for clause-cardinality find prune?)]
           (order+limit (project bindings find) find order-by limit)))))))
