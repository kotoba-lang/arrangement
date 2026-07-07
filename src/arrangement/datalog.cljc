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
  somehow fails to converge, rather than looping forever."
  (:require [arrangement.query :as query]
            [clojure.set :as set]))

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

(defn- rule-invocation?
  "`(rule-name ?arg ...)` -- a `:where`/rule-body element that's neither a
  triple-pattern vector nor a `(not ...)` negation, but an invocation of a
  name declared in `:rules`."
  [x]
  (and (seq? x) (symbol? (first x)) (not= 'not (first x))))

(defn- rule-name [invocation] (first invocation))
(defn- rule-args [invocation] (vec (rest invocation)))

(defn- clause-lvars [pattern] (into #{} (filter lvar?) pattern))

(defn- check-negation-safety!
  "Static pass over a `:where` vector or a rule body, in order: every lvar
  inside a `(not [e a v])` clause must already have been bound by an
  earlier POSITIVE clause (a plain triple, or a rule invocation -- both
  bind the same way). Throws on the first violation instead of running
  an unsafe (unboundedly enumerable) negation, or if the negated form
  isn't a plain triple pattern at all (negating a rule invocation isn't
  supported -- see ns docstring). `not` clauses never contribute new
  bindings, so they don't extend `bound-so-far` for later clauses either."
  [clauses]
  (reduce (fn [bound-so-far clause]
            (if (not-clause? clause)
              (let [pattern (negated-pattern clause)]
                (when-not (vector? pattern)
                  (throw (ex-info "arrangement.datalog: negation of a rule invocation is not supported -- only (not [e a v]) triple patterns"
                                  {:clause clause})))
                (let [unbound (set/difference (clause-lvars pattern) bound-so-far)]
                  (when (seq unbound)
                    (throw (ex-info "arrangement.datalog: unsafe negation -- variable(s) not bound by an earlier positive clause"
                                    {:clause clause :unbound unbound})))
                  bound-so-far))
              (into bound-so-far (clause-lvars clause))))
          #{}
          clauses))

(defn- join-clause
  "One step of the join: for every binding so far,
  - `(not [e a v])`: drop the binding iff the fully-substituted pattern
    has ANY `visible?`-filtered match against `db` -- keep it otherwise.
  - `(rule-name ?arg ...)`: resolve against `(extension-for rule-name)`
    (a set of tuples in that rule's own param order, supplied by the
    fixpoint driver or, for a rule-free query, `q` itself) exactly like a
    triple clause resolves against `db`.
  - `[e a v]`: resolve against `db` via `arrangement.query/query`.
  Triple and negation cases query through the same `visible?`-filtered
  `arrangement.query/query`, so a negation can never observe a fact
  `visible?` would hide (see the ns docstring)."
  [bindings clause db visible? extension-for]
  (cond
    (not-clause? clause)
    (let [pattern (negated-pattern clause)]
      (into #{}
            (remove (fn [binding]
                      (seq (query/query db (mapv #(substitute % binding) pattern) visible?))))
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

    :else
    (into #{}
          (mapcat (fn [binding]
                    (let [pattern (mapv #(substitute % binding) clause)]
                      (keep #(unify-positional binding clause [(:s %) (:p %) (:o %)])
                            (query/query db pattern visible?)))))
          bindings)))

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
                  (fn [rname] (if (= i delta-idx) (get delta-map rname #{}) (get full-map rname #{})))))
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

(defn q
  "`{:find [?var ...] :where [[e a v] ...] :rules [...]}` over `db`.
  `visible?` is required and threaded into every underlying
  `arrangement.query/query` call, same convention as `arrangement.query`
  itself (ADR-2607050500). Returns a set of `:find`-ordered vectors --
  `nil` for any plain `:find` var a clause never bound (e.g. wildcard-only
  clauses).

  `:where` clauses may be `(not [e a v])` (see ns docstring for the
  `visible?`/safety contract) or `(rule-name ?arg ...)`, invoking a
  `:rules` definition. `:find` elements may be `(count ?v)`,
  `(count-distinct ?v)`, `(sum ?v)`, `(avg ?v)`, `(min ?v)`, or `(max ?v)`
  alongside plain variables, which then act as GROUP-BY columns (see
  `project`).

  `:rules` (optional; omit or `[]` for plain Stage 1/2 queries, unchanged)
  is `[[(rule-name ?param ...) clause ...] ...]` -- see ns docstring for
  the fixpoint/semi-naive contract, safety, and the `visible?` guarantee
  extending recursively into rule bodies."
  [db {:keys [find where rules]} visible?]
  (let [parsed-rules (parse-rules (or rules []))
        all-clauses (into where (mapcat :body) (mapcat val parsed-rules))]
    (check-negation-safety! where)
    (doseq [[_ defs] parsed-rules] (doseq [{:keys [body]} defs] (check-negation-safety! body)))
    (check-unknown-rules! all-clauses parsed-rules)
    (let [full (fixpoint db visible? parsed-rules)
          bindings (reduce (fn [bindings clause]
                             (join-clause bindings clause db visible? #(get full % #{})))
                           #{{}}
                           where)]
      (project bindings find))))
