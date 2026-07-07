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

  ADR-2607061200 staged roadmap, Stage 2 (this landing): negation
  (`(not [e a v])` clauses) and aggregation (`(count ?v)`/`(sum ?v)`/etc.
  in `:find`). Both compose on top of the Stage 1 join without changing
  it, per the roadmap's own plan.

  Deliberately still NOT here (Stage 3/4, unscheduled): recursive rules
  (`:rules` + naive/semi-naive fixpoint) and any stratification that would
  come with combining recursion and negation.

  **Negation and `visible?`** (security-relevant, not just a semantics
  choice): a `(not [e a v])` clause is evaluated through the exact same
  `visible?`-filtered `arrangement.query/query` as every positive clause.
  A caller-redacted fact and a genuinely absent fact are therefore
  indistinguishable to `not` -- `visible?` is a first-class effect
  (ADR-2607050500), so a query must never be able to infer a hidden fact's
  *presence* by testing its *absence*. This is why negation is NOT
  implemented as \"run the positive query, then set-difference against
  the unfiltered db\" -- that would leak exactly this way.

  **Safe negation**: every logic variable inside a `(not [e a v])` clause
  must already be bound by an earlier positive `:where` clause (checked
  statically, before any join runs, over the whole `:where` vector) --
  `not` only ever narrows an existing binding, it can never itself
  introduce or enumerate a variable's values. `_` (wildcard) is exempt --
  it doesn't bind, so `(not [?x :flag _])` (\"no flag fact of any value\")
  is always safe."
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

(defn- unify
  "Extend `binding` with `clause`'s variables against one matched `row`
  (`{:s :p :o}`). Returns the extended binding, or nil if a variable bound
  earlier in this same clause conflicts with `row`'s value at another
  position (e.g. `[?x :likes ?x]` against a row where s != o)."
  [binding clause row]
  (reduce (fn [b [term slot]]
            (cond
              (or (wildcard? term) (not (lvar? term))) b
              (contains? b term) (if (= (get b term) (get row slot)) b (reduced nil))
              :else (assoc b term (get row slot))))
          binding
          (map vector clause [:s :p :o])))

(defn- not-clause?
  "`(not [e a v])` -- a `:where` element that isn't itself a triple pattern
  but a negation of one. Distinguished from a positive `[e a v]` clause by
  being a seq (list) headed by the symbol `not`, vs. a vector."
  [x]
  (and (seq? x) (= 'not (first x))))

(defn- negated-pattern [not-clause] (second not-clause))

(defn- clause-lvars [pattern] (into #{} (filter lvar?) pattern))

(defn- check-negation-safety!
  "Static pass over `where`, in order: every lvar inside a `(not [e a v])`
  clause must already have been bound by an earlier POSITIVE clause.
  Throws on the first violation instead of running an unsafe (unboundedly
  enumerable) negation. `not` clauses never contribute new bindings, so
  they don't extend `bound-so-far` for later clauses either."
  [where]
  (reduce (fn [bound-so-far clause]
            (if (not-clause? clause)
              (let [unbound (set/difference (clause-lvars (negated-pattern clause)) bound-so-far)]
                (when (seq unbound)
                  (throw (ex-info "arrangement.datalog: unsafe negation -- variable(s) not bound by an earlier positive :where clause"
                                  {:clause clause :unbound unbound})))
                bound-so-far)
              (into bound-so-far (clause-lvars clause))))
          #{}
          where))

(defn- join-clause
  "One step of the join: for every binding so far, either (positive clause)
  resolve `clause` against `db` and extend the binding with each matching
  row's new variables, or (negative clause, `(not [e a v])`) drop the
  binding iff the fully-substituted pattern has ANY `visible?`-filtered
  match -- keep it otherwise. Both cases query through the same
  `visible?`-filtered `arrangement.query/query`, so a negation can never
  observe a fact `visible?` would hide (see the ns docstring)."
  [bindings clause db visible?]
  (if (not-clause? clause)
    (let [pattern (negated-pattern clause)]
      (into #{}
            (remove (fn [binding]
                      (seq (query/query db (mapv #(substitute % binding) pattern) visible?))))
            bindings))
    (into #{}
          (mapcat (fn [binding]
                    (let [pattern (mapv #(substitute % binding) clause)]
                      (keep #(unify binding clause %)
                            (query/query db pattern visible?)))))
          bindings)))

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
  "`{:find [?var ...] :where [[e a v] ...]}` over `db`. `visible?` is
  required and threaded into every underlying `arrangement.query/query`
  call, same convention as `arrangement.query` itself (ADR-2607050500).
  Returns a set of `:find`-ordered vectors -- `nil` for any plain `:find`
  var a clause never bound (e.g. wildcard-only clauses).

  `:where` clauses may be `(not [e a v])` (see ns docstring for the
  `visible?`/safety contract). `:find` elements may be `(count ?v)`,
  `(count-distinct ?v)`, `(sum ?v)`, `(avg ?v)`, `(min ?v)`, or `(max ?v)`
  alongside plain variables, which then act as GROUP-BY columns (see
  `project`)."
  [db {:keys [find where]} visible?]
  (check-negation-safety! where)
  (let [bindings (reduce (fn [bindings clause] (join-clause bindings clause db visible?))
                         #{{}}
                         where)]
    (project bindings find)))
