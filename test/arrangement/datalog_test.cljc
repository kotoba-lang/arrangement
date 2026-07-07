(ns arrangement.datalog-test
  (:require [clojure.test :refer [deftest is testing]]
            [arrangement.core :as arr]
            [arrangement.datalog :as dl]))

(defn- fixture-db []
  (-> (arr/empty-db)
      (arr/assert-quad {:s "alice" :p "role" :o "admin"})
      (arr/assert-quad {:s "alice" :p "name" :o "Alice"})
      (arr/assert-quad {:s "bob" :p "role" :o "user"})
      (arr/assert-quad {:s "bob" :p "name" :o "Bob"})
      (arr/assert-quad {:s "carol" :p "role" :o "admin"})
      (arr/assert-quad {:s "carol" :p "name" :o "Carol"})))

(def ^:private everything (constantly true))

(deftest single-clause-behaves-like-arrangement-query
  (let [db (fixture-db)]
    (is (= #{["alice"] ["carol"]}
           (dl/q db {:find '[?s] :where '[[?s "role" "admin"]]} everything)))))

(deftest two-clause-join-on-shared-variable
  (let [db (fixture-db)]
    (testing "?s shared between clauses restricts to admins, then projects their name"
      (is (= #{["Alice"] ["Carol"]}
             (dl/q db {:find '[?name]
                       :where '[[?s "role" "admin"]
                                [?s "name" ?name]]}
                   everything))))))

(deftest three-clause-chain-join
  (let [db (fixture-db)]
    (is (= #{["alice" "admin" "Alice"] ["carol" "admin" "Carol"]}
           (dl/q db {:find '[?s ?role ?name]
                     :where '[[?s "role" ?role]
                              [?s "role" "admin"]
                              [?s "name" ?name]]}
                 everything)))))

(deftest no-shared-variable-is-a-cartesian-product
  (let [db (fixture-db)]
    (is (= #{["alice" "Bob"] ["alice" "Carol"] ["alice" "Alice"]
             ["bob" "Bob"] ["bob" "Carol"] ["bob" "Alice"]
             ["carol" "Bob"] ["carol" "Carol"] ["carol" "Alice"]}
           (dl/q db {:find '[?s ?name]
                     :where '[[?s "role" _]
                              [_ "name" ?name]]}
                 everything)))))

(deftest conflicting-binding-yields-empty-result
  (let [db (fixture-db)]
    (testing "?x can't be both alice's own subject and match a name it never has"
      (is (= #{}
             (dl/q db {:find '[?x]
                       :where '[[?x "role" "admin"]
                                [?x "name" "Bob"]]}
                   everything))))))

(deftest repeated-variable-within-one-clause-self-joins
  (let [db (-> (arr/empty-db)
               (arr/assert-quad {:s "alice" :p "knows" :o "alice"})
               (arr/assert-quad {:s "bob" :p "knows" :o "carol"}))]
    (is (= #{["alice"]}
           (dl/q db {:find '[?x] :where '[[?x "knows" ?x]]} everything)))))

(deftest visible-is-required
  (is (thrown? #?(:clj clojure.lang.ArityException :cljs js/Error)
               (dl/q (fixture-db) {:find '[?s] :where '[[?s "role" "admin"]]}))))

(deftest visible-applies-per-clause
  (let [db (fixture-db)
        no-bob (fn [{:keys [s]}] (not= "bob" s))]
    (is (= #{["Alice"] ["Carol"]}
           (dl/q db {:find '[?name]
                     :where '[[?s "role" _]
                              [?s "name" ?name]]}
                 no-bob)))))

;; ── negation (ADR-2607061200 Stage 2) ───────────────────────────────────────

(deftest not-clause-excludes-matching-bindings
  (let [db (fixture-db)]
    (testing "everyone who has a name but is NOT an admin"
      (is (= #{["bob"]}
             (dl/q db {:find '[?s]
                       :where '[[?s "name" _]
                                (not [?s "role" "admin"])]}
                   everything))))))

(deftest not-clause-with-wildcard-value-excludes-any-value
  (let [db (-> (fixture-db)
               (arr/assert-quad {:s "dave" :p "name" :o "Dave"}))]
    (testing "dave has a name but no role fact at all -- (not [?s \"role\" _]) keeps him"
      (is (= #{["dave"]}
             (dl/q db {:find '[?s]
                       :where '[[?s "name" _]
                                (not [?s "role" _])]}
                   everything))))))

(deftest not-clause-can-reference-multiple-earlier-bound-vars
  (let [db (fixture-db)]
    (testing "?s bound by clause 1, ?role bound by clause 2, both usable inside (not ...)"
      (is (= #{["bob" "user"]}
             (dl/q db {:find '[?s ?role]
                       :where '[[?s "name" _]
                                [?s "role" ?role]
                                (not [?s "role" "admin"])]}
                   everything))))))

(deftest unbound-variable-inside-not-clause-throws
  (let [db (fixture-db)]
    (testing "?role is never bound by a positive clause before the negation -- unsafe, must throw"
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                             #"unsafe negation"
                             (dl/q db {:find '[?s]
                                       :where '[[?s "name" _]
                                                (not [?s "role" ?role])]}
                                   everything))))))

(deftest not-clause-wildcard-inside-is-always-safe
  (let [db (fixture-db)]
    (testing "a wildcard inside (not ...) never needs to be bound -- no throw"
      (is (= #{["alice"] ["carol"]}
             (dl/q db {:find '[?s]
                       :where '[[?s "role" "admin"]
                                (not [?s "banned" _])]}
                   everything))))))

(deftest not-clause-respects-visible-just-like-a-positive-clause
  (let [db (fixture-db)
        ;; carol's admin-role fact is HIDDEN from this caller -- to them it
        ;; must look exactly as absent as bob's genuinely-missing admin fact.
        hide-carols-admin-fact (fn [{:keys [s p o]}] (not (and (= s "carol") (= p "role") (= o "admin"))))]
    (testing "carol really IS an admin, but this caller can't see that fact -- (not [?s \"role\" \"admin\"]) must keep her, exactly like bob (a genuine non-admin)"
      (is (= #{["bob"] ["carol"]}
             (dl/q db {:find '[?s]
                       :where '[[?s "name" _]
                                (not [?s "role" "admin"])]}
                   hide-carols-admin-fact))
          "without redaction only bob would pass (carol really is an admin); the caller's visible? makes carol indistinguishable from a real non-admin"))))

;; ── aggregation (ADR-2607061200 Stage 2) ────────────────────────────────────

(deftest count-aggregate-ungrouped
  (let [db (fixture-db)]
    (is (= #{[3]}
           (dl/q db {:find '[(count ?s)] :where '[[?s "name" _]]} everything)))))

(deftest count-aggregate-grouped-by-role
  (let [db (fixture-db)]
    (is (= #{["admin" 2] ["user" 1]}
           (dl/q db {:find '[?role (count ?s)] :where '[[?s "role" ?role]]} everything)))))

(deftest count-distinct-aggregate
  (let [db (-> (arr/empty-db)
               (arr/assert-quad {:s "alice" :p "tag" :o "x"})
               (arr/assert-quad {:s "alice" :p "tag" :o "x"})
               (arr/assert-quad {:s "alice" :p "tag" :o "y"}))]
    (is (= #{["alice" 2]}
           (dl/q db {:find '[?s (count-distinct ?v)] :where '[[?s "tag" ?v]]} everything)))))

(deftest sum-avg-min-max-aggregates
  (let [db (-> (arr/empty-db)
               (arr/assert-quad {:s "alice" :p "score" :o 10})
               (arr/assert-quad {:s "alice" :p "score" :o 20})
               (arr/assert-quad {:s "bob" :p "score" :o 30}))]
    (is (= #{["alice" 30 15.0 10 20] ["bob" 30 30.0 30 30]}
           (dl/q db {:find '[?s (sum ?v) (avg ?v) (min ?v) (max ?v)]
                     :where '[[?s "score" ?v]]}
                 everything)))))

(deftest ungrouped-aggregate-over-zero-matches-is-one-row-not-empty
  (let [db (fixture-db)]
    (is (= #{[0]}
           (dl/q db {:find '[(count ?s)] :where '[[?s "role" "nonexistent"]]} everything))
        "Datomic shape: an all-aggregate :find with zero matches is one row of zeros/nils, not an empty set")))

(deftest min-max-of-empty-group-is-nil-not-a-thrown-error
  (let [db (fixture-db)]
    (is (= #{[nil nil]}
           (dl/q db {:find '[(min ?v) (max ?v)] :where '[[?s "score" ?v]]} everything)))))

(deftest aggregate-honors-visible-too
  (let [db (fixture-db)
        no-bob (fn [{:keys [s]}] (not= "bob" s))]
    (is (= #{[2]}
           (dl/q db {:find '[(count ?s)] :where '[[?s "name" _]]} no-bob)))))

;; ── recursive rules (ADR-2607061200 Stage 3/4) ──────────────────────────────

(defn- chain-db []
  (-> (arr/empty-db)
      (arr/assert-quad {:s "alice" :p "parent" :o "bob"})
      (arr/assert-quad {:s "bob" :p "parent" :o "carol"})
      (arr/assert-quad {:s "carol" :p "parent" :o "dave"})))

(def ^:private ancestor-rules
  '[[(ancestor ?x ?y) [?x "parent" ?y]]
    [(ancestor ?x ?y) [?x "parent" ?z] (ancestor ?z ?y)]])

(deftest transitive-closure-via-recursive-rule
  (let [db (chain-db)]
    (is (= #{["alice" "bob"] ["alice" "carol"] ["alice" "dave"]
             ["bob" "carol"] ["bob" "dave"]
             ["carol" "dave"]}
           (dl/q db {:find '[?x ?y] :where '[(ancestor ?x ?y)] :rules ancestor-rules} everything)))))

(deftest rule-invocation-can-bind-args-in-either-direction
  (let [db (chain-db)]
    (testing "first arg bound (find descendants), second arg bound (find ancestors)"
      (is (= #{["bob"] ["carol"] ["dave"]}
             (dl/q db {:find '[?y] :where '[(ancestor "alice" ?y)] :rules ancestor-rules} everything)))
      (is (= #{["alice"] ["bob"] ["carol"]}
             (dl/q db {:find '[?x] :where '[(ancestor ?x "dave")] :rules ancestor-rules} everything))))))

(deftest rule-without-recursion-behaves-like-a-named-join
  (let [db (chain-db)]
    (is (= #{["bob"]}
           (dl/q db {:find '[?y]
                     :where '[(parent-of "alice" ?y)]
                     :rules '[[(parent-of ?x ?y) [?x "parent" ?y]]]}
                 everything)))))

(deftest mutual-recursion-across-two-rules
  (let [db (-> (arr/empty-db)
               (arr/assert-quad {:s "a" :p "red" :o "b"})
               (arr/assert-quad {:s "b" :p "blue" :o "c"})
               (arr/assert-quad {:s "c" :p "red" :o "d"})
               (arr/assert-quad {:s "d" :p "blue" :o "e"}))
        rules '[[(reach-red ?x ?y) [?x "red" ?y]]
                [(reach-red ?x ?y) [?x "red" ?z] (reach-blue ?z ?y)]
                [(reach-blue ?x ?y) [?x "blue" ?y]]
                [(reach-blue ?x ?y) [?x "blue" ?z] (reach-red ?z ?y)]]]
    (is (= #{["b"] ["c"] ["d"] ["e"]}
           (dl/q db {:find '[?y] :where '[(reach-red "a" ?y)] :rules rules} everything)))))

(deftest recursive-rule-respects-visible-through-the-fixpoint
  (let [db (chain-db)
        hide-bob-carol (fn [{:keys [s p o]}] (not (and (= s "bob") (= p "parent") (= o "carol"))))]
    (testing "without redaction alice reaches carol/dave too; with bob->carol hidden, the fixpoint can't derive past bob"
      (is (= #{["bob"] ["carol"] ["dave"]}
             (dl/q db {:find '[?y] :where '[(ancestor "alice" ?y)] :rules ancestor-rules} everything)))
      (is (= #{["bob"]}
             (dl/q db {:find '[?y] :where '[(ancestor "alice" ?y)] :rules ancestor-rules} hide-bob-carol))
          "the hidden edge is invisible to every rule-body clause too, not just the top-level :where"))))

(deftest unknown-rule-invocation-throws
  (let [db (chain-db)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                           #"unknown rule"
                           (dl/q db {:find '[?y] :where '[(nope "alice" ?y)]} everything)))))

(deftest rule-invoked-with-wrong-arity-throws
  (let [db (chain-db)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                           #"wrong number of arguments"
                           (dl/q db {:find '[?y]
                                     :where '[(anc "alice" ?y "extra")]
                                     :rules '[[(anc ?x ?y) [?x "parent" ?y]]]}
                                 everything)))))

(deftest rule-definitions-with-mismatched-arity-throws
  (let [db (chain-db)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                           #"same arity"
                           (dl/q db {:find '[?x ?y]
                                     :where '[(bad ?x ?y)]
                                     :rules '[[(bad ?x ?y) [?x "parent" ?y]]
                                              [(bad ?x) [?x "parent" _]]]}
                                 everything)))))

(deftest negating-a-rule-invocation-throws
  (let [db (chain-db)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                           #"negation of a rule invocation is not supported"
                           (dl/q db {:find '[?y]
                                     :where '[[?y "parent" _] (not (ancestor "alice" ?y))]
                                     :rules ancestor-rules}
                                 everything)))))

(deftest unsafe-negation-inside-a-rule-body-throws
  (let [db (chain-db)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                           #"unsafe negation"
                           (dl/q db {:find '[?x ?y]
                                     :where '[(risky ?x ?y)]
                                     :rules '[[(risky ?x ?y) (not [?x "parent" ?z])]]}
                                 everything)))))
