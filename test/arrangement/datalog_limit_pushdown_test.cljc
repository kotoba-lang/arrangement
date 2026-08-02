(ns arrangement.datalog-limit-pushdown-test
  "ADR-2608021000 §6-5 B-2: a top-N query walks its ordering clause's distinct
  values in order and stops, instead of joining everything and sorting.

  Every test asserts the driven answer equals the undriven one. The ordered
  drive is a strategy; it is not allowed to be a different query. The way to
  make it undriven is to remove :limit -- that is exactly the condition
  `ordered-driver` keys on."
  (:require #?(:clj [clojure.test :refer [deftest testing is]]
               :cljs [cljs.test :refer-macros [deftest testing is]])
            [arrangement.core :as qs]
            [arrangement.datalog :as d]))

(def ^:private everything (constantly true))

(defn- db-of [quads]
  (reduce (fn [db [s p o]] (qs/assert-quad db {:s s :p p :o o})) (qs/empty-db) quads))

(defn- social [n]
  (db-of (concat
          (for [i (range n) delta [1 2]] [(str "p" i) "knows" (str "p" (mod (+ i delta) n))])
          (for [i (range n) m [0 1]] [(str "m" i "-" m) "creator" (str "p" i)])
          ;; zero-padded so string order is date order
          (for [i (range n) m [0 1]] [(str "m" i "-" m) "date" (format "%04d" (+ (* i 10) m))]))))

(def ^:private recent
  '{:find [?f ?msg ?date]
    :in [?person]
    :where [[?person "knows" ?f]
            [?msg "creator" ?f]
            [?msg "date" ?date]]})

(defn- top-n [db q n person]
  (d/q db (assoc q :order-by '[[?date :desc]] :limit n) everything [person]))

(defn- all-sorted [db q person]
  (d/q db (assoc q :order-by '[[?date :desc]]) everything [person]))

(deftest driven-top-n-equals-the-undriven-answer
  (let [db (social 40)]
    (doseq [n [1 2 3 4 20]]
      (is (= (vec (take n (all-sorted db recent "p0"))) (top-n db recent n "p0"))
          (str "limit " n)))))

(deftest a-limit-larger-than-the-result-returns-everything
  (let [db (social 40)]
    (is (= (all-sorted db recent "p0") (top-n db recent 999 "p0")))))

(deftest ascending-order-drives-the-other-way
  (let [db (social 40)
        asc (d/q db (assoc recent :order-by '[[?date :asc]] :limit 3) everything ["p0"])
        all-asc (d/q db (assoc recent :order-by '[[?date :asc]]) everything ["p0"])]
    (is (= (vec (take 3 all-asc)) asc))))

(deftest ties-are-drained-whole-so-a-secondary-key-is-complete
  ;; Three messages share a date; a top-2 must still choose between them by the
  ;; secondary key, which requires the whole tie group to have been produced.
  (let [db (db-of [["p0" "knows" "a"]
                   ["mc" "creator" "a"] ["mc" "date" "0500"]
                   ["mb" "creator" "a"] ["mb" "date" "0500"]
                   ["ma" "creator" "a"] ["ma" "date" "0500"]
                   ["mz" "creator" "a"] ["mz" "date" "0100"]])
        q '{:find [?msg ?date] :in [?person]
            :where [[?person "knows" ?f] [?msg "creator" ?f] [?msg "date" ?date]]}
        r (d/q db (assoc q :order-by '[[?date :desc] [?msg :asc]] :limit 2) everything ["p0"])]
    (is (= [["ma" "0500"] ["mb" "0500"]] r))))

(deftest a-query-the-driver-cannot-handle-falls-back-and-is-still-right
  ;; A negation clause disqualifies the ordered drive; the answer must be the
  ;; ordinary path's, not an error and not a truncation.
  (let [db (social 20)
        q '{:find [?f ?msg ?date] :in [?person]
            :where [[?person "knows" ?f]
                    [?msg "creator" ?f]
                    [?msg "date" ?date]
                    (not [?f "knows" ?person])]}
        driven (d/q db (assoc q :order-by '[[?date :desc]] :limit 2) everything ["p0"])
        undriven (d/q db (assoc q :order-by '[[?date :desc]]) everything ["p0"])]
    (is (= (vec (take 2 undriven)) driven))))

(deftest visible?-is-applied-to-the-driver-clause-too
  ;; The seed comes from the driver clause; if it bypassed visible? a top-N
  ;; could surface a row the same query without :limit would not return.
  (let [db (social 20)
        hide-high (fn [{:keys [p o]}] (not (and (= p "date") (> (compare o "0100") 0))))
        driven (d/q db (assoc recent :order-by '[[?date :desc]] :limit 3) hide-high ["p0"])
        undriven (d/q db (assoc recent :order-by '[[?date :desc]]) hide-high ["p0"])]
    (is (= (vec (take 3 undriven)) driven))))

(deftest ordering-on-a-variable-bound-by-two-clauses-is-not-driven
  ;; ?date appears twice, so no single value group fixes the sort key. The
  ;; guard must decline rather than pick one of them.
  (let [db (db-of [["p0" "knows" "a"] ["ma" "creator" "a"]
                   ["ma" "date" "0002"] ["ma" "other" "0002"]])
        q '{:find [?msg ?date] :in [?person]
            :where [[?person "knows" ?f] [?msg "creator" ?f]
                    [?msg "date" ?date] [?msg "other" ?date]]}]
    (is (= [["ma" "0002"]]
           (d/q db (assoc q :order-by '[[?date :desc]] :limit 5) everything ["p0"])))))
