(ns arrangement.datalog-limit-pushdown-test
  "ADR-2608021000 §6-6-1: a top-N query walks its ordering clause's distinct
  values and stops, with clauses INDEPENDENT of the driver evaluated once
  rather than once per value group -- the defect that got the first attempt
  reverted (arrangement 6a179a31).

  Every test asserts the driven answer equals the undriven one. Removing
  :limit is exactly what disqualifies the drive, so the query is its own
  control."
  (:require #?(:clj [clojure.test :refer [deftest testing is]]
               :cljs [cljs.test :refer-macros [deftest testing is]])
            [arrangement.core :as qs]
            [arrangement.datalog :as d]))

(def ^:private everything (constantly true))

(defn- db-of [quads]
  (reduce (fn [db [s p o]] (qs/assert-quad db {:s s :p p :o o})) (qs/empty-db) quads))

(defn- pad4
  "Zero-padded so string order is date order. Not `format`, which does not
  exist on cljs and this is a .cljc file."
  [x]
  (let [s (str x)] (str (subs "0000" 0 (max 0 (- 4 (count s)))) s)))

(defn- social [n]
  (db-of (concat
          (for [i (range n) delta [1 2]] [(str "p" i) "knows" (str "p" (mod (+ i delta) n))])
          (for [i (range n) m [0 1]] [(str "m" i "-" m) "creator" (str "p" i)])
          (for [i (range n) m [0 1]] [(str "m" i "-" m) "date" (pad4 (+ (* i 10) m))]))))

(def ^:private recent
  '{:find [?f ?msg ?date]
    :in [?person]
    :where [[?person "knows" ?f]
            [?msg "creator" ?f]
            [?msg "date" ?date]]})

(defn- driven [db q n person]
  (d/q db (assoc q :order-by '[[?date :desc]] :limit n) everything [person]))
(defn- undriven [db q person]
  (d/q db (assoc q :order-by '[[?date :desc]]) everything [person]))

(deftest driven-top-n-equals-the-undriven-answer
  (let [db (social 40)]
    (doseq [n [1 2 3 5 20]]
      (is (= (vec (take n (undriven db recent "p0"))) (driven db recent n "p0"))
          (str "limit " n)))))

(deftest a-limit-past-the-result-returns-everything
  (let [db (social 40)]
    (is (= (undriven db recent "p0") (driven db recent 999 "p0")))))

(deftest ascending-drives-the-other-way
  (let [db (social 40)
        r (d/q db (assoc recent :order-by '[[?date :asc]] :limit 3) everything ["p0"])
        all (d/q db (assoc recent :order-by '[[?date :asc]]) everything ["p0"])]
    (is (= (vec (take 3 all)) r))))

(deftest a-tie-group-larger-than-the-limit-is-resolved-by-the-secondary-key
  (let [db (db-of [["p0" "knows" "a"]
                   ["mc" "creator" "a"] ["mc" "date" "0500"]
                   ["mb" "creator" "a"] ["mb" "date" "0500"]
                   ["ma" "creator" "a"] ["ma" "date" "0500"]
                   ["mz" "creator" "a"] ["mz" "date" "0100"]])
        q '{:find [?msg ?date] :in [?person]
            :where [[?person "knows" ?f] [?msg "creator" ?f] [?msg "date" ?date]]}]
    (is (= [["ma" "0500"] ["mb" "0500"]]
           (d/q db (assoc q :order-by '[[?date :desc] [?msg :asc]] :limit 2) everything ["p0"])))))

(deftest the-hoisted-half-still-constrains-the-answer
  ;; The independent clause [?person knows ?f] is evaluated once and joined in.
  ;; If that join were dropped, every message in the database would qualify --
  ;; this asserts the count that only p0's two friends' messages produce.
  ;; Counts are derived from the fixture, not hand-computed -- I have now got a
  ;; hand-computed fixture count wrong twice in this file's history.
  (let [n 20
        db (social n)
        every-message (count (d/q db '{:find [?msg ?date] :where [[?msg "date" ?date]]}
                                  everything []))]
    (is (= (* 2 n) every-message) "n persons x 2 messages each")
    (is (= 4 (count (driven db recent 99 "p0")))
        "p0's two friends, two messages each -- NOT every-message, which is what
         a dropped join with the hoisted half would admit")
    (is (< 4 every-message) "the two numbers differ, so the assertion above bites")))

(deftest a-query-with-no-independent-clauses-still-works
  ;; Everything depends on the driver: nothing to hoist, base is the seed.
  (let [db (social 20)
        q '{:find [?msg ?date] :where [[?msg "date" ?date]]}
        r (d/q db (assoc q :order-by '[[?date :desc]] :limit 3) everything [])
        all (d/q db (assoc q :order-by '[[?date :desc]]) everything [])]
    (is (= (vec (take 3 all)) r))))

(deftest a-negation-query-falls-back-and-is-still-right
  (let [db (social 20)
        q '{:find [?f ?msg ?date] :in [?person]
            :where [[?person "knows" ?f] [?msg "creator" ?f] [?msg "date" ?date]
                    (not [?f "knows" ?person])]}]
    (is (= (vec (take 2 (undriven db q "p0"))) (driven db q 2 "p0")))))

(deftest visible?-applies-to-the-driver-clause-too
  (let [db (social 20)
        hide (fn [{:keys [p o]}] (not (and (= p "date") (> (compare o "0100") 0))))
        r (d/q db (assoc recent :order-by '[[?date :desc]] :limit 3) hide ["p0"])
        all (d/q db (assoc recent :order-by '[[?date :desc]]) hide ["p0"])]
    (is (= (vec (take 3 all)) r))))

(deftest a-key-bound-by-two-clauses-declines-to-drive
  (let [db (db-of [["p0" "knows" "a"] ["ma" "creator" "a"]
                   ["ma" "date" "0002"] ["ma" "other" "0002"]])
        q '{:find [?msg ?date] :in [?person]
            :where [[?person "knows" ?f] [?msg "creator" ?f]
                    [?msg "date" ?date] [?msg "other" ?date]]}]
    (is (= [["ma" "0002"]]
           (d/q db (assoc q :order-by '[[?date :desc]] :limit 5) everything ["p0"])))))

(deftest a-join-key-outside-find-still-constrains
  ;; The bug this exists for: the two halves join on ?msg, which appears in no
  ;; output column. Pruning the hoisted half down to :find erased it, leaving a
  ;; single empty binding that matched everything -- so replies to OTHER
  ;; people's messages came back. Every earlier fixture here happened to name
  ;; its join keys in :find, so the unit tests all passed and the LDBC
  ;; answers-agree gate is what caught it.
  (let [db (db-of [["m1" "hasCreator" "p0"]
                   ["r1" "replyOf" "m1"] ["r1" "hasCreator" "a"] ["r1" "date" "0002"]
                   ["r2" "replyOf" "m1"] ["r2" "hasCreator" "b"] ["r2" "date" "0001"]
                   ;; a reply to somebody else's message, with the HIGHEST date,
                   ;; so a broken join surfaces it first rather than subtly
                   ["rx" "replyOf" "mOther"] ["rx" "hasCreator" "c"] ["rx" "date" "0009"]
                   ["mOther" "hasCreator" "pZ"]])
        q '{:find [?author ?reply ?date] :in [?person]
            :where [[?msg "hasCreator" ?person]
                    [?reply "replyOf" ?msg]
                    [?reply "hasCreator" ?author]
                    [?reply "date" ?date]]}
        driven-r (d/q db (assoc q :order-by '[[?date :desc]] :limit 20) everything ["p0"])]
    (is (= [["a" "r1" "0002"] ["b" "r2" "0001"]] driven-r))
    (is (= (d/q db (assoc q :order-by '[[?date :desc]]) everything ["p0"]) driven-r))))
