(ns arrangement.commit-delta-test
  "A delta commit must be indistinguishable from a full one.

  The value of a content-addressed snapshot is that the same content has the
  same name. A delta path that produced a different CID for the same graph
  would break every equality above it — CAS, dedup, replication — and it would
  do so silently, because both trees answer reads correctly. So the assertions
  here compare CIDs against `commit!`, not query results."
  (:require [clojure.test :refer [deftest is testing]]
            [arrangement.core :as a]))

(defn- store []
  (let [blocks (atom {})]
    {:put! (fn [cid bytes] (swap! blocks assoc cid bytes) cid)
     :get-fn (fn [cid] (get @blocks cid))
     :blocks blocks}))

;; Deterministic stand-ins: the property under test is structural, and a real
;; MAC/AEAD would only make failures harder to read.
(def ^:private blind-fn pr-str)
(def ^:private encrypt-fn identity)

(defn- quad [n]
  {:s (str "s" n) :p (str "p" (mod n 7)) :o (str "o" n)})

(defn- db-of [quads]
  (reduce (fn [db q] (a/assert-quad db q)) (a/empty-db) quads))

(defn- full-commit [quads prev]
  (let [{:keys [put!]} (store)]
    (a/commit! put! (db-of quads) prev a/current-schema-version
               blind-fn encrypt-fn)))

(deftest delta-from-nothing-matches-a-full-commit
  (testing "a first snapshot built by delta is the same snapshot"
    (doseq [n [1 5 200 900]]
      (let [quads (mapv quad (range n))
            {:keys [put! get-fn]} (store)]
        (is (= (full-commit quads nil)
               (a/commit-delta! put! get-fn nil quads a/current-schema-version
                                blind-fn encrypt-fn))
            (str "n=" n))))))

(deftest delta-on-top-matches-a-full-commit-of-the-whole
  (testing "extending a snapshot lands where rebuilding the union lands"
    (doseq [[base-n add-n] [[10 1] [200 20] [800 150]]]
      (let [base (mapv quad (range base-n))
            additions (mapv quad (range base-n (+ base-n add-n)))
            {:keys [put! get-fn]} (store)
            base-cid (a/commit! put! (db-of base) nil a/current-schema-version
                                blind-fn encrypt-fn)]
        (is (= (full-commit (concat base additions) base-cid)
               (a/commit-delta! put! get-fn base-cid additions
                                a/current-schema-version blind-fn encrypt-fn))
            (str "base=" base-n " add=" add-n))))))

(deftest delta-in-steps-matches-one-delta-of-the-same-quads
  (testing "the snapshot depends on content, not on how many calls produced it"
    (let [base (mapv quad (range 100))
          a1 (mapv quad (range 100 130))
          a2 (mapv quad (range 130 160))
          step (let [{:keys [put! get-fn]} (store)
                     c0 (a/commit! put! (db-of base) nil a/current-schema-version
                                   blind-fn encrypt-fn)
                     c1 (a/commit-delta! put! get-fn c0 a1
                                         a/current-schema-version blind-fn encrypt-fn)]
                 (a/commit-delta! put! get-fn c1 a2
                                  a/current-schema-version blind-fn encrypt-fn))
          expected (let [{:keys [put!]} (store)]
                     (a/commit! put! (db-of (concat base a1 a2))
                                ;; same `prev` the stepwise path ends with
                                (let [{:keys [put! get-fn]} (store)
                                      c0 (a/commit! put! (db-of base) nil
                                                    a/current-schema-version
                                                    blind-fn encrypt-fn)]
                                  (a/commit-delta! put! get-fn c0 a1
                                                   a/current-schema-version
                                                   blind-fn encrypt-fn))
                                a/current-schema-version blind-fn encrypt-fn))]
      (is (= expected step)))))

(deftest delta-round-trips-through-restore
  (testing "the delta snapshot is readable, not merely equal"
    (let [quads (mapv quad (range 300))
          {:keys [put! get-fn]} (store)
          cid (a/commit-delta! put! get-fn nil quads a/current-schema-version
                               blind-fn encrypt-fn)
          restored (a/restore get-fn cid identity)]
      (is (= (:spo (db-of quads)) (:spo restored)))
      (is (= (:pos (db-of quads)) (:pos restored))))))

(deftest delta-writes-far-fewer-blocks-than-a-full-commit
  (testing "the reason this exists"
    (let [base (mapv quad (range 2000))
          additions (mapv quad (range 2000 2020))
          {:keys [put! get-fn blocks]} (store)
          base-cid (a/commit! put! (db-of base) nil a/current-schema-version
                              blind-fn encrypt-fn)
          before (count @blocks)
          _ (a/commit-delta! put! get-fn base-cid additions
                             a/current-schema-version blind-fn encrypt-fn)
          delta-blocks (- (count @blocks) before)
          full-blocks (let [{:keys [put! blocks]} (store)]
                        (a/commit! put! (db-of (concat base additions)) base-cid
                                   a/current-schema-version blind-fn encrypt-fn)
                        (count @blocks))]
      (is (< delta-blocks (/ full-blocks 2))
          (str "delta wrote " delta-blocks " blocks, a full commit wrote "
               full-blocks)))))
