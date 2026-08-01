(ns arrangement.source-test
  "Both sources must answer identically, and the shared conformance suite is
  what says so. JVM-only for the same reason the commit/restore tests are:
  the crypto fixtures are synchronous only on clj."
  (:require [clojure.test :refer [deftest is testing]]
            [datom.source :as ds]
            [datom.source.conformance :as conf]
            [arrangement.core :as arr]
            [arrangement.source :as as]
            [arrangement.core-test :refer [test-blind-fn test-encrypt-fn test-decrypt-fn]]))

(defn- mem-store []
  (let [store (atom {}) reads (atom 0)]
    {:put! (fn [cid bytes] (swap! store assoc cid bytes))
     :get-fn (fn [cid] (swap! reads inc) (get @store cid))
     :reads reads}))

(defn- commit-quads! [put! quads]
  (arr/commit! put! (reduce arr/assert-quad (arr/empty-db) quads)
               nil arr/current-schema-version test-blind-fn test-encrypt-fn))

#?(:clj
   (deftest materialized-source-conforms
     (let [mk (fn [quads] (as/materialized (reduce arr/assert-quad (arr/empty-db) quads)))
           f (conf/check mk)]
       (is (empty? f) (conf/report f)))))

#?(:clj
   (deftest cursor-source-conforms
     (let [mk (fn [quads]
                (let [{:keys [put! get-fn]} (mem-store)]
                  (as/cursor get-fn (commit-quads! put! quads)
                             test-blind-fn test-decrypt-fn)))
           f (conf/check mk)]
       (is (empty? f) (conf/report f)))))

#?(:clj
   (deftest cursor-and-materialized-agree-quad-for-quad
     (let [{:keys [put! get-fn]} (mem-store)
           quads conf/corpus
           m (as/materialized (reduce arr/assert-quad (arr/empty-db) quads))
           c (as/cursor get-fn (commit-quads! put! quads) test-blind-fn test-decrypt-fn)]
       (doseq [[label pattern] conf/cases]
         (is (= (ds/scan-set m pattern) (ds/scan-set c pattern)) (str "case " label))))))

#?(:clj
   (deftest a-cursor-scan-reads-far-fewer-blocks-than-a-full-hydrate
     ;; the whole reason the seam exists
     (let [{:keys [put! get-fn reads]} (mem-store)
           quads (for [i (range 20000)]
                   {:s (str "s" i) :p (if (zero? (mod i 5000)) "rare" "common")
                    :o (str "v" i)})
           cid (commit-quads! put! quads)]
       (reset! reads 0)
       (let [hydrated (arr/restore get-fn cid test-decrypt-fn)
             hydrate-reads @reads]
         (reset! reads 0)
         (let [c (as/cursor get-fn cid test-blind-fn test-decrypt-fn)
               got (ds/scan-set c [nil "rare" nil])
               scan-reads @reads]
           (testing "the two agree"
             (is (= (ds/scan-set (as/materialized hydrated) [nil "rare" nil]) got))
             (is (= 4 (count got))))
           (testing "and the cursor touched far fewer blocks than the hydrate"
             (println (format "  [block reads] cursor %d vs full hydrate %d (%.1fx)"
                              scan-reads hydrate-reads
                              (double (/ hydrate-reads (max 1 scan-reads)))))
             (is (< (* 10 scan-reads) hydrate-reads)
                 (str "cursor " scan-reads " blocks vs hydrate " hydrate-reads))))))))

#?(:clj
   (deftest wrong-blind-key-returns-nothing-which-is-why-it-must-be-asserted
     (let [{:keys [put! get-fn]} (mem-store)
           cid (commit-quads! put! conf/corpus)
           wrong (fn [_] "not-the-real-token")
           c (as/cursor get-fn cid wrong test-decrypt-fn)]
       (testing "a mismatched blind key is indistinguishable from an empty db"
         (is (empty? (ds/scan-set c [nil "knows" nil])))))))
