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
  (let [store (atom {}) reads (atom 0) bytes-read (atom 0)]
    {:put! (fn [cid bytes] (swap! store assoc cid bytes))
     :get-fn (fn [cid]
               (let [b (get @store cid)]
                 (swap! reads inc)
                 (swap! bytes-read + (if b (count b) 0))
                 b))
     :reads reads
     ;; Blocks alone are half the number. A store that answers in 11 blocks
     ;; instead of 90 has not said how much it moved, and on a plane whose
     ;; whole cost model is round trips AND transfer (superproject
     ;; ADR-2608160100), a block count without bytes is the same half-claim
     ;; `kotobase-storage-pack` reports both halves to avoid.
     :bytes bytes-read}))

#?(:clj
   (defn- cost
     "Blocks and bytes read while `f` runs, from zero. JVM-only, like every
     caller: the crypto fixtures are synchronous only on clj."
     [{:keys [reads bytes]} f]
     (reset! reads 0)
     (reset! bytes 0)
     (let [result (f)]
       {:blocks @reads :bytes @bytes :result result})))

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

#?(:clj
   (deftest cursor-and-materialized-agree-on-a-value-range
     (let [{:keys [put! get-fn]} (mem-store)
           quads (for [i (range 20)] {:s (str "p" i) :p "age" :o i})
           m (as/materialized (reduce arr/assert-quad (arr/empty-db) quads))
           c (as/cursor get-fn (commit-quads! put! quads)
                        test-blind-fn test-decrypt-fn)
           want (ds/scan-range m "age" 10 15)]
       (is (= want (ds/scan-range c "age" 10 15)))
       (is (= 5 (count want)) "[10, 15) is five ages")
       (is (every? #(and (>= (:o %) 10) (< (:o %) 15)) want)))))

;; ── what a value range actually costs on the persisted path ─────────────────
;;
;; P4-4 of superproject ADR-2608170400 asks for the difference from a full
;; hydrate, measured in visited nodes AND bytes. The answer has two halves and
;; they point in opposite directions, so reporting either alone would mislead.

#?(:clj
   (defn- vkey
     "Zero-padded so string order is numeric order. Written without `format`,
     which is JVM-only -- this is a .cljc file and clj-kondo is right to
     refuse it outside a reader conditional."
     [i]
     (let [s (str i)]
       (str "v" (apply str (repeat (- 6 (count s)) "0")) s))))

#?(:clj
   (deftest the-attribute-cut-is-real-and-the-value-cut-is-not
     ;; 1,000 `score` quads among 21,000, so that "scan the attribute" is not
     ;; the same thing as "scan everything" -- with a single-attribute corpus
     ;; the two effects below cannot be told apart, and the first draft of
     ;; this measurement used one and could not.
     (let [{:keys [put! get-fn] :as store} (mem-store)
           quads (concat (for [i (range 1000)]
                           {:s (str "s" i) :p "score" :o (vkey i)})
                         (for [i (range 20000)]
                           {:s (str "t" i) :p "noise" :o (str "n" i)}))
           cid (commit-quads! put! quads)
           hydrate (cost store #(arr/restore get-fn cid test-decrypt-fn))
           narrow (cost store #(ds/scan-range
                                (as/cursor get-fn cid test-blind-fn test-decrypt-fn)
                                "score" (vkey 100) (vkey 110)))
           whole (cost store #(ds/scan-range
                               (as/cursor get-fn cid test-blind-fn test-decrypt-fn)
                               "score" nil nil))]
       (println (format "  [P4-4] hydrate %d blocks/%d bytes | range(10) %d/%d | range(1000) %d/%d"
                        (:blocks hydrate) (:bytes hydrate)
                        (:blocks narrow) (:bytes narrow)
                        (:blocks whole) (:bytes whole)))
       (testing "the ATTRIBUTE cut is real, in both currencies"
         (is (= 10 (count (:result narrow))))
         (is (< (* 5 (:blocks narrow)) (:blocks hydrate))
             (str "blocks: " (:blocks narrow) " vs hydrate " (:blocks hydrate)))
         (is (< (* 5 (:bytes narrow)) (:bytes hydrate))
             (str "bytes: " (:bytes narrow) " vs hydrate " (:bytes hydrate))))
       (testing "the VALUE cut is nothing: ten results cost what a thousand cost"
         ;; Not an accident and not a bug -- blinded leaf keys are HMAC, so
         ;; they are not order-preserving and an interval cannot be pruned on
         ;; the key. `CursorSource/-scan-range` says so; this measures it.
         ;;
         ;; THIS IS MEANT AS A TRIPWIRE: if it ever fails because `narrow`
         ;; got cheaper, the store has gained order-preserving range pruning
         ;; and P4-5 of ADR-2608170400 -- separate equality and range indexes
         ;; with a stated leakage budget -- has been answered, and the ADR
         ;; should be updated rather than the assertion.
         ;;
         ;; What is actually DEMONSTRATED is narrower than that, and the
         ;; difference is worth stating because it is the kind of claim this
         ;; ADR keeps catching. Mutation shows the assertion fails whenever
         ;; narrow and whole diverge -- but the mutation that diverged them
         ;; also broke correctness, so what is proven is sensitivity to
         ;; divergence, not to improvement. A genuine improvement keeps every
         ;; returned quad identical and only lowers the cost, and simulating
         ;; THAT requires the very pruning that does not exist: an attempt
         ;; using a memoizing get-fn changed nothing (11 blocks / 248,177
         ;; bytes either way), which incidentally measures something real --
         ;; within one scan the cursor never reads a block twice.
         (is (= (:blocks narrow) (:blocks whole)))
         (is (= (:bytes narrow) (:bytes whole)))
         (is (= 1000 (count (:result whole)))
             "and the unbounded range really did return a hundred times more")))))

#?(:clj
   (deftest when-the-attribute-is-the-corpus-the-cut-costs-more-than-hydrating
     ;; The degenerate case, pinned because it is the one a summary would drop.
     ;; With every quad sharing one attribute there is nothing to cut, and the
     ;; cursor pays MORE than restoring the whole database -- it walks the pos
     ;; tree and decrypts every leaf, where `restore` reads a hydrate path.
     ;; "The cursor is cheaper than a hydrate" is true of the shape above and
     ;; false here, and a claim that does not say which shape it means is not
     ;; a claim.
     (let [{:keys [put! get-fn] :as store} (mem-store)
           quads (for [i (range 20000)] {:s (str "s" i) :p "score" :o (vkey i)})
           cid (commit-quads! put! quads)
           hydrate (cost store #(arr/restore get-fn cid test-decrypt-fn))
           narrow (cost store #(ds/scan-range
                                (as/cursor get-fn cid test-blind-fn test-decrypt-fn)
                                "score" (vkey 1000) (vkey 1010)))]
       (println (format "  [P4-4] single-attribute corpus: hydrate %d blocks/%d bytes | range(10) %d/%d"
                        (:blocks hydrate) (:bytes hydrate)
                        (:blocks narrow) (:bytes narrow)))
       (is (= 10 (count (:result narrow))))
       (is (>= (:blocks narrow) (:blocks hydrate))
           (str "range " (:blocks narrow) " vs hydrate " (:blocks hydrate)))
       (is (>= (:bytes narrow) (:bytes hydrate))))))

