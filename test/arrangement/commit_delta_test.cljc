(ns arrangement.commit-delta-test
  "A delta commit must be indistinguishable from a full one.

  The value of a content-addressed snapshot is that the same content has the
  same name. A delta path that produced a different CID for the same graph
  would break every equality above it — CAS, dedup, replication — and it would
  do so silently, because both trees answer reads correctly. So the assertions
  here compare CIDs against `commit!`, not query results.

  PLATFORM. `commit!`/`commit-delta!` return the CID directly on the JVM and a
  `js/Promise` of it on ClojureScript, and `blind-fn`/`encrypt-fn` carry the
  same split (see `arrangement.core`'s `index-root`). The bodies below were
  written against the synchronous contract only, so they are `#?(:clj)`; the
  ClojureScript coverage is the single async test at the bottom, which exists
  because the cljs path was broken outright and nothing here would have said
  so. Mirroring all five asynchronously is OWED — see that test's comment."
  (:require [clojure.test :refer [deftest is testing]]
            #?(:cljs [cljs.test :refer [async]])
            [arrangement.core :as a]))

(defn- store []
  (let [blocks (atom {})]
    {:put! (fn [cid bytes] (swap! blocks assoc cid bytes) cid)
     :get-fn (fn [cid] (get @blocks cid))
     :blocks blocks}))

;; Deterministic stand-ins: the property under test is structural, and a real
;; MAC/AEAD would only make failures harder to read. They still have to honour
;; the platform contract, though -- on cljs `index-root` `.then`s these, so a
;; plain value here fails with `.then is not a function` and says nothing about
;; the code under test.
(def ^:private blind-fn #?(:clj pr-str
                           :cljs (fn [x] (js/Promise.resolve (pr-str x)))))
(def ^:private encrypt-fn #?(:clj identity
                             :cljs (fn [x] (js/Promise.resolve x))))

(defn- quad [n]
  {:s (str "s" n) :p (str "p" (mod n 7)) :o (str "o" n)})

(defn- db-of [quads]
  (reduce (fn [db q] (a/assert-quad db q)) (a/empty-db) quads))

(defn- full-commit [quads prev]
  (let [{:keys [put!]} (store)]
    (a/commit! put! (db-of quads) prev a/current-schema-version
               blind-fn encrypt-fn)))

#?(:clj
   (deftest delta-from-nothing-matches-a-full-commit
     (testing "a first snapshot built by delta is the same snapshot"
       (doseq [n [1 5 200 900]]
         (let [quads (mapv quad (range n))
               {:keys [put! get-fn]} (store)]
           (is (= (full-commit quads nil)
                  (a/commit-delta! put! get-fn nil quads a/current-schema-version
                                   blind-fn encrypt-fn))
               (str "n=" n)))))))

#?(:clj
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
               (str "base=" base-n " add=" add-n)))))))

#?(:clj
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
         (is (= expected step))))))

#?(:clj
   (deftest delta-round-trips-through-restore
     (testing "the delta snapshot is readable, not merely equal"
       (let [quads (mapv quad (range 300))
             {:keys [put! get-fn]} (store)
             cid (a/commit-delta! put! get-fn nil quads a/current-schema-version
                                  blind-fn encrypt-fn)
             restored (a/restore get-fn cid identity)]
         (is (= (:spo (db-of quads)) (:spo restored)))
         (is (= (:pos (db-of quads)) (:pos restored)))))))

#?(:clj
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
                  full-blocks))))))

;; ── ClojureScript ───────────────────────────────────────────────────────────
;;
;; This test exists because `commit-delta!` had NEVER run on ClojureScript.
;; `index-root`'s cljs branch called `.then` on `pt/insert-many`, which is
;; synchronous on both hosts -- prolly-tree ships an async `scan-prefix` but no
;; async incremental write. So an empty index with no previous root returned
;; nil and threw `Cannot read properties of null (reading 'then')`, and a
;; non-empty one returned a CID string whose `.then` is not a function. The
;; whole file was `.cljc` and the repo's CI runs a real ClojureScript job, but
;; every assertion here was written synchronously, so cljs never reached them.
;;
;; Both shapes are covered deliberately: the empty first delta is the one that
;; produced the null, and the extend-on-top case is the one that produced the
;; string.
;;
;; OWED: async mirrors of the other four, including `restore` and the
;; block-count assertion. This proves the path completes and agrees with
;; `commit!`; it does not carry the full JVM coverage.
;;
;; NOT covered, and this is a real limit rather than an oversight: an
;; asynchronous store. `pt/insert-many` calls `put!` and ignores what it
;; returns, so a Promise-returning `put!` -- which is what a Worker-backed
;; store has -- is never awaited before the commit node that references those
;; blocks is published. `store` above is synchronous, so this test cannot see
;; that. Closing it needs an async write path in prolly-tree.
#?(:cljs
   (deftest cljs-delta-agrees-with-a-full-commit
     (testing "the ClojureScript path completes at all, and lands where commit! lands"
       (async done
         (let [quads (mapv quad (range 40))
               additions (mapv quad (range 40 55))
               {:keys [put! get-fn]} (store)]
           (-> (js/Promise.all
                #js [(full-commit quads nil)
                     (a/commit-delta! put! get-fn nil quads
                                      a/current-schema-version blind-fn encrypt-fn)])
               (.then (fn [^js pair]
                        ;; empty-index / nil-root shape: this is the call that
                        ;; used to throw on null
                        (is (= (aget pair 0) (aget pair 1))
                            "first delta == full commit")
                        (js/Promise.all
                         #js [(full-commit (concat quads additions) (aget pair 1))
                              (a/commit-delta! put! get-fn (aget pair 1) additions
                                               a/current-schema-version
                                               blind-fn encrypt-fn)])))
               (.then (fn [^js pair]
                        (is (= (aget pair 0) (aget pair 1))
                            "delta on top == full commit of the whole")
                        (done)))
               (.catch (fn [e]
                         (is false (str "cljs commit-delta! threw: " e))
                         (done)))))))))
