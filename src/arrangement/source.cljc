(ns arrangement.source
  "`arrangement`'s two `datom.source/IPatternSource` implementations.

  Both answer the same questions; they differ only in what they read to do it,
  which is the entire point of having a seam between them.

  - `materialized` wraps an in-memory db — today's behaviour, unchanged. Cost
    is O(1) per scan but you must have paid O(database) to build the db.
  - `cursor` reads the persisted index trees directly with `prolly-tree`'s
    key-range-pruned `scan-prefix`, so a scan descends O(path) blocks and
    returns O(result) rows. Nothing is materialized.

  The cursor implementation is possible because of a property the index format
  already had and nobody had used: a leaf key is
  `(pr-str [(blind-fn (blind-input a)) ... b ... o])` — each component blinded
  INDEPENDENTLY, then concatenated. A reader holding the blind key can
  therefore compute the prefix for any bound leading component without
  decrypting anything, and `scan-prefix` prunes to it. The four indices exist
  precisely so that every pattern shape has some index where its bound
  positions ARE the leading ones.

  Which index answers which pattern:

      pattern        index   prefix components
      [s p o]        spo     3   (exact)
      [s p _]        spo     2
      [s _ _]        spo     1
      [s _ o]        spo     1   + filter on o
      [_ p o]        pos     2
      [_ p _]        pso     1
      [_ _ o]        ocp     1
      [_ _ _]        spo     0   (full scan — unavoidable, it asked for all)

  Each index stores its value as the triple in ITS OWN component order
  (`pos` leaves hold `[p o s]`), so decoding permutes back. Getting that wrong
  is silent — the row count is right and the fields are transposed — which is
  why the conformance suite has cases where s, p and o are drawn from
  overlapping value sets."
  (:require [clojure.string :as str]
            [datom.source :as ds]
            [arrangement.core :as arr]
            [arrangement.query :as q]
            [prolly-tree.core :as pt]
            [ipld.core :as ipld]
            [ipld.value :as v]))

;; ── materialized: today's path, behind the seam ──────────────────────

(defrecord ^:no-doc MaterializedSource [db]
  ds/IPatternSource
  (-scan [_ pattern] (q/query db pattern (constantly true))))

(defn materialized
  "A source over an already-hydrated db. Wrapping `arrangement.query/query`
  rather than reimplementing it keeps this honest as a baseline: if the two
  paths disagree, it is the cursor that is wrong."
  [db]
  (->MaterializedSource db))

;; ── cursor: prefix scans over the persisted trees ────────────────────

(def ^:private index-order
  "Component order of each index, both for its key and for its value."
  {"spo" [:s :p :o] "pso" [:p :s :o] "pos" [:p :o :s] "ocp" [:o :p :s]})

(defn- plan
  "Pick the index and the leading bound components for `pattern`.
  Returns `[index-name bound-values]`; a position not covered by the prefix is
  handled by the post-filter in `-scan`."
  [[s p o]]
  (cond
    (and s p o) ["spo" [s p o]]
    (and s p)   ["spo" [s p]]
    (and p o)   ["pos" [p o]]
    s           ["spo" [s]]          ; [s _ o] lands here too; o post-filtered
    p           ["pso" [p]]
    ;; `[_ _ o]` deliberately has NO prefix. `ocp` is keyed by object, but
    ;; `assert-quad` only populates it when `ref?` says the object is a Link,
    ;; so for ordinary values it is empty and a prefix scan there would return
    ;; nothing at all -- silently, and indistinguishably from no matches.
    ;; A full scan with a post-filter is slower and right. (Datomic's AVET has
    ;; the same shape: it is [a v e], so value-only lookup is not indexed
    ;; there either.) Wiring `ocp` for ref-valued objects is a follow-up.
    :else       ["spo" []]))

(defn key-prefix
  "The leaf-key prefix for `values` blinded in order.

  A leaf key is `(pr-str [b1 b2 b3])`, i.e. `[\"b1\" \"b2\" \"b3\"]`. The prefix
  for a known leading b1 is `[\"b1\" ` — WITH the trailing space, so that a
  blinded token which is a strict prefix of another cannot match it. Dropping
  that space is the classic prefix-scan bug and it only shows up on data you
  do not have in a small test."
  [blind-fn values]
  (if (empty? values)
    ""
    (let [toks (mapv #(pr-str (blind-fn (arr/blind-input %))) values)]
      (str "[" (str/join " " toks)
           (when (< (count values) 3) " ")))))

(defn- leaf->quad [index-name triple]
  (zipmap (index-order index-name) triple))

(defrecord ^:no-doc CursorSource [get-fn roots blind-fn decrypt-fn]
  ds/IPatternSource
  (-scan [_ pattern]
    (let [[idx values] (plan pattern)
          root (get roots idx)]
      (if (nil? root)
        #{}
        (into #{}
              (comp (map (fn [[_ ciphertext]]
                           (leaf->quad idx (v/decode-value (decrypt-fn ciphertext)))))
                    ;; the prefix constrains only the LEADING components; a
                    ;; pattern like [s _ o] still has to check the rest.
                    (filter (fn [{:keys [s p o]}]
                              (let [[ps pp po] pattern]
                                (and (or (nil? ps) (= ps s))
                                     (or (nil? pp) (= pp p))
                                     (or (nil? po) (= po o)))))))
              (pt/scan-prefix get-fn root (key-prefix blind-fn values)))))))

(defn snapshot-roots
  "The four index root CIDs of a `arrangement.core/commit!` snapshot."
  [get-fn snapshot-cid]
  (when snapshot-cid
    (let [node (ipld/decode (get-fn snapshot-cid))]
      (into {} (keep (fn [k] (when-let [l (get-in node ["index-roots" k])]
                               [k (ipld/link-cid l)])))
            ["spo" "pso" "pos" "ocp"]))))

(defn cursor
  "A source that reads a persisted snapshot directly — no materialization.

  `blind-fn` must be the SAME keyed function the snapshot was committed with;
  a different key derives different prefixes and every scan silently returns
  nothing. That failure is indistinguishable from an empty database, so it is
  worth asserting at the call site rather than discovering in a dashboard.

  JVM-only for now: `decrypt-fn` is Promise-returning on cljs and the scan
  would have to be async all the way out, which changes the protocol's shape.
  Deliberately not faked with a synchronous stub."
  [get-fn snapshot-cid blind-fn decrypt-fn]
  (->CursorSource get-fn (or (snapshot-roots get-fn snapshot-cid) {}) blind-fn decrypt-fn))
