(ns arrangement.core
  "The in-memory, 4-covering-index Arrangement -- Datomic's own term for
  this exact structure (`spo`/`pso`/`pos`/`ocp` here, EAVT/AEVT/AVET/VAET
  in Datomic's vocabulary) -- plus CID-addressed commit snapshotting via
  `prolly-tree.core`. Repo formerly `quad-store` (renamed: it stores
  triples `{:s :p :o}`, not RDF quads -- `Arrangement` names the actual
  structure instead of overloading `quad`, and aligns this whole substrate
  with Datomic terminology per the design this org tracks kotoba : kotobase
  = Clojure : Datomic against, ADR-2607032500). `arrangement.query` (this
  same repo, formerly the standalone `kqe` repo) is the pattern-routing
  query layer over the indices below.

  A triple is `{:s subject :p predicate :o object}`. s/p/o are still
  treated as opaque values for indexing purposes (general typed-value
  support -- int/bytes/bool beyond string and `ipld.core/Link` -- remains a
  follow-up), but an `ipld.core/Link` value is now recognized and preserved
  end to end: through the hot db, through a commit snapshot's index-root
  (`index-root` below), and back out again on a cold read (see
  `kotoba-lang/kotobase-peer`'s `cold-datoms`/`hydrate-db`, which call
  `edn->link` on read).

  `:o` values that are references to other entities are additionally
  indexed in `ocp` for reverse-reference lookup when `ref?` (default:
  `ipld.core/link?`, ADR-2607023200 §6-4 -- \"ref? naturalizes to: is the
  value a Link\") says so; a caller can still pass a different predicate to
  `assert-quad`/`retract-quad` to opt out or widen it."
  (:require [prolly-tree.core :as pt]
            [ipld.core :as ipld]
            [ipld.value :as v]))

(defn empty-db [] {:spo {} :pso {} :pos {} :ocp {}})

(defn- upd [m k1 k2 v]
  (update m k1 (fnil (fn [m2] (update m2 k2 (fnil conj #{}) v)) {})))

(defn- rm [m k1 k2 v]
  (if-let [m2 (get m k1)]
    (let [s (disj (get m2 k2 #{}) v)]
      (if (empty? s)
        (let [m2' (dissoc m2 k2)]
          (if (empty? m2') (dissoc m k1) (assoc m k1 m2')))
        (assoc m k1 (assoc m2 k2 s))))
    m))

(defn assert-quad
  "Add `{:s :p :o}` to `db`'s 4 indices. `ref?` (default: `ipld.core/link?`)
  decides whether `:o` is also indexed in `:ocp` for reverse-reference
  lookup."
  ([db q] (assert-quad db q ipld/link?))
  ([db {:keys [s p o]} ref?]
   (cond-> db
     true     (update :spo upd s p o)
     true     (update :pso upd p s o)
     true     (update :pos upd p o s)
     (ref? o) (update :ocp upd o p s))))

(defn retract-quad
  "Remove `{:s :p :o}` from `db`'s 4 indices."
  ([db q] (retract-quad db q ipld/link?))
  ([db {:keys [s p o]} ref?]
   (cond-> db
     true     (update :spo rm s p o)
     true     (update :pso rm p s o)
     true     (update :pos rm p o s)
     (ref? o) (update :ocp rm o p s))))

(defn entity-attrs
  "All `{p #{o...}}` for subject `s` (EAVT-style)."
  [db s] (get (:spo db) s {}))

(defn by-predicate
  "All `{s #{o...}}` for predicate `p` (AEVT-style scan)."
  [db p] (get (:pso db) p {}))

(defn by-predicate-value
  "All subjects `s` where `[s p o]` holds (AVET-style point lookup)."
  [db p o] (get-in db [:pos p o] #{}))

(defn values-for-predicate
  "Distinct object values asserted for predicate `p`, in no particular order
  (`:pos` is a hash map). Exposed so a query can DRIVE an ordered scan from a
  clause's value position -- sorting these and walking them is bounded by the
  number of distinct values, where joining every row that carries them is
  bounded by the number of rows."
  [db p] (keys (get (:pos db) p {})))

(defn refs-to
  "All `{p #{s...}}` referencing object `o` (VAET-style reverse lookup) --
  only populated for quads asserted with a truthy `ref?`."
  [db o] (get (:ocp db) o {}))

;; ── Link <-> EDN-safe round-trip ─────────────────────────────────────────────
;; `ipld.core/Link` is a bare deftype with no reader/print-method (by design --
;; the codebase's `dag-cbor`/`ipld` layer round-trips Links via CBOR tag 42,
;; never via a JVM/cljs-specific reader macro). `index-root` below persists
;; keys through `pr-str`/`edn/read-string` (a prolly-tree leaf key, not a
;; dag-cbor block), so a raw Link would NOT survive that round-trip. Represent
;; it instead as a plain 2-vector `["ipld/link" cid]` -- ordinary, portable EDN
;; that needs no custom reader on either JVM or ClojureScript.
;; Still load-bearing on the KEY path (see `index-root`): a leaf key is built
;; with `pr-str`, and `pr-str` of a Link record is platform-dependent record
;; printing. It is NO LONGER used on the value path, which is `ipld.value`
;; (`kotoba.value.v1`) as of schema-version 2 — that codec carries a Link as a
;; real tag-42 value and needs no textual stand-in. `edn->link` remains the
;; read path for schema-version 1 snapshots.
(defn link->edn
  "A Link becomes `[\"ipld/link\" cid]`; anything else passes through."
  [v] (if (ipld/link? v) ["ipld/link" (ipld/link-cid v)] v))

(defn edn->link
  "Inverse of `link->edn`: reconstructs the Link, or passes through anything
  that isn't the `[\"ipld/link\" cid]` shape."
  [v] (if (and (vector? v) (= 2 (count v)) (= "ipld/link" (first v)))
        (ipld/link (second v))
        v))

(defn blind-input
  "What `blind-fn` sees for one s/p/o component.

  PUBLIC because deriving it is exactly how a cold reader seeks by prefix
  without materializing the db (`arrangement.source/cursor`, and
  `kotobase-peer`'s `cold-datoms` before it). Keeping it private forced every
  such reader to re-implement it, which is how two copies of a crypto input
  drift apart.

  Deliberately NOT the `kotoba.value.v1` bytes: `blind-fn` is a caller-supplied
  keyed MAC whose output a cold reader re-derives to seek by prefix
  (`kotobase-peer`'s `cold-datoms`), so changing its input is a cross-repo
  crypto change, not a local one. Typed round-tripping is the VALUE slot's job
  — which is exactly where a component's type was being lost before."
  [component]
  ;; An ALLOWLIST, because the failure mode is silent. `blind-fn` serializes
  ;; what it is handed — the reference implementation `pr-str`s it — and
  ;; `pr-str` is canonical for only some values:
  ;;
  ;;   set / map      iteration order is undefined -> two runtimes derive
  ;;                  different seek tokens for the same component
  ;;   byte array     prints as `#object[[B 0x… "[B@…"]`, an identity hash —
  ;;                  not stable across two arrays with the SAME bytes, or
  ;;                  even across runs
  ;;   record         platform-dependent record printing
  ;;
  ;; None of these were rejected before; they produced divergent keys quietly.
  ;; A Link is admitted by name (it is a `defrecord`, so `map?` is true for it)
  ;; and goes through `link->edn`, which exists for exactly this reason.
  ;;
  ;; This bounds the KEY path only. The VALUE slot is `kotoba.value.v1` and
  ;; accepts the codec's full admitted set.
  (when-not (or (nil? component)
                (boolean? component)
                (integer? component)
                (string? component)
                (keyword? component)
                (symbol? component)
                (ipld/link? component))
    (throw (ex-info "arrangement: component is not a blindable scalar"
                    {:problem :arrangement/component-not-blindable
                     :component-type (type component)})))
  (link->edn component))

;; ── index-root: JVM (sync) / cljs (async, ADR-2607051000 Worker addendum) ──
;; `blind-fn`/`encrypt-fn` carry a DIFFERENT contract per platform, by design:
;; JVM `javax.crypto` is synchronous (`(blind-fn x) -> string`, `(encrypt-fn
;; bytes) -> bytes`, called directly). The Worker's Web Crypto
;; (`crypto.subtle.sign`/`.encrypt`) is Promise-based — there is no
;; synchronous AEAD/HMAC primitive in that runtime — so the cljs contract is
;; `(blind-fn x) -> js/Promise<string>`, `(encrypt-fn bytes) -> js/Promise<
;; bytes>`, and `index-root`/`commit!` become Promise-returning too. This
;; does NOT touch `put!`/`get-fn` (still synchronous on both platforms,
;; unchanged from `prolly-tree.core`/`ipld.core`'s existing contract) — the
;; async boundary is isolated to the crypto step alone, resolved BEFORE the
;; (still-synchronous) tree is built. The JVM body below is byte-identical to
;; the one ADR-2607051000's implementation PR merged; only a cljs sibling is
;; new."
#?(:cljs
   (defn- pmap-async
     "cljs only: map `f` (returns a `js/Promise`) over `coll` concurrently,
     return one `js/Promise` of the resolved results, order-preserved --
     `js/Promise.all`, cljs-idiomatic (`vec`-in, `vec`-out)."
     [f coll]
     (-> (js/Promise.all (into-array (map f coll)))
         (.then (fn [arr] (vec arr))))))

(defn- index-root
  "Flatten one index map into sorted `[key val]` prolly-tree entries and
  build a tree from it (ADR-2607051000, ciphertext-over-CID persistence:
  accepted 2026-07-06, this fn implements its corrected key/value split —
  see ADR-2607061800's addendum for why the original ADR text was wrong
  about the value slot).

  `key` is `(pr-str [(blind-fn a) (blind-fn b) (blind-fn c)])` (each position
  passed through `blind-input` first, then `blind-fn` — a keyed, deterministic
  MAC, e.g. HMAC-SHA256 — so the leaf key is queryable by prefix for a caller
  who already knows the plaintext component, but is NOT the plaintext, and is
  NOT order-preserving/full ciphertext).

  `val` is `(encrypt-fn (ipld.value/encode-value [a b c]))` — an AEAD
  ciphertext blob of the REAL triple. This is the correction: the ORIGINAL
  triple lived only in the (now-blinded, one-way, unrecoverable) key, so once
  the key stopped being plaintext there was nowhere left to read the actual
  s/p/o payload back from — `val` now carries it, encrypted, so `cold-datoms`
  (in `kotoba-lang/kotobase-peer`) can decrypt a matched leaf's value to
  reconstruct the row instead of trying to invert the key.

  **schema-version 2** (ADR-kotoba-canonical-value-codec, VC3): the value slot
  encodes with `kotoba.value.v1` instead of `ipld/encode`. `ipld/encode` is a
  NODE codec — it writes a keyword as text and hands back a string, and has no
  defined order for a set — so a typed component did not survive the
  round-trip even though its CID verified. The value codec is what makes the
  s/p/o this repo's own `assert-quad` already accepts (ordinary map keys, any
  value) actually persistable. The KEY path is deliberately unchanged; see
  `blind-input`.

  `blind-fn`/`encrypt-fn` are REQUIRED (no default — matching this
  codebase's no-silent-default stance, ADR-2607050700, same as
  `schema-version` below): synchronous on JVM (`(blind-fn blind-input-
  component) -> string`, `(encrypt-fn bytes) -> bytes`); Promise-returning
  on cljs (see the platform-contract note above). Returns the root CID
  directly on JVM, a `js/Promise` of it on cljs."
  [put! m blind-fn encrypt-fn]
  #?(:clj
     (let [entries (sort-by first
                            (for [[a m2] m [b os] m2 o os]
                              [(pr-str (mapv #(blind-fn (blind-input %)) [a b o]))
                               (encrypt-fn (v/encode-value [a b o]))]))]
       (pt/build-tree put! entries))
     :cljs
     (let [triples (vec (for [[a m2] m [b os] m2 o os] [a b o]))]
       (-> (pmap-async
            (fn [triple]
              (-> (pmap-async blind-fn (mapv blind-input triple))
                  (.then (fn [blinded]
                           (-> (encrypt-fn (v/encode-value triple))
                               (.then (fn [ct] [(pr-str blinded) ct])))))))
            triples)
           (.then (fn [entries] (pt/build-tree put! (vec (sort-by first entries)))))))))

(def current-schema-version
  "The current `\"schema-version\"` value for this index shape
  (ADR-2607050500, \"Schema evolution\"). Not a hidden default -- `commit!`
  requires the caller to pass a version explicitly (see below); this is
  just the value to pass when you have no other one in mind. Bump this --
  and give callers a migration path keyed on the old value -- the day the
  4-index shape changes incompatibly.

  **2** (was 1): the leaf VALUE slot moved from `ipld/encode` (a node codec,
  which loses a keyword's type and has no defined order for a set) to
  `kotoba.value.v1` via `ipld.value` — ADR-kotoba-canonical-value-codec, VC3.
  The migration is read-compatible, not a rewrite: `restore` still reads a
  version-1 snapshot through the old codec (see `supported-schema-versions`).
  What a version-1 snapshot CANNOT do is retroactively recover a type it never
  persisted — a keyword written under version 1 comes back as the string it
  was stored as. New writes are version 2."
  2)

(def supported-schema-versions
  "Snapshot versions `restore` can read. Writing is always
  `current-schema-version`; reading accepts the older shape so an existing
  store keeps opening. Anything outside this set is rejected by name rather
  than interpreted under the current index shape."
  #{1 2})

(defn commit!
  "Snapshot `db`'s 4 indices into 4 prolly-trees via `put!`
  (`prolly-tree.core`-shaped port: `(put! cid bytes)`), CID-address the
  commit itself (dag-cbor of `{schema-version index-roots prev}`, where
  every root and `prev` is a REAL tag-42 IPLD link via `kotoba-lang/ipld`
  -- an empty index snapshots as null), and return the commit CID string.
  `prev` is the previous commit CID, or nil for the first commit.

  `schema-version` is REQUIRED (ADR-2607050500: schema evolution is a
  caller-declared choice, not a silently-assumed default) -- pass
  `current-schema-version` if you have no other version in mind, but state
  it. Content-addressed: committing the same `db` + `prev` + `schema-
  version` twice returns the same CID.

  `blind-fn`/`encrypt-fn` are REQUIRED (ADR-2607051000, accepted
  2026-07-06) and threaded unchanged to `index-root` for all 4 indices —
  see `index-root`'s docstring for their contract, including the
  synchronous-JVM/Promise-cljs platform split. Returns the commit CID
  directly on JVM, a `js/Promise` of it on cljs."
  [put! db prev schema-version blind-fn encrypt-fn]
  (let [->link #(some-> % ipld/link)]          ; empty index -> nil root -> null
    #?(:clj
       (let [roots {"spo" (->link (index-root put! (:spo db) blind-fn encrypt-fn))
                    "pso" (->link (index-root put! (:pso db) blind-fn encrypt-fn))
                    "pos" (->link (index-root put! (:pos db) blind-fn encrypt-fn))
                    "ocp" (->link (index-root put! (:ocp db) blind-fn encrypt-fn))}]
         (ipld/put-node! put! {"schema-version" schema-version
                               "index-roots" roots "prev" (->link prev)}))
       :cljs
       (-> (pmap-async (fn [k] (index-root put! (get db k) blind-fn encrypt-fn))
                       [:spo :pso :pos :ocp])
           (.then (fn [[spo pso pos ocp]]
                    (ipld/put-node! put! {"schema-version" schema-version
                                          "index-roots" {"spo" (->link spo) "pso" (->link pso)
                                                         "pos" (->link pos) "ocp" (->link ocp)}
                                          "prev" (->link prev)})))))))

(defn restore
  "Rebuild a complete in-memory arrangement from a snapshot produced by
  `commit!`. Reads only the persisted `spo` covering index and derives the
  other three indexes by re-asserting every recovered triple. `get-fn` is
  `(fn [cid] bytes)` and `decrypt-fn` is the inverse of the encrypt function
  supplied to `commit!` (synchronous on clj, Promise-returning on cljs).

  A nil snapshot returns an empty db. Unknown schema versions are rejected
  instead of being interpreted with the current index shape; a version this
  build still supports (`supported-schema-versions`) is decoded with the codec
  that WROTE it, never reinterpreted under the current one. Returns a db on
  clj and a Promise of a db on cljs."
  [get-fn snapshot-cid decrypt-fn]
  (if (nil? snapshot-cid)
    #?(:clj (empty-db) :cljs (js/Promise.resolve (empty-db)))
    (let [snapshot (ipld/decode (get-fn snapshot-cid))
          schema-version (get snapshot "schema-version")
          _ (when-not (contains? supported-schema-versions schema-version)
              (throw (ex-info "Unsupported arrangement snapshot schema"
                              {:problem :arrangement/unsupported-schema-version
                               :supported supported-schema-versions
                               :current current-schema-version
                               :actual schema-version
                               :snapshot-cid snapshot-cid})))
          ;; The codec is chosen by the version the snapshot RECORDS, so a
          ;; version-1 leaf keeps its original (type-lossy) reading instead of
          ;; being re-interpreted as kotoba.value.v1 bytes.
          decode-leaf (if (= 1 schema-version)
                        (fn [bytes] (mapv edn->link (ipld/decode bytes)))
                        v/decode-value)
          root-cid (some-> (get-in snapshot ["index-roots" "spo"]) ipld/link-cid)
          entries (if root-cid (pt/scan-prefix get-fn root-cid "") [])
          build (fn [triples]
                  (reduce (fn [db [s p o]] (assert-quad db {:s s :p p :o o}))
                          (empty-db)
                          triples))]
      #?(:clj
         (build (map (fn [[_ ciphertext]] (decode-leaf (decrypt-fn ciphertext)))
                     entries))
         :cljs
         (-> (js/Promise.all
              (into-array
               (map (fn [[_ ciphertext]]
                      (-> (decrypt-fn ciphertext) (.then decode-leaf)))
                    entries)))
             (.then (fn [triples] (build (vec triples)))))))))

;; ── Incremental commit ──────────────────────────────────────────────────────

(defn- index-triple
  "The triple `index` stores for quad `{s p o}`, or nil when that index skips
  it. Mirrors `assert-quad`'s four `upd` calls exactly; if those ever diverge,
  a delta commit stops matching a full one and the tests below say so."
  [index {:keys [s p o]} ref?]
  (case index
    :spo [s p o]
    :pso [p s o]
    :pos [p o s]
    :ocp (when (ref? o) [o p s])))

(def ^:private index-names
  [[:spo "spo"] [:pso "pso"] [:pos "pos"] [:ocp "ocp"]])

(defn- prev-root
  "Root CID of one index in a previously committed snapshot, or nil."
  [snapshot name]
  (some-> (get-in snapshot ["index-roots" name]) ipld/link-cid))

(defn commit-delta!
  "Commit `quads` ON TOP of `prev-commit-cid` without rebuilding the indices,
  and return the new commit CID.

  `commit!` flattens four in-memory index maps and builds four trees from
  scratch, so a caller holding a large graph must materialize all of it to add
  one fact. That is why a fold is O(graph) however little novelty it has, and
  why folding a million-entity graph does not fit in a Worker's budget. Here
  each index's previous tree is extended in place through
  `prolly-tree/insert-many`: only the leaves the new keys land in are read and
  rewritten, and the internal levels are re-chunked once.

  The result is CID-IDENTICAL to `(commit! put! db prev schema-version ...)`
  for the db that would result from asserting the same quads — the tests treat
  any divergence as a failure. It has to be: the whole point of a
  content-addressed snapshot is that the same content has the same name, and a
  delta path that produced a different CID for the same graph would break
  every equality check above it — CAS, dedup, replication — while looking like
  it worked.

  `prev-commit-cid` nil commits the quads as a first snapshot. `quads` is a
  seq of `{:s :p :o}`. `ref?` (default `ipld.core/link?`) decides whether `:o`
  is also indexed in `:ocp`, matching `assert-quad`. `get-fn` reads blocks;
  everything else matches `commit!`'s contract, including its
  synchronous-JVM / Promise-cljs split."
  ([put! get-fn prev-commit-cid quads schema-version blind-fn encrypt-fn]
   (commit-delta! put! get-fn prev-commit-cid quads schema-version blind-fn
                  encrypt-fn ipld/link?))
  ([put! get-fn prev-commit-cid quads schema-version blind-fn encrypt-fn ref?]
   (let [snapshot (when prev-commit-cid (ipld/decode (get-fn prev-commit-cid)))
         ->link #(some-> % ipld/link)
         triples-for (fn [index] (keep #(index-triple index % ref?) quads))]
     #?(:clj
        (let [roots (into {}
                          (map (fn [[index name]]
                                 (let [entries (mapv (fn [t]
                                                       [(pr-str (mapv #(blind-fn (blind-input %)) t))
                                                        (encrypt-fn (v/encode-value t))])
                                                     (triples-for index))]
                                   [name (->link (pt/insert-many
                                                  put! get-fn
                                                  (prev-root snapshot name)
                                                  entries))])))
                          index-names)]
          (ipld/put-node! put! {"schema-version" schema-version
                                "index-roots" roots
                                "prev" (->link prev-commit-cid)}))
        :cljs
        (-> (pmap-async
             (fn [[index name]]
               (-> (pmap-async
                    (fn [t]
                      (-> (pmap-async blind-fn (mapv blind-input t))
                          (.then (fn [blinded]
                                   (-> (encrypt-fn (v/encode-value t))
                                       (.then (fn [ct] [(pr-str blinded) ct])))))))
                    (vec (triples-for index)))
                   ;; `insert-many-async`, and the await is the point.
                   ;;
                   ;; This line has now been wrong in two different ways. It
                   ;; originally `.then`ed the SYNCHRONOUS `pt/insert-many` --
                   ;; written as though an async variant existed when none did
                   ;; -- so `commit-delta!` had never once run on
                   ;; ClojureScript: an empty index with no previous root
                   ;; returns nil and `(.then nil ...)` throws, a non-empty one
                   ;; returns a CID string whose `.then` is not a function.
                   ;; That was fixed by calling it synchronously, which
                   ;; completed but left a second defect: `insert-many` ignores
                   ;; what `put!` returns, so on a Worker store -- the only
                   ;; place this branch runs -- the blocks were never waited
                   ;; on, and the commit node naming them could be published
                   ;; while they were still in flight.
                   ;;
                   ;; `prolly-tree` grew `insert-many-async` for exactly this,
                   ;; so the shape the original author reached for is now the
                   ;; correct one: await the tree write before linking its root.
                   (.then (fn [entries]
                            (-> (pt/insert-many-async put! get-fn
                                                      (prev-root snapshot name)
                                                      (vec entries))
                                (.then (fn [root] [name (->link root)])))))))
             index-names)
            ;; The commit node's OWN write has to be awaited too, and
            ;; `ipld/put-node!` cannot do it: it calls `(put! cid bytes)` and
            ;; discards the result to return the cid, which is right for the
            ;; synchronous port it was written against and drops the promise
            ;; here. Awaiting the index roots while letting the node that
            ;; names them race would fix the smaller half of the problem and
            ;; leave the published head pointing at a block in flight.
            (.then (fn [pairs]
                     (let [{:keys [cid bytes]}
                           (ipld/node->block {"schema-version" schema-version
                                              "index-roots" (into {} pairs)
                                              "prev" (->link prev-commit-cid)})]
                       (-> (js/Promise.resolve (put! cid bytes))
                           (.then (fn [_] cid)))))))))))
