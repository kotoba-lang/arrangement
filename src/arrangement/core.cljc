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
            [ipld.core :as ipld]))

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
(defn link->edn
  "A Link becomes `[\"ipld/link\" cid]`; anything else passes through."
  [v] (if (ipld/link? v) ["ipld/link" (ipld/link-cid v)] v))

(defn edn->link
  "Inverse of `link->edn`: reconstructs the Link, or passes through anything
  that isn't the `[\"ipld/link\" cid]` shape."
  [v] (if (and (vector? v) (= 2 (count v)) (= "ipld/link" (first v)))
        (ipld/link (second v))
        v))

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

  `key` is `(pr-str [(blind-fn k1') (blind-fn k2') (blind-fn v')])` (each
  position passed through `link->edn` first, then `blind-fn` — a keyed,
  deterministic MAC, e.g. HMAC-SHA256 — so the leaf key is queryable by
  prefix for a caller who already knows the plaintext component, but is
  NOT the plaintext, and is NOT order-preserving/full ciphertext).

  `val` is `(encrypt-fn (ipld/encode [k1' k2' v']))` — an AEAD ciphertext
  blob of the REAL `(k1' k2' v')` triple. This is the correction: the
  ORIGINAL triple lived only in the (now-blinded, one-way, unrecoverable)
  key, so once the key stopped being plaintext there was nowhere left to
  read the actual s/p/o payload back from — `val` now carries it,
  encrypted, so `cold-datoms` (in `kotoba-lang/kotobase-peer`) can decrypt
  a matched leaf's value to reconstruct the row instead of trying to
  invert the key.

  `blind-fn`/`encrypt-fn` are REQUIRED (no default — matching this
  codebase's no-silent-default stance, ADR-2607050700, same as
  `schema-version` below): synchronous on JVM (`(blind-fn link-edn-
  component) -> string`, `(encrypt-fn bytes) -> bytes`); Promise-returning
  on cljs (see the platform-contract note above). Returns the root CID
  directly on JVM, a `js/Promise` of it on cljs."
  [put! m blind-fn encrypt-fn]
  #?(:clj
     (let [entries (sort-by first
                            (for [[k1 m2] m [k2 vs] m2 v vs
                                  :let [k1' (link->edn k1) k2' (link->edn k2) v' (link->edn v)]]
                              [(pr-str [(blind-fn k1') (blind-fn k2') (blind-fn v')])
                               (encrypt-fn (ipld/encode [k1' k2' v']))]))]
       (pt/build-tree put! entries))
     :cljs
     (let [triples (vec (for [[k1 m2] m [k2 vs] m2 v vs
                              :let [k1' (link->edn k1) k2' (link->edn k2) v' (link->edn v)]]
                          [k1' k2' v']))]
       (-> (pmap-async
            (fn [[k1' k2' v']]
              (-> (pmap-async blind-fn [k1' k2' v'])
                  (.then (fn [blinded]
                           (-> (encrypt-fn (ipld/encode [k1' k2' v']))
                               (.then (fn [ct] [(pr-str blinded) ct])))))))
            triples)
           (.then (fn [entries] (pt/build-tree put! (vec (sort-by first entries)))))))))

(def current-schema-version
  "The current `\"schema-version\"` value for this index shape
  (ADR-2607050500, \"Schema evolution\"). Not a hidden default -- `commit!`
  requires the caller to pass a version explicitly (see below); this is
  just the value to pass when you have no other one in mind. Bump this --
  and give callers a migration path keyed on the old value -- the day the
  4-index shape changes incompatibly."
  1)

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
