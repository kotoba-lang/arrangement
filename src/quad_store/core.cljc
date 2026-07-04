(ns quad-store.core
  "In-memory 4-index Quad Arrangement -- `spo`/`pso`/`pos`/`ocp`, the same
  naming as the deleted kotoba-query Rust crate's EAVT/AEVT/AVET/VAET
  indices -- plus CID-addressed commit snapshotting via `prolly-tree.core`.

  A quad is `{:s subject :p predicate :o object}`. s/p/o are still treated
  as opaque values for indexing purposes (general typed-value support --
  int/bytes/bool beyond string and `ipld.core/Link` -- remains a follow-up),
  but an `ipld.core/Link` value is now recognized and preserved end to end:
  through the hot db, through a commit snapshot's index-root (`index-root`
  below), and back out again on a cold read (see `kotoba-lang/kotobase-
  engine`'s `cold-datoms`/`hydrate-db`, which call `edn->link` on read).

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

(defn- index-root
  "Flatten one index map into sorted `[key val]` prolly-tree entries and
  build a tree from it. `key` is the printed `[k1 k2 v]` triple (each
  position passed through `link->edn` first, so a Link value survives the
  `pr-str` round-trip) so the whole index is content-addressed by its full
  (s,p,o)-equivalent set; `val` is `true` (membership-only encoding, no
  separate value payload)."
  [put! m]
  (let [entries (sort-by first
                         (for [[k1 m2] m [k2 vs] m2 v vs]
                           [(pr-str [(link->edn k1) (link->edn k2) (link->edn v)]) true]))]
    (pt/build-tree put! entries)))

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
  version` twice returns the same CID."
  [put! db prev schema-version]
  (let [->link #(some-> % ipld/link)          ; empty index -> nil root -> null
        roots {"spo" (->link (index-root put! (:spo db)))
               "pso" (->link (index-root put! (:pso db)))
               "pos" (->link (index-root put! (:pos db)))
               "ocp" (->link (index-root put! (:ocp db)))}]
    (ipld/put-node! put! {"schema-version" schema-version
                          "index-roots" roots "prev" (->link prev)})))
