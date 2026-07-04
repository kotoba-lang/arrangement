# arrangement

`kotoba-lang/arrangement` is the shared CLJC home for an in-memory
4-covering-index Arrangement (`spo`/`pso`/`pos`/`ocp` — Datomic's own term
for exactly this structure; EAVT/AEVT/AVET/VAET in Datomic's own naming)
plus CID-addressed commit snapshotting via `kotoba-lang/prolly-tree`, and
the pattern-routing query layer over it.

Formerly two repos: `quad-store` (this one, renamed — it stores triples
`{:s :p :o}`, not RDF quads; `Arrangement` names the actual structure
instead of overloading `quad`, and aligns this substrate with Datomic
terminology throughout, per `kotoba : kotobase = Clojure : Datomic`,
ADR-2607032500) and `kqe` (Kotoba Query Engine, merged in here — a pure
routing function over these indices with no storage of its own doesn't
need its own repo). See `90-docs/adr/2607010930-clj-wgsl-migration.md`
Phase 6 for the original landing, and ADR-2607050600 for the rename/merge.

A triple is `{:s subject :p predicate :o object}`. For this landing s/p/o
are opaque strings — dag-cbor round-trips strings exactly but not e.g.
Clojure keywords, so string-only keeps `commit!`'s snapshot honest about
what actually survives `cbor.core` encode/decode (except an `ipld.core/
Link` value, which *is* recognized and preserved end to end — see
`link->edn`/`edn->link`). General typed values are a follow-up.

## Use

```clojure
(require '[arrangement.core :as arr]
         '[arrangement.query :as q])

(def db (-> (arr/empty-db)
            (arr/assert-quad {:s "alice" :p "role" :o "admin"})
            (arr/assert-quad {:s "alice" :p "name" :o "Alice"})))

(arr/entity-attrs db "alice")              ;=> {"role" #{"admin"}, "name" #{"Alice"}}
(arr/by-predicate-value db "role" "admin") ;=> #{"alice"}

;; ref? defaults to ipld.core/link? -- a Link-valued object is reverse-indexed
;; automatically; pass a different predicate to opt out or widen it.
(def db2 (arr/assert-quad db {:s "bob" :p "knows" :o (ipld.core/link "bafy...")}))
(arr/refs-to db2 (ipld.core/link "bafy...")) ;=> {"knows" #{"bob"}}

;; content-addressed commit (same db+prev+schema-version -> same CID).
;; schema-version is required -- pass arr/current-schema-version if you
;; have no other version in mind, but state it.
(def store (atom {}))
(def cid (arr/commit! (fn [c b] (swap! store assoc c b)) db nil arr/current-schema-version))

;; pattern query over the hot db -- visible? is required (Query is a
;; first-class effect, ADR-2607050500); pass (constantly true) to see
;; everything, as an explicit choice.
(q/query db ["alice" nil nil] (constantly true))
;=> #{{:s "alice" :p "role" :o "admin"} {:s "alice" :p "name" :o "Alice"}}
```

## Scope

- 4-index hot (in-memory) Arrangement: full CRUD via `assert-quad`/
  `retract-quad`, point/scan lookups via `entity-attrs`/`by-predicate`/
  `by-predicate-value`/`refs-to`, pattern query via `arrangement.query/
  query` (routes `[s p o]` to whichever index matches the bound
  positions).
- `commit!` snapshots each index to a `prolly-tree` and CID-addresses the
  commit as `{schema-version index-roots prev}` — a real commit chain,
  content-addressed (verified by test: same db+prev+schema-version always
  yields the same commit CID). Index roots and `prev` are **real tag-42
  IPLD links** (via [`kotoba-lang/ipld`](https://github.com/kotoba-lang/ipld);
  empty index → null), so a generic IPLD tool — or `ipld.core/links` —
  walks from a commit block to every index tree with no schema knowledge
  of this repo.
- `ipld.core/Link` values round-trip correctly through the persisted
  index (`link->edn`/`edn->link`), and are auto reverse-indexed via
  `ref?`'s default (`ipld.core/link?`).

**Not in this landing** (tracked follow-ups, not silently omitted):
- Cold (post-commit, prolly-tree-backed) query — the 4 index roots are
  persisted but nothing here reconstructs a hot index from them yet (see
  `kotoba-lang/kotobase-peer`'s `cold-datoms` for a filtered cold read
  that doesn't need one).
- General typed values beyond string + `ipld.core/Link`.
- Full Datalog fixpoint / SPARQL BGP evaluation — `arrangement.query`'s
  own documented scope is triple-pattern only.

## Test

```bash
clojure -M:test        # JVM
npm run test:cljs       # real shadow-cljs (not nbb -- see this org's own
                        # verification discipline, ADR-2607022600 add.3)
```

## License

MIT
