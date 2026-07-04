(ns arrangement.query
  "`[s p o]` triple-pattern query with wildcards (nil) over an
  `arrangement.core` db, routing to whichever index matches the bound
  positions -- bound subject -> spo, bound predicate only -> pso, bound
  predicate + bound object -> pos, fully unbound -> full spo scan.

  Formerly the standalone `kotoba-lang/kqe` repo (Kotoba Query Engine, named
  after the deleted kotoba-query Rust crate); merged into this repo because
  it is a pure routing function over `arrangement.core`'s indices with no
  storage of its own -- one repo for one Arrangement, not two for a
  structure and its lookup.

  Only the hot (in-memory) `arrangement.core` db is queried here. Cold
  (prolly-tree-backed, post-`commit!`) query and full Datalog
  fixpoint/SPARQL BGP evaluation are explicitly NOT in this landing --
  tracked as follow-ups, not silently omitted.

  `query`'s `visible?` is REQUIRED (ADR-2607050500: \"Query as first-class
  effect\" -- not a bare read). This namespace stays auth-agnostic by
  design (no purpose/scope/capability opinion lives here), but it refuses
  to run a query without the caller stating a visibility decision; there
  is no permissive default to fall back on silently. Pass `(constantly
  true)` to see everything -- that is a caller's explicit choice, not
  this namespace's."
  (:require [arrangement.core :as arr]))

(defn- query* [db [s p o]]
  (cond
    (some? s)
    (into #{}
          (for [[p2 os] (arr/entity-attrs db s)
                :when (or (nil? p) (= p p2))
                o2 os
                :when (or (nil? o) (= o o2))]
            {:s s :p p2 :o o2}))

    (and (some? p) (some? o))
    (into #{} (for [s2 (arr/by-predicate-value db p o)] {:s s2 :p p :o o}))

    (some? p)
    (into #{} (for [[s2 os] (arr/by-predicate db p) o2 os] {:s s2 :p p :o o2}))

    :else
    (into #{} (for [[s2 pm] (:spo db) [p2 os] pm o2 os] {:s s2 :p p2 :o o2}))))

(defn query
  "`pattern` is `[s p o]`, any position `nil` for wildcard. `visible?` is
  applied as a post-filter over every candidate quad before it's returned
  -- see the ns docstring. Returns a set of matching `{:s :p :o}` quads."
  [db pattern visible?]
  (into #{} (filter visible? (query* db pattern))))
