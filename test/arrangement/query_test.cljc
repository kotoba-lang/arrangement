(ns arrangement.query-test
  (:require [clojure.test :refer [deftest is testing]]
            [arrangement.core :as arr]
            [arrangement.query :as q]))

(defn- fixture-db []
  (-> (arr/empty-db)
      (arr/assert-quad {:s "alice" :p "role" :o "admin"})
      (arr/assert-quad {:s "alice" :p "name" :o "Alice"})
      (arr/assert-quad {:s "bob" :p "role" :o "user"})
      (arr/assert-quad {:s "carol" :p "role" :o "admin"})))

(def ^:private everything (constantly true))

(deftest bound-subject-routes-to-spo
  (let [db (fixture-db)]
    (is (= #{{:s "alice" :p "role" :o "admin"} {:s "alice" :p "name" :o "Alice"}}
           (q/query db ["alice" nil nil] everything)))
    (is (= #{{:s "alice" :p "role" :o "admin"}}
           (q/query db ["alice" "role" nil] everything)))
    (is (= #{} (q/query db ["alice" "role" "user"] everything)))))

(deftest bound-predicate-only-routes-to-pso
  (let [db (fixture-db)]
    (is (= #{{:s "alice" :p "role" :o "admin"}
             {:s "bob" :p "role" :o "user"}
             {:s "carol" :p "role" :o "admin"}}
           (q/query db [nil "role" nil] everything)))))

(deftest bound-predicate-and-object-routes-to-pos
  (let [db (fixture-db)]
    (is (= #{{:s "alice" :p "role" :o "admin"} {:s "carol" :p "role" :o "admin"}}
           (q/query db [nil "role" "admin"] everything)))))

(deftest fully-unbound-scans-everything
  (let [db (fixture-db)]
    (testing "unbound query returns every quad"
      (is (= 4 (count (q/query db [nil nil nil] everything)))))))

;; ── query-time visibility seam (ADR-2607050500) ─────────────────────────────
;; visible? is REQUIRED -- no permissive-default arity to fall back on.
;; Every call site above already states its own visibility decision.

(deftest visible-is-required
  (is (thrown? #?(:clj clojure.lang.ArityException :cljs js/Error)
               #_:clj-kondo/ignore
               (q/query (fixture-db) [nil nil nil]))
      "arrangement.query refuses to run a query with no stated visibility decision"))

(deftest visible-redacts-without-query-knowing-why
  (let [db (fixture-db)
        admins-only? (fn [{:keys [s]}] (not= "bob" s))]
    (testing "a composing layer can hide specific quads from a result"
      (is (= #{{:s "alice" :p "role" :o "admin"} {:s "carol" :p "role" :o "admin"}}
             (q/query db [nil "role" nil] admins-only?))))
    (testing "visible? applies uniformly across every routing branch"
      (is (= #{{:s "alice" :p "role" :o "admin"} {:s "alice" :p "name" :o "Alice"}}
             (q/query db ["alice" nil nil] admins-only?)))
      (is (= #{{:s "carol" :p "role" :o "admin"}}
             (q/query db [nil "role" "admin"] (fn [{:keys [s]}] (= s "carol")))))
      (is (= 3 (count (q/query db [nil nil nil] admins-only?)))))
    (testing "an always-false visible? redacts everything"
      (is (= #{} (q/query db [nil nil nil] (constantly false)))))))
