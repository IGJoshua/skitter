(ns user
  (:require
   [clojure.spec.alpha :as s]
   [farolero.core :as far :refer [handler-bind handler-case restart-case]]
   [skitter.runtime :as r]
   [skitter.builtins :as b]))

(defonce
  ^{:doc "Code to run once when the environment is loaded."}
  on-load
  (do
    (alter-var-root #'farolero.core/*debugger-hook* (constantly nil))))
