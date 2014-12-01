(ns Calc.main
  (:require [Calc.core :as c])
  (:gen-class))

(defn -main
  ([] (c/repl nil))
  ([args & r] (c/repl args)))
