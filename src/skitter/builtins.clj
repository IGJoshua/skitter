(ns skitter.builtins
  (:require
   [skitter.runtime :as r]))

(defmacro defbuiltin
  [name reexport? cont-sym arglist & body]
  `(do
     (defmethod r/call '~name
       [cont# _# args#]
       (-> cont#
           (update ::value-stack
                   conj [:val (let [~cont-sym cont#
                                    ~arglist args#]
                                ~@body)])
           (update ::ns conj nil)))
     (swap! r/global-env assoc-in '[skitter.lang ::ns-map ~name] '~name)
     (swap! r/global-env update-in '[skitter.lang ::ns-publics] (fnil conj #{}) '~name)
     ~(if reexport?
        `(do
           (swap! r/global-env assoc-in '[skitter.core ::reexports ~name] 'skitter.lang)
           (swap! r/global-env update-in '[skitter.core ::ns-publics] (fnil conj #{}) '~name))
        `(swap! r/global-env assoc-in '[skitter.core ::ns-map ~name] '~name))))

(defbuiltin do true
  _ [& args]
  (last args))

(defbuiltin cons true
  _ [& args]
  (concat (butlast args) (last args)))

(defbuiltin add false
  _ [& args]
  (reduce + args))

(defbuiltin sub false
  _ [& args]
  (reduce - args))

(defbuiltin reexport true
  cont [export-map public?]
  (run! (fn [[ns syms]]
          (run! (fn [sym]
                  (swap! r/global-env assoc-in [(first (::ns cont)) ::reexports sym] ns)
                  (when public?
                    (swap! r/global-env update-in [(first (::ns cont)) ::ns-publics] conj sym)))
                syms))
        export-map)
  nil)

(defbuiltin reexport-all true
  cont [export-ns public?]
  (run! (fn [sym]
          (swap! r/global-env assoc-in [(first (::ns cont)) ::reexports sym] export-ns)
          (when public?
            (swap! r/global-env update-in [(first (::ns cont)) ::ns-publics] conj sym)))
        (get-in @r/global-env [export-ns ::ns-publics]))
  nil)
