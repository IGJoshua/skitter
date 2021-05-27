(ns skitter.builtins
  (:require
   [skitter.runtime :as r]))

(defmacro defcall
  [name reexport? arglist & body]
  `(do
     (defmethod r/call '~name
       ~arglist
       ~@body)
     (swap! r/global-env assoc-in '[skitter.lang ::r/ns-map ~name] '~name)
     (swap! r/global-env update-in '[skitter.lang ::r/ns-publics] (fnil conj #{}) '~name)
     ~(if reexport?
        `(do
           (swap! r/global-env assoc-in '[skitter.core ::r/reexports ~name] 'skitter.lang)
           (swap! r/global-env update-in '[skitter.core ::r/ns-publics] (fnil conj #{}) '~name))
        `(swap! r/global-env assoc-in '[skitter.core ::r/ns-map ~name] '~name))
     '~name))

(defmacro defbuiltin
  [name reexport? cont-sym arglist & body]
  `(defcall ~name ~reexport?
     [cont# _# args#]
     (-> cont#
         (update ::r/value-stack
                 conj [:val (let [~cont-sym cont#
                                  ~arglist args#]
                              ~@body)])
         (update ::r/ns conj nil))))

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
                  (swap! r/global-env assoc-in [(first (::r/ns cont)) ::r/reexports sym] ns)
                  (when public?
                    (swap! r/global-env update-in [(first (::r/ns cont)) ::r/ns-publics] conj sym)))
                syms))
        export-map)
  nil)

(defbuiltin reexport-all true
  cont [export-ns public?]
  (run! (fn [sym]
          (swap! r/global-env assoc-in [(first (::r/ns cont)) ::r/reexports sym] export-ns)
          (when public?
            (swap! r/global-env update-in [(first (::r/ns cont)) ::r/ns-publics] conj sym)))
        (get-in @r/global-env [export-ns ::r/ns-publics]))
  nil)

(defbuiltin eval true
  cont [to-eval]
  (r/run-expr (first (::r/ns cont)) to-eval))

(defcall apply true
  [cont _ [f & args]]
  (let [args (map (fn [arg] [:val arg]) (apply list* args))]
    (-> cont
        (update ::r/value-stack
                conj [:val f])
        (update ::r/value-stack
                into args)
        (update ::r/expr-stack
                conj [:call (inc (count args))]))))

(defbuiltin read-string true
  _ [s]
  (read-string s))
