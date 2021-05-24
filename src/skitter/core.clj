(ns skitter.core
  (:refer-clojure :exclude [resolve apply eval destructure])
  (:require
   [clojure.spec.alpha :as s]
   [farolero.core :as far :refer [handler-case handler-bind restart-case]])
  (:gen-class))

(def expr-types #{:expr :call :prompt :test :def :eval-val :ns-pop
                  :env-pop :env-push :env-extend
                  :binding-push :binding-pop :binding-set})
(s/def ::expr-type expr-types)
(s/def ::expr (s/cat :type ::expr-type
                     :args (s/* any?)))

(def val-types #{:val :prompt})
(s/def ::val-type val-types)
(s/def ::val (s/tuple ::val-type any?))

(s/def ::env (s/or :env-map (s/map-of symbol? any?)
                   :prompt #{:prompt}))

(s/def ::expr-stack (s/coll-of ::expr :kind seq?))
(s/def ::value-stack (s/coll-of ::val :kind vector?))
(s/def ::env-stack (s/coll-of ::env :kind seq?))
(s/def ::ns (s/coll-of symbol?))
(s/def ::bindings (s/map-of symbol? (s/coll-of any?)))
(s/def ::cont (s/keys :req [::ns]
                      :opt [::env-stack ::expr-stack
                            ::value-stack ::bindings]))

(defn make-cont
  [ns]
  {::ns (list ns)})

(def special-operator?
  '#{quote lit def let binding if shift reset})

(s/def ::special-operator special-operator?)

(def literal-types '#{clo mac cont})
(s/def ::literal-type literal-types)
(s/def ::literal (s/cat :lit '#{lit}
                        :type ::literal-type
                        :args (s/* any?)))
(s/def ::fn-literal (s/cat :lit '#{lit}
                           :clo '#{clo}
                           :ns symbol?
                           :env ::env
                           :arglist (s/coll-of symbol? :kind vector?)
                           :body (s/* any?)))
(s/def ::mac-literal (s/cat :lit '#{lit}
                            :clo '#{mac}
                            :ns symbol?
                            :env ::env
                            :arglist (s/coll-of symbol? :kind vector?)
                            :body (s/* any?)))
(s/def ::cont-literal (s/cat :lit '#{lit}
                             :name '#{cont}
                             :cont ::cont))

(s/def ::ns-map ::env)
(s/def ::ns-publics (s/coll-of symbol? :kind set?))
(s/def ::reexports (s/map-of symbol? symbol?))
(s/def ::namespace (s/keys :req [::ns-map ::ns-publics ::reexports]))
(s/def ::global-env (s/map-of symbol? ::namespace))

(defonce global-env (atom {}))

(defn resolve
  [current-ns bindings local-env sym]
  (restart-case (or
                 (let [s (symbol (name sym))
                       globals @global-env]
                   (if (special-operator? s)
                     s
                     (if-let [ns (some-> sym
                                         namespace
                                         symbol)]
                       (or (some #(get % sym) bindings)
                           (and ((get-in globals [ns ::ns-publics]) s)
                                (get-in globals [ns ::ns-map s]))
                           (loop [reexported-ns (get-in globals [ns ::reexports s])]
                             (when reexported-ns
                               (or (and (contains? (get-in globals [reexported-ns ::ns-publics]) s)
                                        (get-in globals [reexported-ns ::ns-map s]))
                                   (recur (get-in globals [reexported-ns ::reexports s]))))))
                       (or (get local-env s)
                           (get-in globals [current-ns ::ns-map s])
                           (loop [reexported-ns (get-in globals [current-ns ::reexports s])]
                             (when reexported-ns
                               (or (and (contains? (get-in globals [reexported-ns ::ns-publics]) s)
                                        (get-in globals [reexported-ns ::ns-map s]))
                                   (recur (get-in globals [reexported-ns ::reexports s])))))))))
                 (far/error ::unresolved-symbol
                            :symbol sym
                            :current-ns current-ns
                            :env local-env))
    (::far/use-value [v] v)))
(s/fdef resolve
  :args (s/cat :current-ns symbol?
               :bindings ::bindings
               :local-env ::env
               :sym symbol?))

(defmulti pop-expr
  (fn [cont]
    (let [[expr] (::expr-stack cont)]
      (first expr))))
(s/fdef pop-expr
  :args (s/cat :cont ::cont)
  :ret ::cont)

(defmulti eval
  (fn [cont expr]
    (cond
      (seq? expr) (cond
                    (special-operator? (first expr)) (first expr)
                    :else :list)
      (symbol? expr) :sym
      :else :self)))

(defmethod pop-expr :expr
  [cont]
  (eval (update cont ::expr-stack next)
        (second (first (::expr-stack cont)))))

(defmethod eval :self
  [cont expr]
  (update cont ::value-stack conj [:val expr]))

(defn macro?
  [expr]
  (s/valid? ::mac-literal expr))

(defmethod eval :list
  [cont expr]
  (clojure.core/apply update cont ::expr-stack conj
                      [:call (count expr)]
                      (map (fn [expr] [:expr expr])
                           (reverse
                            (if (macro? (let [[op & args] expr]
                                          (cond
                                            (symbol? op) (resolve (first (::ns cont)) (::bindings cont)
                                                                  (first (filter map? (::env-stack cont))) op)
                                            :else op)))
                              (cons (first expr) (map #(list 'quote %) (next expr)))
                              expr)))))

(defmethod eval :sym
  [cont expr]
  (update cont ::value-stack conj [:val (resolve (first (::ns cont)) (::bindings cont)
                                                 (first (filter map? (::env-stack cont))) expr)]))

(defmethod eval 'quote
  [cont expr]
  (update cont ::value-stack conj [:val (first (next expr))]))

(defmethod eval 'lit
  [cont expr]
  (update cont ::value-stack conj [:val expr]))

(defmethod eval 'def
  [cont expr]
  (far/assert (= 3 (count expr)) [] "def with other than 3 arguments")
  (update cont ::expr-stack conj [:def (second expr)] [:expr (nth expr 2)]))

(defmethod eval 'let
  [cont expr]
  (far/assert (vector? (second expr)) "let with a non-vector binding")
  (far/assert (even? (count (second expr))) "let with a non-even binding vector")
  (let [[bindings & body] (next expr)
        bindings (mapcat (fn [[sym expr]]
                           [[:expr expr] [:env-extend sym]])
                         (partition 2 bindings))
        exprs (concat (list* [:env-push (first (filter map? (::env-stack cont)))] bindings)
                      (map (fn [expr] [:expr expr]) body)
                      '([:env-pop]))]
    (clojure.core/apply update cont ::expr-stack conj (reverse exprs))))

(defmethod eval 'binding
  [cont expr]
  (far/assert (vector? (second expr)) "binding with a non-vector binding")
  (far/assert (even? (count (second expr))) "binding with a non-even binding vector")
  (far/assert (every? #(handler-case (resolve (first (::ns cont)) (::bindings cont) nil %)
                         (:no-error [_] true)
                         (::far/error [& _] false))
                      (map first (partition 2 (second expr))))
              []
              "every symbol being bound to resolves")
  (let [[bindings & body] (next expr)
        bindings (mapcat (fn [[sym expr]]
                           [[:expr expr] [:binding-set sym]])
                         (partition 2 bindings))
        exprs (concat (list* [:binding-push] bindings)
                      (map (fn [expr] [:expr expr]) body)
                      '([:binding-pop]))]
    (clojure.core/apply update cont ::expr-stack conj (reverse exprs))))

(defmethod eval 'if
  [cont expr]
  (let [[test then else] (next expr)]
    (update cont ::expr-stack conj [:test then else] [:expr test])))

(defmethod eval 'shift
  [cont expr]
  (let [[prompt-name cc-sym & body] (next expr)
        not-prompt (complement #{[:prompt prompt-name]})
        saved-envs (take-while not-prompt
                               (::env-stack cont))
        [saved-exprs escape-exprs] (split-with not-prompt
                                               (::expr-stack cont))
        [saved-vals escape-vals] (split-with not-prompt
                                             (::value-stack cont))
        saved-bindings
        (reduce-kv
         (fn [m k v]
           (assoc m k (take-while not-prompt v)))
         {} (::bindings cont))
        saved-cont (list
                    'lit
                    'cont
                    (assoc (make-cont (first (::ns cont)))
                           ::expr-stack saved-exprs
                           ::value-stack saved-vals
                           ::env-stack saved-envs
                           ::bindings saved-bindings))
        [env & envs] (::env-stack cont)
        new-env (concat (if (map? env)
                          [(assoc env cc-sym saved-cont)]
                          [{cc-sym saved-cont} env])
                      envs)]
    (assoc cont
           ::env-stack new-env
           ::expr-stack (cons [:expr (cons 'do body)] escape-exprs)
           ::value-stack escape-vals)))

(defmethod eval 'reset
  [cont expr]
  (let [[prompt-name & body] (next expr)]
    (-> cont
        (update ::expr-stack conj [:prompt prompt-name] [:expr (cons 'do body)])
        (update ::value-stack conj [:prompt prompt-name])
        (update ::env-stack conj [:prompt prompt-name])
        (update ::bindings #(reduce-kv
                             (fn [m k v]
                               (assoc m k (cons [:prompt prompt-name] v)))
                             {} %)))))

(defmulti apply
  (fn [cont f args]
    (if-not (symbol? f)
      [:lit (second f)]
      f)))

(defn destructure
  [arglist args]
  (loop [acc {}
         arglist arglist
         args args]
    (if arglist
      (cond
        ('#{&} (first arglist)) (assoc acc (second arglist) args)
        :else (recur (assoc acc (first arglist) (first args))
                     (next arglist)
                     (next args)))
      acc)))

(defmethod apply '[:lit clo]
  [cont [_ _ ns closed-env arglist & body] args]
  (let [local-env (merge closed-env
                         (destructure arglist args))
        {::keys [expr-stack]} cont]
    (-> cont
        (update ::ns conj ns)
        (update ::env-stack conj local-env)
        (update ::expr-stack conj [:env-pop] [:expr (cons 'do body)]))))

(defmethod apply '[:lit mac]
  [cont [_ _ ns closed-env arglist & body :as macro] args]
  (let [local-env (merge closed-env
                         (destructure arglist args))
        env {'&env (first (filter map? (::env-stack cont)))
             '&form (cons macro args)}
        {::keys [expr-stack]} cont]
    (-> cont
        (update ::ns conj ns)
        (update ::env-stack conj (merge local-env env))
        (update ::expr-stack conj [:eval-val nil] [:env-pop] [:expr (cons 'do body)]))))

(defmethod apply '[:lit cont]
  [cont [_ _ called-cont] args]
  (assoc cont
         ::ns (concat (::ns called-cont) (::ns cont))
         ::env-stack (concat (::env-stack called-cont) (::env-stack cont))
         ::expr-stack (concat (::expr-stack called-cont) (::expr-stack cont))
         ::value-stack (cons [:val (first args)] (concat (::value-stack called-cont) (::value-stack cont)))
         ::bindings (reduce-kv
                     (fn [m k v]
                       (update m k concat v))
                     (::bindings called-cont)
                     (::bindings cont))))

(defmacro defbuiltin
  [name reexport? cont-sym arglist & body]
  `(do
     (defmethod apply '~name
       [cont# _# args#]
       (-> cont#
           (update ::value-stack
                   conj [:val (let [~cont-sym cont#
                                    ~arglist args#]
                                ~@body)])
           (update ::ns conj nil)))
     (swap! global-env assoc-in '[skitter.lang ::ns-map ~name] '~name)
     (swap! global-env update-in '[skitter.lang ::ns-publics] (fnil conj #{}) '~name)
     ~(if reexport?
        `(do
           (swap! global-env assoc-in '[skitter.core ::reexports ~name] 'skitter.lang)
           (swap! global-env update-in '[skitter.core ::ns-publics] (fnil conj #{}) '~name))
        `(swap! global-env assoc-in '[skitter.core ::ns-map ~name] '~name))))

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
                  (swap! global-env assoc-in [(first (::ns cont)) ::reexports sym] ns)
                  (when public?
                    (swap! global-env update-in [(first (::ns cont)) ::ns-publics] conj sym)))
                syms))
        export-map)
  nil)

(defbuiltin reexport-all true
  cont [export-ns public?]
  (run! (fn [sym]
          (swap! global-env assoc-in [(first (::ns cont)) ::reexports sym] export-ns)
          (when public?
            (swap! global-env update-in [(first (::ns cont)) ::ns-publics] conj sym)))
        (get-in @global-env [export-ns ::ns-publics]))
  nil)

(defmethod pop-expr :call
  [cont]
  (let [{::keys [value-stack] [[_ arg-count] & expr-stack] ::expr-stack} cont
        form (reverse (take arg-count value-stack))
        _ (far/assert (every? (comp #{:val} first) form) "all the arguments to a function are values")
        form (map second form)
        value-stack (nthnext value-stack arg-count)]
    (apply (assoc cont
                  ::expr-stack (cons [:ns-pop] expr-stack)
                  ::value-stack value-stack)
           (first form) (next form))))

(defmethod pop-expr :prompt
  [cont]
  (let [{value-stack ::value-stack
         [[_ prompt-name] & expr-stack] ::expr-stack} cont
        [ret-values [[val-type val] & value-stack]]
        (split-with (complement #{[:prompt prompt-name]}) value-stack)]
    (far/assert (and (= :prompt val-type)
                     (= prompt-name val))
                "the prompts are the same")
    (assoc cont
           ::expr-stack expr-stack
           ::value-stack (concat ret-values value-stack)
           ::env-stack (next (drop-while (complement #{[:prompt prompt-name]}) (::env-stack cont)))
           ::bindings (reduce-kv (fn [m k v]
                                   (assoc m k (next (drop-while (complement #{[:prompt prompt-name]}) v))))
                                 {} (::bindings cont)))))

(defmethod pop-expr :env-pop
  [cont]
  (let [{[_] ::expr-stack} cont]
    (-> cont
        (update ::expr-stack next)
        (update ::env-stack next))))

(defmethod pop-expr :env-push
  [cont]
  (let [{[[_ new-env]] ::expr-stack} cont]
    (-> cont
        (update ::expr-stack next)
        (update ::env-stack conj new-env))))

(defmethod pop-expr :env-extend
  [cont]
  (let [{[[_ sym]] ::expr-stack
         [[val-type val]] ::value-stack} cont]
    (far/assert (#{:val} val-type) "the environment is extending with a value")
    (-> cont
        (update ::expr-stack next)
        (update ::value-stack next)
        (update ::env-stack
                (fn [[env & envs]]
                  (far/assert (map? env)
                              "a prompt isn't between making a value and saving it to the environment")
                  (cons (assoc env sym val) envs))))))

(defmethod pop-expr :binding-pop
  [cont]
  (let [{[_] ::expr-stack} cont]
    (-> cont
        (update ::expr-stack next)
        (update ::bindings next))))

(defmethod pop-expr :binding-push
  [cont]
  (let [{[[_ new-env]] ::expr-stack} cont]
    (-> cont
        (update ::expr-stack next)
        (update ::bindings conj {}))))

(defmethod pop-expr :binding-set
  [cont]
  (let [{[[_ sym]] ::expr-stack
         [[val-type val]] ::value-stack} cont]
    (far/assert (#{:val} val-type) "the binding is being set with a value")
    (-> cont
        (update ::expr-stack next)
        (update ::value-stack next)
        (update ::bindings (fn [[env & envs]]
                             (cons (assoc env sym val) envs))))))

(defmethod pop-expr :test
  [cont]
  (let [{[[_ then else] & expr-stack] ::expr-stack
         [[val-type val] & value-stack] ::value-stack} cont]
    (far/assert (#{:val} val-type) "the test is being run on a value")
    (-> cont
        (update ::expr-stack next)
        (update ::expr-stack conj [:expr (if val then else)])
        (assoc ::value-stack value-stack))))

(defmethod pop-expr :eval-val
  [cont]
  (let [{[[val-type val] & value-stack] ::value-stack ::keys [expr-stack]} cont]
    (far/assert (#{:val} val-type) "the value being evaluated is a value")
    (-> cont
        (assoc ::value-stack value-stack)
        (update ::expr-stack next)
        (update ::expr-stack conj [:expr val]))))

(defmethod pop-expr :def
  [cont]
  (let [{[[_ var-name]] ::expr-stack
         [[val-type val] & value-stack] ::value-stack} cont
        sym (symbol (name var-name))]
    (far/assert (#{:val} val-type) "the value being saved to a def is a value")
    (swap! global-env #(cond-> %
                         (not (:private (meta sym))) (update-in [(first (::ns cont)) ::ns-publics] (fnil conj #{}) sym)
                         :always (assoc-in [(first (::ns cont)) ::ns-map sym] val)))
    (-> cont
        (update ::expr-stack next)
        (update ::value-stack next)
        (update ::value-stack conj [:val val]))))

(defmethod pop-expr :ns-pop
  [cont]
  (-> cont
      (update ::ns next)
      (update ::expr-stack next)))

(defn run-expr
  [ns expr]
  (let [cont
        (loop [cont (update (make-cont ns)
                            ::expr-stack conj [:expr expr])]
          (if (seq (::expr-stack cont))
            (recur (pop-expr cont))
            cont))]
    (far/assert (= 1 (count (::value-stack cont))) "there's only one item left on the value stack at the end")
    (far/assert (#{:val} (first (first (::value-stack cont)))) "the last item on the value stack is a value")
    (second (first (::value-stack cont)))))

(defn -main
  [& args]
  )
