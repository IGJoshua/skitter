(ns skitter.core
  (:refer-clojure :exclude [resolve apply eval])
  (:require
   [clojure.spec.alpha :as s]
   [farolero.core :as far :refer [handler-case handler-bind restart-case]])
  (:gen-class))

(def expr-types #{:expr :call :prompt :env-pop :test})
(s/def ::expr-type expr-types)
(s/def ::expr (s/cat :type ::expr-type
                     :args (s/* any?)))

(def val-types #{:val :prompt})
(s/def ::val-type val-types)
(s/def ::val (s/tuple ::val-type any?))

(s/def ::expr-stack (s/coll-of ::expr :kind seq?))
(s/def ::value-stack (s/coll-of ::val :kind vector?))
(s/def ::env (s/map-of symbol? any?))
(s/def ::env-list (s/coll-of ::env :kind seq?))
(s/def ::ns symbol?)
(s/def ::cont (s/keys :req [::ns ::env-list ::expr-stack ::value-stack]))

(s/def ::ns-map ::env)
(s/def ::global-env (s/map-of symbol? ::ns-map))

(def special-operator?
  '#{lit def let binding if shift reset})

(s/def ::special-operator special-operator?)

(def literal-types '#{clo})
(s/def ::literal-type literal-types)
(s/def ::literal (s/cat :lit '#{lit}
                        :type ::literal-type
                        :args (s/* any?)))
(s/def ::fn-literal (s/cat :lit '#{lit}
                           :clo '#{clo}
                           :env ::env
                           :arglist (s/coll-of symbol? :kind vector?)
                           :body (s/* any?)))

(def global-env (atom {}))

(defn resolve
  [current-ns local-env sym]
  (restart-case (or
                 (let [s (symbol (name sym))
                       global-env @global-env]
                   (if (special-operator? s)
                     s
                     (if-let [ns (some-> sym
                                         namespace
                                         symbol)]
                       (get-in global-env [ns s])
                       (or (get local-env s)
                           (get-in global-env [current-ns s])))))
                 (far/error ::unresolved-symbol))
    (::far/use-value [v] v)))
(s/fdef resolve
  :args (s/cat :current-ns symbol?
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
  (update cont ::value-stack conj expr))

(defmethod eval :list
  [cont expr]
  (apply update cont ::expr-stack conj
         [:call (count expr)]
         (map (fn [expr] [:expr expr]) (reverse expr))))

(defmethod eval :sym
  [cont expr]
  (update cont ::value-stack conj (resolve (::ns cont) (first (::env-list cont)) expr)))

(defmethod eval 'lit
  [cont expr]
  (update cont ::value-stack conj expr))

(defmethod eval 'if
  [cont expr]
  (let [[test then else] (next expr)]
    (update cont ::expr-stack conj [:test then else] test)))

(defmulti apply
  (fn [cont f args]
    (if-not (symbol? f)
      [:lit (second f)]
      f)))

(defmethod apply '[:lit clo]
  [cont [_ _ closed-env arglist & body] args]
  (let [local-env (merge closed-env
                         (zipmap arglist args))
        {::keys [expr-stack value-stack]} cont]
    (-> cont
        (update ::env-list conj local-env)
        (update ::expr-stack conj [:env-pop nil] [:expr (cons 'do body)]))))

(defmethod pop-expr :call
  [cont]
  (let [{::keys [value-stack] [[_ arg-count] & expr-stack] ::expr-stack} cont
        new-stack-count (- (count value-stack) arg-count)
        [f & args] (subvec value-stack new-stack-count)
        value-stack (subvec value-stack 0 new-stack-count)]
    (apply (assoc cont
                  ::expr-stack expr-stack
                  ::value-stack value-stack)
           f args)))

(defmethod pop-expr :prompt
  [cont]
  (let [{[[val-type val] & value-stack] ::value-stack
         [[_ prompt-name] & expr-stack] ::expr-stack} cont]
    (far/assert (and (= :prompt val-type)
                     (= prompt-name val)))
    (assoc cont
           ::expr-stack expr-stack
           ::value-stack value-stack)))

(defmethod pop-expr :env-pop
  [cont]
  (let [{[_ & expr-stack] ::expr-stack} cont]
    (-> cont
        (assoc ::expr-stack expr-stack)
        (update ::env-list next))))

(defmethod pop-expr :test
  [cont]
  ;; TODO: Pop the expression, pop a value, if the value is true, push then,
  ;;       otherwise, push else
  )

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, world!"))
