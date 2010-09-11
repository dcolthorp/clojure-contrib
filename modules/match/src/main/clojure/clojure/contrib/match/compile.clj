(ns clojure.contrib.match.compile
  (:require [clojure.zip :as zip]
            [clojure.walk :as walk]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities
(defmacro with-gensyms "Create gensyms bound to names." [names & code]
  (let [syms (into []  (map (fn [name] `(gensym '~name)) names))]
    `(let [~names ~syms]
       ~@code)))

(defn variable-binding? "Decide whether the given thing is a directive to bind a variable"
  [v]
  (and (symbol? v)
       (re-find #"^[\w-]+$" (name v))))

(defn class-name? [class]
  (re-find #"\A(?:[a-z0-9]+\.)+[A-Z]\w*\Z" (name class)))

(defn predicate-name? [sym]
  (= \? (last (name sym))))

(defn all-zip [root]
  (zip/zipper #(instance? clojure.lang.Seqable %)
              seq
              #(into (empty %1) %2)
              root))

(defn deep-count [root atom]
  (loop [zipper (all-zip root) n 0]
    (if (zip/end? zipper)
      n
      (if (= (zip/node zipper)
             atom)
        (recur (zip/next zipper) (inc n))
        (recur (zip/next zipper)
               n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; state manipulation/usage helpers
(defn- make-state []
  {:variables (atom #{})})
(defn- add-variable [state & variables]
  (swap! (:variables state) #(into % variables))
  state)
(defn- state-variables [state]
  @(:variables state))

(defn- success "Do whatever a successful match entails. Returns code for a successful match." [state]
  ((:success state) state))

(defn- failure "Do whatever a failed match entails. Returns code for a failed match." [state]
  ((:failure state) state))

(defn- simple-if "Return an if statement testing condition that uses the default success and failure"
  ([state condition] (simple-if state condition (success state)))
  ([state condition true-case] (simple-if state condition true-case (failure state)))
  ([state condition true-case false-case]
     `(if ~condition ~true-case ~false-case)))

(defn- default-match "Returns the code for the default runtime match behavior."
  [pattern matching-name state]
  (simple-if state (list '= matching-name pattern)))


(defn- wrap-result "Wrap succuss and/or failure behavior with the
functions specified. Passes the wrapping functions the current state
with the original success/failure behavior restored when that result
is signaled in a submatch."
  [state & key-wrappers]
  (let [original-results (select-keys state [:success :failure])]
    (loop [state state, key-wrappers key-wrappers]
      (if (empty? key-wrappers)
        state
        (let [[key wrapper & remaining] key-wrappers]
          (recur
           (assoc state key (fn [current-state] (wrapper (merge current-state original-results))))
           remaining))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern match compilation
(declare compile-pattern)


(defn compile-matches "Compiles a list of pattern, match pairs into a
block of code. If the first match fails the following match functions
are never evaluated. "
  [matches success-code failure-code state]
  (if (empty? matches)
    success-code
    (let [[pattern matching & remainder] matches
          matching-name (gensym 'matching)]
      `(let [~matching-name ~matching]
         ~(compile-pattern
           pattern
           matching-name
           (merge state
                  {:success (fn [state] (compile-matches remainder success-code failure-code state))
                   :failure  (fn [_] failure-code)}))))))

(defn wrap-code? [compiled placeholder code]
  (and (< 1 (deep-count compiled placeholder)) (coll? code)))

(defn compile-top-level-match "Compiles a match at the very top level."
  [matches success-code failure-code]
  {:pre [(vector? matches), (even? (count matches))]}
  (with-gensyms [successn failuren]
    (let [success-placeholder (gensym "success")
          failure-placeholder (gensym "failure")
          state (make-state)
          compiled (compile-matches matches success-placeholder failure-placeholder state)
          variables (into [] (state-variables state))
          variable-assigns (mapcat #(vector % nil) variables)
          wrap-success (wrap-code? compiled success-placeholder success-code)
          wrap-failure (wrap-code? compiled failure-placeholder failure-code)]
        `(let [~@variable-assigns
             ~@(if wrap-success (list successn `(fn [~@variables] ~success-code)))
             ~@(if wrap-failure (list failuren `(fn [~@variables] ~failure-code)))]
         ~(walk/prewalk-replace {success-placeholder (if wrap-success `(~successn ~@variables) success-code)
                                 failure-placeholder (if wrap-failure `(~failuren ~@variables) failure-code)}
                                compiled)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern compilation

;; ad-hoc hierarchies for dispatching compilation
(derive clojure.lang.IPersistentList ::function-call)
(derive clojure.lang.Cons ::function-call)
(derive clojure.lang.LazySeq ::function-call)

(defmulti compile-pattern (fn [pattern _ _]
                            (if (nil? pattern)
                              ::nil
                              (class pattern))))

;;; Default compilation matching - use the pattern matcher stored in state
(defmethod compile-pattern :default [pattern matching-name state]
  (default-match pattern matching-name state))

;;; Regular Expressions
(defmethod compile-pattern java.util.regex.Pattern [pattern matching-name state]
  (simple-if state `(and (string? ~matching-name) (re-find ~pattern ~matching-name))))

;;; Variables
(defmethod compile-pattern clojure.lang.Symbol [pattern matching-name state]
  (cond
   (some #(= % pattern) '(_)) (success state)
   (predicate-name? pattern) (simple-if state `(~pattern ~matching-name))
   (variable-binding? pattern) `(let [~pattern ~matching-name]
                                  ~(success (add-variable state pattern)))
   (class-name? pattern) (simple-if state `(instance? ~pattern ~matching-name))
   true (default-match pattern matching-name state)))

;;; Vectors - the sequence type that is destructured, a la let
(defmethod compile-pattern clojure.lang.IPersistentVector [pattern matching-name state]
  (letfn [(compile-rest [pattern matching-name state]
                        (cond
                         (empty? pattern)
                         (simple-if state `(empty? ~matching-name))

                         
                         (= '& (first pattern))
                         (let [pattern-after-& (rest pattern)]
                           (assert (= 1 (count pattern-after-&)))
                           (compile-pattern (first pattern-after-&) matching-name state))

                         
                         true
                         (with-gensyms [seqn firstn restn]
                           `(if-let [~seqn (seq ~matching-name)]
                              (let [~firstn (first ~seqn) ~restn (rest ~seqn)]
                                ~(compile-pattern
                                  (first pattern)
                                  firstn
                                  (wrap-result state
                                               :success
                                               #(compile-rest (rest pattern)
                                                              restn %))))
                              ~(failure state)))))]
    `(if (and
          ~matching-name
          (or
           (instance? clojure.lang.Seqable ~matching-name)
           (instance? Iterable ~matching-name)
           (instance? java.util.Map ~matching-name)
           (.isArray (class ~matching-name))))
       ~(compile-rest pattern matching-name state)
       ~(failure state))))

;;; Maps - match values derived from
;;; the matched value
(defn- compile-map-key-pattern
  "Defines how a form in a value position is used to get the value the pattern in the key position is matched against."
  [key matching-name match-against failure]
  (with-gensyms [valuen]
    (cond

     ;; .foo - match against (.foo %)
     (and (symbol? key)
          (= \. (.charAt (name key) 0)))
     `(if ~matching-name
        (let [~valuen (~key ~matching-name)]
          ~(match-against valuen)))

     ;; (foo %) - match against (foo %)
     (seq? key) 
     `(let [~valuen ~(walk/postwalk-replace {'% matching-name} key)]
        ~(match-against valuen))

     ;; Default - extract key from a
     ;; map-like value and match against that.
     true 
     (with-gensyms [keyn]
       `(let [~keyn ~key]
          (if (contains? ~matching-name ~keyn)
            (let [~valuen (get ~matching-name ~keyn)]
              ~(match-against valuen))
            ~(failure)))))))

(defmethod compile-pattern clojure.lang.IPersistentMap [pattern matching-name state]
  (letfn
      [(compile-rest
        [pattern matching-name state]
        (if (empty? pattern)
          (success state)
          (let [[key subpattern] (first pattern)
                compile-next (fn [valuen]
                               (compile-pattern
                                subpattern valuen
                                (wrap-result state :success
                                             #(compile-rest
                                               (dissoc pattern key)
                                               matching-name %))))]
            (compile-map-key-pattern key matching-name compile-next #(failure state)))))]
    (compile-rest pattern matching-name state)))

;; Lists - function calls
(defmulti compile-list (fn [pat _ _] (first pat)))
(defmethod compile-pattern ::function-call [pattern matching-name state]
  (compile-list pattern matching-name state))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function evaluation

(defmethod compile-list :default [pattern matching-name state]
  (simple-if state (walk/postwalk-replace {'% matching-name} pattern)))


;;; special forms
(defmethod compile-list 'if [[_ test then else] matching-name state]
  (compile-pattern test matching-name
                   (wrap-result state
                                :success #(compile-pattern then matching-name %)
                                :failure #(compile-pattern else matching-name %))))

(defmethod compile-list 'and [[_ & patterns] matching-name state]
  (letfn [(compile-and [patterns matching-name state]
                       (if (empty? patterns)
                         (success state)
                         (compile-pattern (first patterns) matching-name
                                          (wrap-result state :success #(compile-and (rest patterns) matching-name %)))))]
    (compile-and patterns matching-name state)))

(defmethod compile-list 'or [[_ & patterns] matching-name state]
  (letfn [(compile-or [patterns matching-name state]
                      (if (empty? patterns)
                        (failure state)
                        (compile-pattern (first patterns) matching-name
                                         (wrap-result state :failure #(compile-or (rest patterns) matching-name %)))))]
    (compile-or patterns matching-name state)))

(defmethod compile-list 'not [[_ pattern] matching-name state]
  (compile-pattern pattern matching-name
                   (wrap-result state
                                :success failure
                                :failure success)))

(defmethod compile-list 'quote [pattern matching-name state]
  (simple-if state `(= ~pattern ~matching-name)))


(defmethod compile-list 'unquote [pattern matching-name state]
  (simple-if state `(= ~(second pattern) ~matching-name)))
(defmethod compile-list 'clojure.core/unquote [pattern matching-name state]
  (simple-if state `(= ~(second pattern) ~matching-name)))
