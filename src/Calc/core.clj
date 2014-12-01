(ns Calc.core
  (:require [clojure.string :as str]
            [clojure.core.match :refer [match]])
  #_(:gen-class))

(set! *warn-on-reflection* true)


;; ------------------------------ general helpers

(defn print-pass [txt] (println txt) txt)

(defmacro throwex [msg] `(throw (Exception. ~msg)))

(defn round2
  "Round a double to the given precision (number of significant digits)"
  [precision d]
  (let [factor (Math/pow 10 precision)]
    (/ (Math/round (* d factor)) factor)))

;; ------------------------------ program


;; calc vars (funs are later on)
(def vars (atom {"last" 0, "nil" "", "true" "1", "false" "0"}))

;pattern: only match whole words
(defn expand-inner [line vrs]
  (reduce (fn [acc [k v]] (str/replace acc (re-pattern (str "\\b" k "\\b")) (str v))) line vrs))


(defn expand           ;;also sanitizes (nil, false... would cause problems...)
  ([line vrs]              ;;expand until no more change occured
   (let [new (expand-inner line vrs)]
     (if (= line new)
       new
       (recur new vrs))))
  ([line] (expand line @vars)))

(defn tokenize ;; -> num, :op, :Xpar, symbol (fns), :<arg num>, :cm (comma), :if{,end,delim}
  ([str args]
   (binding [*read-eval* false]
     (->> str
          (re-seq #"\d+[\./]\d+|,|[a-zA-Z_!?$]\w*[!?$\w]*|\d+|[+*-/\(\)\[\]\|]|<=|>=|<|>")
          ;(map #(do (println "tknz: " %1) %1))
          (map #(case %1
                  "+" :+
                  "-" :neg ;; resolve in 'correct-minus
                  "*" :*
                  "/" :/
                  "(" :lpar
                  ")" :rpar
                  "," :cm
                  "[" :if     ;;these should be processed out into a vector
                  "]" :ifend
                  "|" :ifdelim
                  "<" 'lt
                  ">" 'gt
                  "<=" 'lteq
                  ">=" 'gteq
                  (or (args %1)  ;; args: {"arg_name" :<arg num>} ;;or whatever...
                      (read-string %1))) ))))
  ([str] (tokenize str {})))

(defn correct-minus [tokens] ;; (-5) vs 8-5
  (map (fn [pred cur] ;; traverses pairs and if preceeding makes sense to be substracted from...
         (if (not= cur :neg) cur ;; only chage :neg
           (if (or (#{:ifend :rpar} pred) (number? pred)                      ;; after ] ) num arg ;; not funs!
                   (and (keyword? pred) (number? (read-string (name pred)))))
             :-     ;; minus makes sense here (minus operator)
             'neg)) ;; just negates (actual function)
         ) (cons nil tokens) tokens)) ;;shift first; 'start' is nil


(defn tokens-tree                                                      ;; resolving branches: ifs
  ([tokens [bc & br :as buffer]]                                       ;; buffer contains subtrees; tokens are added to first subtree
   (match tokens
          ([:if      & r]:seq)  (let [[nw rst] (tokens-tree r '([]) )] ;; get recursively `if block` and rest
                                  (recur rst (cons (conj bc nw) br)))  ;; continue on rest and add new to end of first buffer-subtree
          ([:ifend   & r]:seq)  [(vec (reverse buffer)) r]             ;; return tuple: [buffer-part continuation]; reverse?: stack buffer
          ([:ifdelim & r]:seq)  (recur r (cons [] buffer))             ;; add new empty subtree to buffer
          ([tkn      & r]:seq)  (recur r (cons (conj bc tkn) br))      ;; add token to first subtree of buffer
          ([]            :seq)  [(vec (reverse buffer)) []]            ;; end of tokens
          ; :else          (println tokens " " buffer)  ;;DEBUG
          ))
  ([tokens] (ffirst (tokens-tree tokens '([]) ))))                     ;; start with 1 empty subtree


(def precedence {:+ 2 :- 2 :* 3 :/ 3})  ;;all left associative
(defn operator? [x] (#{:+ :- :* :/} x))

;(defn numOrArg? [x] (or (number? x) (and (keyword? x) (number? (read-string (name x))))))

(defn numOrArg? [x] (or (number? x) (and (keyword? x) (-> x name read-string number?))))

; infix to postfix
(defn shunting-yard
  ([tokens] (shunting-yard tokens []))
  ([input stack]
   (match [input              stack             ]                                                   ;; (ic: input-current; sr: stack-rest, etc.)
          [([] :seq)          ([] :seq)         ]  (lazy-seq nil)                                   ;; end of list
          [([] :seq)          ([:lpar & _]:seq) ]  (throwex "unmatched left parent")                ;; invalid: unmatched left-pars at end
          [([] :seq)          ([c & r]:seq)     ]  (cons c (lazy-seq (shunting-yard [] r)))         ;; pour stack to output
          [([:rpar & _ ]:seq) ([] :seq)         ]  (throwex "unmatched right parent")
          [([:lpar & ir]:seq) stack             ]  (shunting-yard ir (cons :lpar stack))            ;; just push left-par on stack
          [([:rpar & ir]:seq) ([:lpar & sr]:seq)]  (shunting-yard ir sr)                            ;; pop all up to :lpar (stop condition)
          [([:rpar & _ ]:seq) ([sc & sr]:seq)   ]  (cons sc (lazy-seq (shunting-yard input sr)))    ;; pop all up to :lpar (op, fun)

          [([(ic :guard numOrArg?) & ir]:seq) _ ]  (cons ic (lazy-seq (shunting-yard ir stack)))    ;; just pass number/arg to output
          [([(ic :guard symbol?)   & ir]:seq) _ ]  (shunting-yard ir (cons ic stack))               ;; add fun to stack

          [([:cm & _ ]:seq)   ([] :seq)         ]  (throwex "comma outside function call")
          [([:cm & ir]:seq)   ([:lpar & sr]:seq)]  (shunting-yard ir stack)                         ;; 'start' of fn: end popping operators
          [([:cm & _ ]:seq)   ([sc & sr]:seq)   ]  (cons sc (lazy-seq (shunting-yard input sr)))    ;; pop all ops before :lpar

          [([(ic :guard operator?) & ir]:seq) ([]:seq)]          (shunting-yard ir [ic])            ;; add operator to empty stack
          [([(ic :guard operator?) & ir]:seq) ([:lpar & _]:seq)] (shunting-yard ir (cons ic stack)) ;; add operator to stack

          [([(ic :guard operator?) & ir]:seq) ([(top :guard symbol?) & sr]:seq)]                    ;; op pops (fn: highest precedence)
          (cons top (lazy-seq (shunting-yard input sr)))                                            ;; pop comcanceplete fns

          [([(ic :guard operator?) & ir]:seq) ([(top :guard operator?) & sr]:seq)]                  ;; op race
          (if (<= (precedence ic) (precedence top))                                                 ;; is ok to add? : (or pop first)
            (cons top (lazy-seq (shunting-yard input sr)))                                          ;; pop all (not bigger) operators
            (shunting-yard ir (cons ic stack)))                                                     ;; add operator to stack

          [([(ic :guard vector?) & ir]:seq) _]                                                      ;; process each subtree (for branching)
          (cons (mapv shunting-yard ic) (lazy-seq (shunting-yard ir stack)))

          :else (throwex (str "unmatched: [" (apply str (rest(interleave (repeat " ")input))) "] " stack))
          )))



;;functions compiled to RPN, with :<arg num> placeholders for arguments; [arg-count rpn]
(def funs (atom {'sqr    [1 [:1 :1 :*]]
                 'avg    [2 [:1 :2 :+ 2 :/]]
                 'avg3   [3 [:1 :2 :3 :+ :+ 3 :/]]
                 'neg    [1 [0 :1 :-]]
                 'inc    [0 [1 :+]]     ;; partial functions:
                 'dec    [0 [1 :-]]
                 'dup    [1 [:1 :1]]}))

(defn build-fun [line]
  (binding [*read-eval* false]
    (let [r-def #"^\s*[Dd][Ee][Ff]\s+([a-zA-Z_?!$][\w?!$]*)\s*(\([^)]*\))\s*(.*)"
          [_ name argstr body] (or (re-find r-def line) (throwex (str "ivalid func definition: " line)))
          args (read-string argstr)
          argmap (into {} (map-indexed (fn [i x] [(str x) (keyword (str i))]) (cons nil args)))] ;;cons nil: dummy: starts at zero
      [(symbol name) [(count args) (-> body
                                       (expand (apply dissoc (cons @vars (keys argmap))))
                                       (tokenize argmap)
                                       correct-minus
                                       tokens-tree
                                       shunting-yard)]])))

(defn add-fun!
  ([line] (apply add-fun! (build-fun line)))
  ([name body] (swap! funs #(assoc %1 name body)) [name body]))

(defn apply-fun [rpn args]
  (let [argmap (into {} (map-indexed (fn [i x] [(keyword (str i)) x]) (cons nil args)))
        ] ;;cons nil: starts with zero: just shift
    (map (fn rec [x] (cond
                      (vector? x) (mapv rec x)  ;; vectors need to stay vectors, others shouldn't change
                      (sequential? x) (map rec x)
                      :else (argmap x x))) rpn)))

(defn rpn-branch [rpn-eval c] ;; if, branching; adds correct branch to input
  (case (count c)
    0 nil
    1 (do (rpn-eval (first c)) nil)                                ;; just eval for side effects
    2 (let [[cnd t    ] c] (if (not= 0 (rpn-eval cnd)) t  ))       ;; no else (condition, true branch); nothing else
    3 (let [[cnd t f  ] c] (if (not= 0 (rpn-eval cnd)) t f))       ;; both branches possible
    4 (let [[cnd p z n] c] (let [choice (rpn-eval cnd)]
                             (cond
                              (pos? choice) p
                              (neg? choice) n
                              :else         z ;; zero branch
                              )))
    ;else:
    (let [[cnd & branches] c] (get (vec branches) (int (rpn-eval cnd))) ) ;; cond is index to rest (too big: nil)
    ))

(defn rpn-eval
  ([x] (rpn-eval x []))
  ([[c & r :as input] [t s & rs :as stack]]
   ;(println c " " r " " t " " s " " rs " : " input " " stack)
   (if (empty? input)
     t
     (cond
      ;special functions:
      (= 'ratio c) (if (integer? t)  ;;num -> numerat. denomi.
                     (recur r (cons 1 (cons t (rest stack))))
                     (let [n (rationalize t)] (recur r (cons (denominator n) (cons (numerator n) (rest stack))))))
      (= 'round c) (recur r (cons (round2   s t) rs          )) ; precision, num -> rounded
      (= 'log   c) (recur r (cons (Math/log   t) (rest stack)))
      (= 'log10 c) (recur r (cons (Math/log10 t) (rest stack)))

      ;generic cases:
      (number? c)   (recur r (cons c stack))                                                          ;; add num to stack
      (operator? c) (recur r (cons (({:+ +', :- -', :* *', :/ /} c) s t) rs))                         ;; eval binary fn: operator
      (symbol? c)   (let [[arity rpn] (or (@funs c) (throwex (str "unknown function: " c)))           ;; find func
                          args (reverse (take arity stack))]                                          ;; build args from stack
                      (recur (concat (apply-fun rpn args) r) (drop arity stack)))                     ;; add applied fun to input
      (keyword? c)  (throwex (str "missing function argument: " c))
      (vector? c)   (recur (concat (rpn-branch rpn-eval c) r) stack)                      ;; if, branching; adds correct branch to input

      :else (throwex (str "rpn-eval: unknown token: " c))
      ))))


(defn line-eval [line]
  (let [res (-> line expand tokenize correct-minus tokens-tree shunting-yard rpn-eval)]
      (swap! vars #(assoc %1 "last" res))
      res))


(defn add-var! [line]
  (let [rg #"^\s*[Vv][Aa][RrLl]\s+([a-zA-Z_@]\w*)\s+(.*)"
        [_ name body] (or (re-find rg line) (throwex (str "add-var: invalid line")))]
    ;(println name " " body)
    (swap! vars #(assoc %1 name (line-eval body)))
    (@vars name)))


(defn repl-line [line]
  (cond
   (nil? line) :exit
   (re-matches #"^\s*exit.*" line) :exit
   (re-matches #"^\s*[dD][eE][fF].*" line) (add-fun! line)
   (re-matches #"^\s*[vV][aA][rRlL].*" line) (add-var! line)
   :else  (line-eval line)
   ))


(defn repl "main enetery point"
  ([x] (match x
              nil (recur
                   (try
                     (print ">") (flush)
                     (-> (read-line) repl-line)
                     (catch Exception e
                       (do
                         (swap! vars #(assoc %1 "last" 0))
                         [:err (.getMessage e) e]))))
              :exit nil
              [:err msg e] (recur (println "ERROR: " msg))
              txt (recur (printf "$ %s\n" txt))
              ))
  ([] (repl nil)))

;; ------------------

(def lib
  "
  def precision() 0.00002                         | for iterative methods and such...
  def prec_digits() neg round(0, log10 precision) | ~ how many decimal places
  def near?(x, y) (abs(x-y)) < (abs precision)    | kinda crazy, but...

  def kill  (x)
  def kill2 (x, y)
  def kill3 (x, y, z)

  def not (x)    [x|0|1]
  def or  (x, y) [x|x|y]
  def and (x, y) [x|[y|x|0]|0]
  def nor (x, y) [x|0|not y]
  def nand(x, y) [x|not y|1]
  def xor (x, y) [x|not y|y]
  def xnor(x, y) [x|y|not y]
  def impl(x, y) [x|y|1]
  def bool(x)    [x|1|0]                 | normalize to 1 or 0


  def gt  (x, y) [x-y|1|0|0]
  def gteq(x, y) [x-y|1|1|0]
  def lt  (x, y) [x-y|0|0|1]
  def lteq(x, y) [x-y|0|1|1]
  def eq  (x, y) [x-y|0|1|0]
  def neq (x, y) [x-y|1|0|1]
  def neg?(x)    x < 0
  def pos?(x)    x > 0
  def abs (x)    [neg? x|neg x|x]

  def sqrt_l1(S, last, cur) [last near? cur|cur|sqrt_l1(S, cur, (last + S / last)/2)]    | iterative
  def sqrt(x) sqrt_l1(x, x, x*2 + 0.1)

  def pow  (x,p) [p|x*pow(x, dec p)|1]   | power, only integer exponent

  def fact (x) [x|x * fact dec x|1]      | simple factorial
  def fact2_l1(a, x) [x|f(a*x, dec x)|a] | accumulated factorial
  def fact2(x)       1 fact2_l1 x

  def root_l1(A, n, nmi,  last, cur) [last near? cur|cur|root_l1(A, n, nmi, cur, (nmi*last + A / pow(last, nmi))/n)]    | iterative
  def root(x, n) root_l1(x, n, n-1, x, x*2 +0.1)                                                | extremly slow for larger vaules...

  def exp_l1(x, num, denom) pow(root(x, denom), num)
  def exp (x, y) [neg? y| 1/exp(x, neg y) | x (y ratio) exp_l1]

  def logn(x, n) log(x)/log(n)

  def ackermann(m, n) [m|ackermann(m-1, [n|ackermann(m, n-1)|1])|n+1]

  ")
(doseq [f (str/split-lines lib)] (repl-line f))

(println "Calc.core:loaded.")






