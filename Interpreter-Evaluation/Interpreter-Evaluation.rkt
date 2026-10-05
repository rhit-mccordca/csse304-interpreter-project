#lang racket

(require "../chez-init.rkt" racket/trace)
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define-datatype expression expression?
  [var-exp ;;variable expression
   (id symbol?)]
  [var-exps
   (ids list?)]
  [lit-exp ;;literal expression
   (data scheme-value?)]
  [val-exp
   (id expression?)
   (value expression?)]
  [lambda-exp ;;lambda expression
   (id expression?)
   (body list?)]
  [app-exp ;;application expression
   (rator expression?)
   (rand list?)]
  [if-exp ;;if expression
   (bool expression?)
   (if-true expression?)
   (if-else expression?)]
  [let-exp
   (vars expression?)
   ;symbols not expressions,
   ;let-exp (vars var-exps bodies)
   ;vars is list of symbols
   (body list?)]
  [let*-exp
   (vars expression?)
   (body list?)]
  [letrec-exp
   (vars expression?)
   (body list?)]
  [set!-exp
   (id symbol?)
   (value expression?)])
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Again, you'll probably want to use your code from A11b
; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

; Helper Functions
(define (lambda? expr)
  (and (>= (length expr) 3)
       (if (list? (2nd expr))
           (andmap symbol? (2nd expr))
           (symbol? (2nd expr)))))

(define (app? expr)
    (and (pair? expr)
         (list? expr)))

(define (if? expr)
    (and (= (length expr) 4)))

(define (val-exp? expr)
  (and (list? expr)
       (= (length expr) 2)
       (symbol? (1st expr))))

(define (let? expr)
  (and (>= (length expr) 3)
       (list? (2nd expr))
       (andmap val-exp? (2nd expr))))

(define (set!? expr)
  (and (= (length expr) 3)
       (symbol? (2nd expr))))

(define parse-err
  (lambda (expr)
    (error 'parse-exp "parse-error: ~s" expr)))

(define unparse-err
  (lambda (expr)
    (error 'unparse-exp "unparse-error: ~s" expr)))

(define (parse-exp expr)
    (cond
      [(empty? expr) '()]
      [(symbol? expr) (var-exp expr)]
      [(or (vector? expr)
           (string? expr)
           (boolean? expr)
           (number? expr))(lit-exp expr)]
      [(and (pair? expr) (eqv? (1st expr) 'quote)) (lit-exp (2nd expr))]
      [(eqv? (1st expr) 'lambda)
       (if (lambda? expr) (lambda-exp
                           (if (list? (2nd expr))
                               (var-exps (map (lambda (exp) (parse-exp exp)) (2nd expr)))
                               (var-exp (2nd expr)))
                           (map (lambda (exp) (parse-exp exp)) (cddr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'let)
       (if (let? expr) (let-exp (var-exps (map (lambda (exp) (parse-exp exp)) (2nd expr))) (map (lambda (exp) (parse-exp exp)) (cddr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'let*)
       (if (let? expr) (let*-exp (var-exps (map (lambda (exp) (parse-exp exp)) (2nd expr))) (map (lambda (exp) (parse-exp exp)) (cddr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'letrec)
       (if (let? expr) (letrec-exp (var-exps (map (lambda (exp) (parse-exp exp)) (2nd expr))) (map (lambda (exp) (parse-exp exp)) (cddr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'set!)
       (if (set!? expr) (set!-exp (var-exp (2nd expr)) (parse-exp (3rd expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'if)
       (if (if? expr) (if-exp
                       (parse-exp (2nd expr))
                       (parse-exp (3rd expr))
                       (parse-exp (cadddr expr)))
           (parse-err expr))]
      [(val-exp? expr) (val-exp (parse-exp (1st expr)) (parse-exp (2nd expr)))]
      [(app? expr) (app-exp (parse-exp (1st expr))
                            (map (lambda (expr) (parse-exp expr)) (cdr expr)))]
      [else (parse-err expr)]))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Pick your favorite representation based on the lecture

(define apply-env
  (lambda (env id)
    (if (equal? id '+)
        (prim-proc '+)
        (error "this is not a real environment implementation"))))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment
; creates empty env for eval-exp

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp (empty-env) form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  ;;change define to have define contract for env exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-rands rands)])
                 (apply-proc proc-value args))]
      [if-exp (bool if-true if-else)
               (if (eval-exp env bool) (eval-exp env if-true)
                                       (eval-exp env if-else))]
      [let-exp (vars body)
               (let (new-env (extend-env vars (list (eval-exp env (car var-exps))) env))) ;returns value in environment
               (eval-exp new-env (car bodies))]
      ;;lambda is easy??
      [lambda-exp (id body)
                  ;;produce closeure data structure
                  ;;use proc-val
                  ;;add new proc called closure-proc
                  ;;stores 3 rectangle slots (list of symbols, list of bodies, env obj)
                  ;;after invoking, falls into app-exp type then eval rator and rands, then add case to apply-pro using proc-val from before
                  ;;create new env, env has names of lists of symbols, uses list of evaluated operated values (args), parent env stored in closure
                  ;;havin created, evaluate code of closure in the body (then youre done) (uses one line, not complicated)
                  ;;worst case-> claude video
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)]])))
;(trace eval-exp)

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map (lambda (e) (eval-exp env )) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define init-env         ; you'll want to have a global environment with the prim procs and maybe other stuff
  '())

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (first args) (second args))]
      [(-) (- (first args) (second args))]
      [(*) (* (first args) (second args))]
      [(add1) (+ (first args) 1)]
      [(sub1) (- (first args) 1)]
      [(cons) (cons (first args) (second args))]
      [(=) (= (first args) (second args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
