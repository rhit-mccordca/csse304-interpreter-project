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

(define (quoted? expr)
  (and (list? expr)
       (= 2 (length expr))
       (eqv? 'quote (car expr))))

(define (literal? expr)
  (or (number? expr)
      (string? expr)
      (boolean? expr)
      (vector? expr)
      (quoted? expr)))

(define-datatype expression expression?
  [lit-exp
   (data literal?)]
  [var-exp
   (id symbol?)]
  
  [lambda-exp
   (vars (lambda (x)
           (or (symbol? x) ((list-of? symbol?) x))))
   (bodies (list-of? expression?))]
  
  [if-exp
   (test-exp expression?)
   (then-exp expression?)
   (else-exp expression?)]
  
  [let-exp
   (vars (list-of? symbol?))
   (var-exps (list-of? expression?))
   (bodies (list-of? expression?))]
  [named-let-exp
   (name symbol?)
   (vars (list-of? symbol?))
   (var-exps (list-of? expression?))
   (bodies (list-of? expression?))]
  [let*-exp
   (vars (list-of? symbol?))
   (var-exps (list-of? expression?))
   (bodies (list-of? expression?))]
  [letrec-exp
   (vars (list-of? symbol?))
   (var-exps (list-of? expression?))
   (bodies (list-of? expression?))]
  
  [set-exp
   (id symbol?)
   (value expression?)]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))])
	

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
   (name symbol?)]
  [closure-proc
   (vars (list-of? symbol?))
   (bodies (list-of? expression?))
   (env environment?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Again, you'll probably want to use your code from A11b

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define (lambda? expr)
  (let ([vars (2nd expr)][bodies (cddr expr)])
    (and (or (symbol? vars) ((list-of? symbol?) vars))
         ((list-of? list?) bodies))))

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
      [(symbol? expr) (var-exp expr)]
      [(literal? expr) (lit-exp expr)]
      [(pair? expr)
       (case (1st expr)
         [(let)
          (if (symbol? (2nd expr))
              (let ([name (2nd expr)]
                    [var-pairs (3rd expr)]
                    [bodies (cdddr expr)])
                (named-let-exp name
                               (map 1st var-pairs)
                               (map parse-exp (map 2nd var-pairs))
                               (map parse-exp bodies)))
              (let ([var-pairs (2nd expr)]
                    [bodies (cddr expr)])
                (let-exp (map 1st var-pairs)
                         (map parse-exp (map 2nd var-pairs))
                         (map parse-exp bodies))))]
         [(let*)
          (let ([var-pairs (2nd expr)]
                    [bodies (cddr expr)])
                (let*-exp (map 1st var-pairs)
                         (map parse-exp (map 2nd var-pairs))
                         (map parse-exp bodies)))]
         [(letrec)
          (let ([var-pairs (2nd expr)]
                    [bodies (cddr expr)])
                (letrec-exp (map 1st var-pairs)
                         (map parse-exp (map 2nd var-pairs))
                         (map parse-exp bodies)))]
         [(lambda)
          (if (lambda? expr)
              (lambda-exp (2nd expr) (map parse-exp (cddr expr)))
              (parse-err expr))]
         [(if)
           (if-exp
          (parse-exp (2nd expr))
          (parse-exp (3rd expr))
          (parse-exp (4th expr)))]
         [(set!)
          (set-exp (2nd expr) (3rd expr))]
         [else (app-exp (parse-exp (1st expr))
                        (map parse-exp (cdr expr)))])]
      [else (parse-err expr)]))
          
      #| [(eqv? (1st expr) 'lambda)
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
      |#

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Pick your favorite representation based on the lecture

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond ([(null? los) #f]
             [(eq? sym (car los)) pos]
             [else (loop (cdr los) (add1 pos))])))))
                        

(define apply-env
  (lambda (env id)
    (cond [(equal? id '+) (prim-proc '+)]
          [(equal? id '-) (prim-proc '-)]
          [(equal? id '*) (prim-proc '*)]
          [(equal? id '/) (prim-proc '/)]
          [(equal? id 'add1) (prim-proc 'add1)]
          [(equal? id 'sub1) (prim-proc 'sub1)]
          [(equal? id 'cons) (prim-proc 'cons)]
          [(equal? id '=) (prim-proc '=)]
          [(equal? id '>=) (prim-proc '>=)]
          [(equal? id 'car) (prim-proc 'car)]
          [(equal? id 'cdr) (prim-proc 'cdr)]
          [(equal? id 'list) (prim-proc 'list)]
          [else (error "this is not a real environment implementation")])))

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

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp (empty-env) form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (data) (if (quoted? data) (2nd data) data)]
      [var-exp (id)
               (apply-env env id)]
      [lambda-exp (vars bodies) (closure-proc vars bodies env)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-rands env rands)])
                 (apply-proc proc-value args))]
      [if-exp (test-exp then-exp else-exp)
              (if (eval-exp env test-exp) (eval-exp env then-exp) (eval-exp env else-exp))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (env rands)
    (map eval-exp env rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [closure-proc (vars bodies env) (map eval-exp env bodies)])))
      ;;[else (error 'apply-proc
                  ;; "Attempt to apply bad procedure: ~s" 
                  ;; proc-value)])))



(define init-env         ; you'll want to have a global environment with the prim procs and maybe other stuff
  '())

(define empty-env (lambda () (empty-env-record)))

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (first args) 1)]
      [(sub1) (- (first args) 1)]
      [(cons) (cons (first args) (second args))]
      [(=) (= (first args) (second args))]
      [(>=) (>= (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) (apply list args)]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

;(trace apply-prim-proc)

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