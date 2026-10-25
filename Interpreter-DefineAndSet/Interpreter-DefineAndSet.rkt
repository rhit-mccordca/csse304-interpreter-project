#lang racket

(require "../chez-init.rkt" racket/trace)
(provide eval-one-exp reset-global-env y2 advanced-letrec)

;-------------------+
; General Helpers   |
;-------------------+

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;-------------------+
; Datatype Helpers  |
;-------------------+

(define scheme-value?
  (lambda (x) #t))

(define (quoted? expr)
  (and (list? expr)
       (= 2 (length expr))
       (eqv? 'quote (car expr))))

(define (literal? expr)
  (or (number? expr)
      (string? expr)
      (boolean? expr)
      (vector? expr)
      (quoted? expr)
      (void? expr)))

(define prim-procs
  '(+ - * / add1 sub1 cons < > >= = car cdr list zero? null? procedure? assq eq? equal? eqv? atom? length list->vector not
                        list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? vector-set! display newline
                        caar cadr cadar map apply union member product quotient list-tail append))

(define (prim-proc? sym)
  (ormap (lambda (proc) (eqv? sym proc)) prim-procs))

;-------------------+
;    Datatype       |
;    Definitions    |
;-------------------+

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
  [else-exp
   (bodies (list-of? expression?))]
  [one-if-exp
   (test-exp expression?)
   (then-exp expression?)]
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
   (names (list-of? symbol?))
   (exps (list-of? expression?))
   (bodies (list-of? expression?))]
  [and-exp
   (exprs (list-of? scheme-value?))]
  [or-exp
   (exprs (list-of? scheme-value?))]
  [set-exp
   (id symbol?)
   (value expression?)]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  [cond-exp
   (test-exps (list-of? expression?))
   (body-exps (list-of? expression?))]
  [begin-exp
    (bodies (lambda (x)
              (or ((list-of? expression?) x) (null? x))))])

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure-proc
   (vars (lambda (x)
           (or (symbol? x) ((list-of? symbol?) x))))
   (bodies (list-of? expression?))
   (env environment?)])

;-------------------+
; Parser Helpers    |
;-------------------+

(define (lambda? expr)
  (let ([vars (2nd expr)][bodies (cddr expr)])
    (and (or (empty? vars) (symbol? vars) ((list-of? symbol?) vars))
         (list-of? scheme-value?))))

(define (app? expr)
  (and (pair? expr)
       (list? expr)))

(define (if? expr)
  (= (length expr) 4))

(define (one-if? expr)
  (= (length expr) 3))

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

(define (and? expr)
  (and (>= (length expr) 1)
       (list? (cdr expr))))

(define (or? expr)
  (and (>= (length expr) 1)
       (list? (cdr expr))))

(define (union s1 s2)
  (cond [(null? s1) s2]
        [(member (car s1) s2) (union (cdr s1) s2)]
        [else (cons (car s1) (union (cdr s1) s2))]))

(define (product expr)
  (apply * (map (lambda (x) x) expr)))

;-------------------+
;   Error Helpers   |
;-------------------+
   
(define parse-err
  (lambda (expr)
    (error 'parse-exp "parse-error: ~s" expr)))

(define env-err
  (lambda (env)
    (error 'apply-global-env "this is not a real environment implementation: ~s" env)))

(define apply-proc-err
  (lambda (proc)
    (error 'apply-proc "Attempt to apply bad procedure: ~s" proc)))

(define global-env-err
  (lambda (sym)
    (error 'global-env "Not defined in the global environment: ~s" sym)))

;-------------------+
;     Parser        |
;-------------------+

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
        (let ([exp-pairs (2nd expr)]
              [bodies (cddr expr)])
          (letrec-exp (map 1st exp-pairs)
                      (map parse-exp (map 2nd exp-pairs))
                      (map parse-exp bodies)))]
       [(lambda)
        (if (lambda? expr)
            (lambda-exp (2nd expr)
                        (map parse-exp (cddr expr)))
            (parse-err expr))]
       [(begin)
        (if (empty? (cdr expr))
            (lit-exp (void))
            (begin-exp (map parse-exp (cdr expr))))]
       [(cond)
        (cond-exp (map (lambda (exp) (if (eq? (car exp) 'else)
                                         (lit-exp #t)
                                         (parse-exp (car exp))))
                       (cdr expr))
                  (map (lambda (exp) (begin-exp (map parse-exp (cdr exp)))) (cdr expr)))]
       [(and)
        (if (and? expr)
            (and-exp (map parse-exp (cdr expr)))
            (parse-err expr))]
       [(or)
        (if (or? expr)
            (or-exp (map parse-exp (cdr expr)))
            (parse-err expr))]
       [(if)
        (cond [(if? expr)
               (if-exp
                (parse-exp (2nd expr))
                (parse-exp (3rd expr))
                (parse-exp (4th expr)))]
              [(one-if? expr)
               (one-if-exp
                (parse-exp (2nd expr))
                (parse-exp (3rd expr)))]
              [else (parse-err expr)])]
       [(set!)
        (set-exp (2nd expr) (3rd expr))]
       [else (app-exp (parse-exp (1st expr))
                      (map parse-exp (cdr expr)))])]
    [else (parse-err expr)]))
      
;-------------------+
;   Environments    |
;-------------------+

;; Environment Datatype Declarations

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms vector?)
   (vals vector?)
   (env environment?)])

;; Environment Initializations

(define global-env
  (extend-env
   (list->vector prim-procs)
   (list->vector (map (lambda (x) (prim-proc x)) prim-procs))
   (empty-env)))
  
(define make-init-env
  (lambda () 
    (extend-env
     (list->vector prim-procs)
     (list->vector (map (lambda (x) (prim-proc x)) prim-procs))
     (empty-env))))

(define empty-env
  (lambda () (empty-env-record)))

(define reset-global-env
  (lambda () (set! global-env (make-init-env))))

;; Environment Helpers

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))

;; Exvironment Applications

(define apply-global-env
  (lambda (sym)
    (cases environment global-env
      [extended-env-record (syms vals env)
                           (let ([pos (vector-member sym syms)])
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (global-env-err sym)))]
      [else (global-env-err sym)])))


(define apply-env
  (lambda (env sym)
    (cases environment env
      [empty-env-record ()
                        (apply-global-env sym)]
      [extended-env-record (syms vals env)
                           (let ([pos (vector-member sym syms)])
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (apply-env env sym)))])))

(define set-ref
  (lambda (ref val)
    ))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record (list->vector syms)
                         (if (list? vals)
                             (if (empty? vals)
                             (make-vector (length syms))
                             (list->vector vals))
                             (vector vals))
                         env)))

(define set-env-vals
  (lambda (env clos)
    (cases environment env
      [empty-env-record ()
                        (error 'set-env-vals "Cannot set values in an empty environment")]
      [extended-env-record (syms vals env)
                           (vector-copy! vals 0 (list->vector clos))])))

;-----------------------+
;  Syntax Expansion     |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [var-exp (symbol) exp]
      [lit-exp (literal) exp]
      [and-exp (exprs)
               (cond [(null? exprs) (lit-exp #t)]
                     [(null? (cdr exprs)) (syntax-expand (car exprs))]
                     [else (if-exp (syntax-expand (car exprs))
                                   (syntax-expand (and-exp (cdr exprs)))
                                   (lit-exp #f))])]
      [or-exp (exprs)
               (cond [(null? exprs) (lit-exp #f)]
                     [(null? (cdr exprs)) (syntax-expand (car exprs))]
                     [else (if-exp (syntax-expand (car exprs))
                                   (syntax-expand (car exprs))
                                   (syntax-expand (or-exp (cdr exprs))))])]
      [lambda-exp (vars bodies)
                  (lambda-exp vars
                              (map syntax-expand bodies))]
      [let-exp (vars var-exps bodies)
               (app-exp (lambda-exp vars
                                    (map syntax-expand bodies))
                        (map syntax-expand var-exps))]
      [named-let-exp (name vars var-exps bodies)
                     (app-exp (letrec-exp (list name)
                                          (list (lambda-exp vars
                                                   (map syntax-expand bodies)))
                                          (list (var-exp name)))
                                 (map syntax-expand var-exps))]
      [let*-exp (vars var-exps bodies)
                (if (<= (length vars) 1)
                    (syntax-expand (let-exp vars var-exps bodies))
                    (syntax-expand (let-exp (list (1st vars))
                                            (list (1st var-exps))
                                            (list (let*-exp (cdr vars)
                                                            (cdr var-exps)
                                                            bodies)))))]
      [letrec-exp (names exps bodies)
                  (letrec-exp names
                              (map syntax-expand exps)
                              (map syntax-expand bodies))]
      [app-exp (rator rands)
               (app-exp (syntax-expand rator)
                        (map syntax-expand rands))]
      [if-exp (test-exp then-exp else-exp)
              (if-exp (syntax-expand test-exp)
                      (syntax-expand then-exp)
                      (syntax-expand else-exp))]
      [one-if-exp (test-exp then-exp)
                  (one-if-exp (syntax-expand test-exp)
                              (syntax-expand then-exp))]
      [begin-exp (bodies)
                 (app-exp (syntax-expand (lambda-exp '() bodies)) '())]
      [cond-exp (test-exps body-exps)
                (cond [(null? test-exps) (lit-exp (void))]
                      [(null? (cdr test-exps)) (syntax-expand (car body-exps))]
                      [else (if-exp (syntax-expand (car test-exps))
                            (syntax-expand (car body-exps))
                            (syntax-expand (cond-exp (cdr test-exps)
                                                     (cdr body-exps))))])]
      [set-exp (id value)
               (set-exp (syntax-expand id)
                        (syntax-expand value))]
      [else exp])))

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.

;-------------------+
;    Procedure      |
;    Applications   |
;-------------------+

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure-proc (vars bodies env)
                    (if (symbol? vars)
                        (let ([new-env (extend-env (list vars) (list args) env)])
                          (last (map (lambda (body) (eval-exp new-env body)) bodies)))
                        (let ([new-env (extend-env vars args env)])
                          (last (map (lambda (body) (eval-exp new-env body)) bodies))))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))
;(trace extend-env)


(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(not) (apply not args)]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(list) (apply list args)]
      [(zero?) (zero? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(null?) (null? (1st args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(atom?) (apply (not (pair?)) args)]
      [(length) (apply length args)]
      [(list->vector) (apply list->vector args)]
      [(list?) (apply list? args)]
      [(pair?) (apply pair? args)]
      [(procedure?) (if (and (list? args) (= (length args) 1)) (proc-val? (1st args)) (proc-val? args))]
      [(vector->list) (apply vector->list args)]
      [(vector) (apply vector args)]
      [(make-vector) (make-vector (1st args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (apply vector? args)]
      [(number?) (apply number? args)]
      [(symbol?) (apply symbol? args)]
      [(vector-set!) (vector-set! (1st args) (2nd args) (caddr args))]
      [(display) (display (1st args))]
      [(newline) (newline)]
      [(map) (map (lambda (elem) (apply-proc (1st args) elem)) (2nd args))]
      [(apply) (apply-proc (1st args) (2nd args))]
      [(and) (and args)]
      [(union) (union (1st args) (2nd args))]
      [(member) (apply member args)]
      [(product) (apply product args)]
      [(quotient) (quotient (1st args) (2nd args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(append) (apply append args)]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

;-------------------+
;    Interpreter    |
;-------------------+

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (data) (if (quoted? data) (2nd data) data)]
      [var-exp (id)
               (apply-env env id)]
      [lambda-exp (vars bodies) (closure-proc vars bodies env)]
      [letrec-exp (names exps bodies)
                  (let* ([new-env (extend-env names '() env)]
                         [clos-exps (map (lambda (exp) (eval-exp new-env exp)) exps)])
                    (set-env-vals new-env clos-exps)
                    (last (map (lambda (body) (eval-exp new-env body)) bodies)))]
                    ;(eval-exp (app-exp (lambda-exp names bodies) clos-exps)))
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-rands env rands)])
                 (apply-proc proc-value args))]
      [if-exp (test-exp then-exp else-exp)
              (if (eval-exp env test-exp) (eval-exp env then-exp) (eval-exp env else-exp))]
      [one-if-exp (test-exp then-exp)
                  (when (eval-exp env test-exp) (eval-exp env then-exp))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

;-------------------+
; Macro Interpreter |
;-------------------+

(provide add-macro-interpreter)
(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
  (lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote

;-------------------+
;    Evaluation     |
;    Procedures     |
;-------------------+

(define top-level-eval
  (lambda (form)
    (eval-exp (empty-env) form)))

(define eval-rands
  (lambda (env rands)
    (map (lambda (rand) (eval-exp env rand)) rands)))

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

;-------------------+
;  Read-Eval-Print  |
;-------------------+

(define rep
  (lambda ()
    (display "--> ")
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      (pretty-print answer) (newline)
      (rep))))

;-------------------+
; Trace Statements  |
;-------------------+

;(trace parse-exp)
;(trace syntax-expand)
;(trace eval-exp)
;(trace set-env-vals)

;-------------------+
; Y2 additions      |
;-------------------+

(define y2
  (lambda (which f1 f2)
    (error "nyi")))

(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body)...) letrec-body)
     #'(error "nyi")]))