#lang racket

(require "../chez-init.rkt" racket/trace)
(provide eval-one-exp)

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

(define (prim-proc? sym)
  (let ([prim-procs '(+ - * / add1 sub1 cons >= = car cdr list zero? null? procedure? assq eq? equal? atom? length list->vector not
                        list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? vector-set! display newline
                        caar cadr cadar map apply and)])
    (ormap (lambda (proc) (eqv? sym proc)) prim-procs)))

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
   (rand (list-of? expression?))]

  [begin-exp
    (bodies (list-of? expression?))])

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
         (or (literal? bodies) (symbol? bodies) ((list-of? list?) bodies) ((list-of? symbol?) bodies) ((list-of? literal?) bodies)))))

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
  
(define (begin? expr)
  (and (>= (length expr) 2)
       (list? expr)))

;-------------------+
;   Error Helpers   |
;-------------------+
   
(define parse-err
  (lambda (expr)
    (error 'parse-exp "parse-error: ~s" expr)))

(define env-err
  (lambda (env)
    (error 'apply-global-env "this is not a real environment implementation: ~s" env)))

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
        (let ([var-pairs (2nd expr)]
              [bodies (cddr expr)])
          (letrec-exp (map 1st var-pairs)
                      (map parse-exp (map 2nd var-pairs))
                      (map parse-exp bodies)))]
       [(lambda)
        (if (lambda? expr)
            (lambda-exp (2nd expr) (map parse-exp (cddr expr)))
            (parse-err expr))]
       [(begin)
        (if (begin? expr)
            (begin-exp (map parse-exp (cdr expr)))
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
          
      
;-------------------+
;   Environments    |
;-------------------+

(define scheme-value?
  (lambda (x) #t))

;; Environment Datatype Declarations

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])

;; Environment Initializations

(define init-env '())

(define empty-env
  (lambda () (empty-env-record)))

;; Environment Helpers

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))

;; Exvironment Applications

(define apply-global-env
  (lambda (env sym)
    (if (prim-proc? sym)
        (prim-proc sym)
        (env-err env))))

(define apply-env
  (lambda (env sym)
    (cases environment env
      [empty-env-record ()
                        (apply-global-env env sym)]
      [extended-env-record (syms vals env)
                           (let ([pos (list-find-position sym syms)])
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

;-----------------------+
;  Syntax Expansion     |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [var-exp (symbol) exp]
      [lit-exp (literal) exp]
      [and-exp (exps)
               (cond [(null? exps) (lit-exp #t)]
                     [(null? (cdr exps)) (syntax-expand (car exps))]
                     [else (if-exp (syntax-expand (car exps))
                                   (syntax-expand (and-exp (cdr exps)))
                                   (lit-exp #f))])])))

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
                    (let ([new-env (extend-env vars args env)])
                      (last (map (lambda (body) (eval-exp new-env body)) bodies)))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

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
      [let-exp (vars var-exps bodies)
               (let ([var-vals (map (lambda (x) (eval-exp env x)) var-exps)])
                 (let ([new-env (extend-env vars var-vals env)])
                   (last (map (lambda (body) (eval-exp new-env body)) bodies))))]
      [let*-exp (vars var-exps bodies)
                (let loop ([env env] [vars vars] [var-exps var-exps])
                  (if (empty? var-exps)
                      (last (map (lambda (body) (eval-exp env body)) bodies))
                      (let ([var-val (eval-exp env (1st var-exps))])
                        (loop (extend-env (list (1st vars)) (list var-val) env) (cdr vars) (cdr var-exps)))))]
                
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-rands env rands)])
                 (apply-proc proc-value args))]
      [if-exp (test-exp then-exp else-exp)
              (if (eval-exp env test-exp) (eval-exp env then-exp) (eval-exp env else-exp))]
      [begin-exp (bodies)
                 (last (map (lambda (body) (eval-exp env body)) bodies))]
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
    (let ([answer (top-level-eval (parse-exp (read)))])
      (pretty-print answer) (newline)
      (rep))))

