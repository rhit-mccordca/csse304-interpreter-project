#lang racket

(require "../chez-init.rkt" racket/trace)
(provide parse-exp unparse-exp)

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define-datatype expression expression?
  [var-exp ;;variable expression
   (id symbol?)]
  [var-exps
   (ids list?)]
  [lit-exp ;;literal expression
   (data number?)]
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
  [vec-exp
   (vec vector?)]
  [let-exp
   (vars expression?)
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
      [(number? expr) (lit-exp expr)]
      [(vector? expr) (vec-exp expr)]
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


(define (unparse-exp expr)
    (cases expression expr
      [var-exp (id) id]
      [var-exps (ids) (map (lambda (exp) (unparse-exp exp)) ids)]
      [val-exp (id value) (list (unparse-exp id) (unparse-exp value))]
      [lit-exp (data) data]
      [vec-exp (vec) vec]
      [app-exp (rator rand) (cons (unparse-exp rator)
                                  (map (lambda (exp) (unparse-exp exp)) rand))]
      [lambda-exp (id body) (cons 'lambda (cons (unparse-exp  id) (map (lambda (exp) (unparse-exp exp)) body)))]
      [let-exp (vars body) (cons 'let (cons (unparse-exp vars) (map (lambda (exp) (unparse-exp exp)) body)))]
      [let*-exp (vars body) (cons 'let* (cons (unparse-exp vars) (map (lambda (exp) (unparse-exp exp)) body)))]
      [letrec-exp (vars body) (cons 'letrec (cons (unparse-exp vars) (map (lambda (exp) (unparse-exp exp)) body)))]
      [if-exp (bool if-true if-false) (cons 'if (cons (unparse-exp bool) (cons (unparse-exp if-true) (cons (unparse-exp if-false) '()))))]
      [else (unparse-err expr)]))

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

(define lit-exp?
  (lambda (x)
    (cases expression x
      [lit-exp (data) #t]
      [else #f])))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))