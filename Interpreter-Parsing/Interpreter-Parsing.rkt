#lang racket

(require "../chez-init.rkt" racket/trace)
(provide parse-exp unparse-exp)

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define-datatype expression expression?
  [var-exp ;;variable expression
   (id symbol?)]
  [lit-exp ;;literal expression
   (data number?)]
  [val-expr
   (id symbol?)
   (value expression?)]
  [lambda-exp ;;lambda expression
   (id list?)
   (body expression?)]
  [app-exp ;;application expression
   (rator expression?)
   (rand list?)]
  [if-exp ;;if expression
   (bool expression?)
   (if-true expression?)
   (if-else expression?)]
  [let-exp
   (vars expression?)]
  [let*-exp
   (vars expression?)]
  [letrec-exp
   (vars expression?)]
  [set!-exp
   (id symbol?)
   (value expression?)])

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

; Helper Functions
(define (lambda? expr)
    (and (= (length expr) 3)
         (list? (2nd expr))
         (andmap symbol? (2nd expr))))

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

(define (parse-exp expr)
    (cond
      [(empty? expr) '()]
      [(symbol? expr) (var-exp expr)]
      [(number? expr) (lit-exp expr)]
      [(eqv? (1st expr) 'lambda)
       (if (lambda? expr) (lambda-exp (2nd expr) (parse-exp (3rd expr))) (parse-err expr))]
      [(eqv? (1st expr) 'let)
       (if (let? expr) (let-exp (parse-exp (2nd expr)) (parse-exp (cdr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'let*)
       (if (let? expr) (let*-exp (parse-exp (2nd expr)) (parse-exp (cdr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'letrec)
       (if (let? expr) (letrec-exp (parse-exp (2nd expr)) (parse-exp (cdr expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'set!)
       (if (set!? expr) (set!-exp (var-exp (2nd expr)) (parse-exp (3rd expr)))
           (parse-err expr))]
      [(eqv? (1st expr) 'if)
       (if (if? expr) (if-exp
                       (parse-exp (2nd expr))
                       (parse-exp (3rd expr))
                       (parse-exp (cdr expr)))
           (parse-err expr))]
      [(app? expr) (app-exp (parse-exp (1st expr))
                            (map (lambda (expr) (parse-exp expr)) (cdr expr)))]
      [else (parse-err expr)]))


(define unparse-exp
  (lambda (exp)
    'nyi))

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