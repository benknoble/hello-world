#lang racket

(require syntax/parse/define
         (only-in racket/base [define def])
         (for-syntax racket/syntax)
         rackunit)

(define-syntax define
  (syntax-parser
    [(_ {~or {~seq t:keyword head}
             {~seq head t:keyword}}
        . body)
     #:with transformer (format-id #'t "~a" (syntax->datum #'t))
     (syntax/loc this-syntax
       (transformer head . body))]
    [(_ head . body)
     (syntax/loc this-syntax
       (def head . body))]))

(define (rename-transformer name:id impl:id)
  #:define-syntax-parse-rule
  (define #:define-syntax name (make-rename-transformer #'impl)))

(define (strip-define sans-define:id)
  #:define-syntax-parse-rule
  #:with name (format-id #'sans-define "define-~a" #'sans-define)
  (define #:rename-transformer sans-define name))

(define #:strip-define syntax-parse-rule)
(define #:strip-define syntax)

(define #:rename-transformer from-match match-define)

;; {{{ define-steps impl
(module steps racket
  (provide define-steps)

  (require syntax/parse/define
           (for-syntax syntax/parse/lib/function-header))

  (define step-level (make-parameter -1))
  (define (indent) (build-string (* (step-level) 3) (λ _ #\space)))

  (begin-for-syntax
    (define-splicing-syntax-class step
      #:datum-literals (step)
      (pattern {~seq step message:string {~and form:expr {~not step}} ...})))

  (define-syntax-parse-rule (define-steps header:function-header step:step ...+)
    (define header
      (parameterize ([step-level (add1 (step-level))])
        (define step-number -1)
        (begin
          (set! step-number (add1 step-number))
          (displayln (format "~a~a. ~a" (indent) step-number step.message))
          step.form ...)
        ...)))) ;; }}}

(require 'steps)
(define #:rename-transformer with-steps define-steps)
(define #:strip-define steps)

;; --------------------------------------------------

(define foo 123)
(check-equal? foo 123)

(define (bar x) (list foo x))
(check-equal? (bar 456) (list 123 456))

(define (baz x)
  #:syntax-parse-rule
  (bar x))
(check-equal? (baz 456) (list 123 456))

(define #:from-match `(,a ,b, c) (list 1 2 3))
(check-equal? (list a b c) (list 1 2 3))

(define #:rename-transformer from-values define-values)
;; don't want to redefine values
;; suggests a change: transform #:values into values-define-transformer or
;; similar, so that we can use #:values, #:match, etc., without issue.
;; test for binding? preferred order?
;; (define #:strip-define values)

(define #:from-values (x y z) (values 1 2 3))
(check-equal? (list x y z) (list 1 2 3))

;; ??
(check-equal? (define #:list 1 2 3) (list 1 2 3))

(define (qux bar)
  #:steps
  step "Setup"
  (define a 1)
  (define b 2)
  step "Make a list"
  (list a b bar))

(define #:with-steps (zam zoink)
  step "My variables"
  (define c 3)
  step "Make a list with sublists"
  (list (qux c) zoink))


(check-equal? (with-output-to-string (thunk (check-equal? (qux 3) '(1 2 3))))
              "0. Setup\n1. Make a list\n")

(check-equal? (with-output-to-string (thunk (check-equal? (zam 3) '((1 2 3) 3))))
              #<<EOS
0. My variables
1. Make a list with sublists
   0. Setup
   1. Make a list

EOS
                )
