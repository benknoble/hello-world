#lang racket

(require (only-in racket/base [define def]))

(require syntax/parse/define)

(define-syntax-parser define
  [(_ head e:expr #:where body:expr ...) #'(def head (begin body ... e))]
  [(_ head . body) #'(def head . body)])

(define (foo x)
  (complex x)

  #:where

  (define (complex y)
    (something-complicated)
    (add1 x))
  (define (something-complicated)
    (void)))

(module+ main
  (foo 123))
