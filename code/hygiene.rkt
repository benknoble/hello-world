#lang racket

(require syntax/parse/define
         (for-syntax racket/syntax))

(begin-for-syntax
  (define (syntax-map f stx)
    (datum->syntax stx (f (syntax->datum stx)))))

(define-syntax-parse-rule (m f:keyword . e)
  #:with real-f (format-id #'f "~a" (syntax->datum #'f))
  (real-f . e))

(define-syntax-parse-rule (m-old f:keyword . e)
  #:with real-f (syntax-map (compose1 string->symbol keyword->string) #'f)
  (real-f . e))

(module+ foo
  (provide f)
  (define (f . e) (apply + e)))

(define (f . e) (apply - e))

(m #:f 1 2 3)
(m-old #:f 1 2 3)

(module+ foo
  (m #:f 1 2 3)
  (m-old #:f 1 2 3))
