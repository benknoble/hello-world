#lang racket

(provide (all-defined-out))

(define (reader-modules lang)
  `((submod ,lang reader)
    ,(string->symbol (~a lang "/lang/reader"))))

(define readers '(read read-syntax))

(define (get-reader lang)
  (for*/or ([mod (in-list (reader-modules lang))]
            [reader (in-list readers)])
    (with-handlers ([exn:fail? (const #f)])
      (dynamic-require mod reader (const #f)))))

(define (arbitrary-read lang port)
  (define reader (get-reader lang))
  (define arity (procedure-arity reader))
  (define stx
    (case arity
      [(1) (reader port)]
      [(2) (reader (object-name port) port)]
      [(5) (reader port #f #f #f #f)]
      [(6) (reader (object-name port) port #f #f #f #f)]))
  (define mod
    (second
      (if (syntax? stx)
        (syntax->datum stx)
        stx)))
  (values stx mod))

(define (run lang port)
  (define-values (stx mod) (arbitrary-read lang port))
  (eval stx)
  (dynamic-require `',mod #f)
  (with-handlers ([exn:fail? (const #f)])
    (dynamic-require `(submod ',mod main) #f)))
