#lang racket

(provide (all-defined-out))

(require qi)

;; vim: lw+=define-flow,define-switch,flow-lambda,switch-lambda,on,switch,π,λ01

;; (define (nice? str)
;;   (define (three-vowels? str)
;;     (>= (length (regexp-match* #rx"[aeiou]" str)) 3))
;;   (define (double-letter? str)
;;     (regexp-match #px"(.)\\1" str))
;;   (define (no-kapu? str)
;;     (not (regexp-match #rx"ab|cd|pq|xy" str)))
;;   (and (three-vowels? str)
;;        (double-letter? str)
;;        (no-kapu? str)))

(define-flow three-vowels?
  (~>> (regexp-match* #rx"[aeiou]")
       length
       (>= _ 3)))
(define-flow double-letter? (~>> (regexp-match #px"(.)\\1")))
(define-flow no-kapu? (~>> (regexp-match #rx"ab|cd|pq|xy") !))
(define-flow nice? (and three-vowels? double-letter? no-kapu?))
