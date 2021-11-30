#lang racket

(require racket/gui/easy
         racket/gui/easy/operator
         syntax/parse/define
         (for-syntax racket/syntax))

(define-for-syntax (@internal stx id)
  (format-id stx "@internal-~a" id #:source stx))

(define-syntax-parse-rule (define/obsp n:id p:expr)
  #:with @internal (@internal #'n (syntax-e #'n))
  (begin
    (define/obs @internal p)
    (define/obs n (@internal . ~> . (λ (the-p) (the-p))))))

(define (internal-obsp-update! internal o f)
  (internal . <~ . (λ (the-p) (the-p (f (the-p))) the-p))
  (obs-peek o))

(define-syntax-parse-rule (obsp-update! o:id f:expr)
  #:with @internal (@internal #'o (syntax-e #'o))
  (internal-obsp-update! @internal o f))
;; don't need p~>/obsp-map because ~>/obs-map already work
(define-syntax <~p (make-rename-transformer #'obsp-update!))
(define-syntax-parse-rule (:=p o:id v:expr) (<~p o (const v)))
(define-syntax-parse-rule (λ:=p o:id f:expr) (λ (v) (:=p o (f v))))
(define-syntax-parse-rule (λ<~p o:id f:expr) (thunk (<~p o f)))

(define p (make-parameter #f))
(define/obsp @op p)

(obs-observe! @op (λ (x) (printf "op: Value: Got ~s~n" x)))

(equal? (obs-peek @op) (p))

;; bypass @op
(p 1)

;; new versions
(obsp-update! @op add1) ;; 2
(<~p @op add1) ;; 3
(:=p @op 4) ;; 4
((λ:=p @op add1) (obs-peek @op)) ;; 5
((λ<~p @op add1)) ;; 6
