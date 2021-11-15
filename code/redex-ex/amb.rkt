#lang racket

;; vim: lw+=define-language,define-extended-language,define-judgment-form,define-metafunction

(provide (all-defined-out)
         (all-from-out redex))

(require redex)

(define-language L
  [e ;;=
    (e e) ; app
    (λ (x t) e) ; abs
    x ; var
    (amb e ... : t) ; amb
    number
    (+ e ...)
    (if0 e e e)
    (fix e)]
  [t ;;=
    (→ t t) ;; function type
    num]
  [x variable-not-otherwise-mentioned])

;; (redex-match L ((λ _ e_body) _) `((λ (x num) (+ x 1)) 17))
;; (redex-match L (→ _ t_range) `(→ num (→ num num)))
;; (redex-match L (_ ... e_1 e_2 _ ...) `(1 2 3 4))
;; not quite odd-lengths (works on evens, too)
;; (redex-match L (_ ..._1 e_left _ ... e_right _ ..._1) `(1 2 3 4 5))

(define-extended-language L+Γ L
  [Γ ;;=
    ε ; empty
    (x : t Γ) ; extended
    ])

(define-judgment-form
  L+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)

  [(types Γ e_1 (→ t_1 t_2))
   (types Γ e_2 t_1)
   ---
   (types Γ (e_1 e_2) t_2)]

 [(types (x : t_1 Γ) e t_2)
   ---
   (types Γ (λ (x t_1) e) (→ t_1 t_2))]

  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ---
   (types Γ (fix e) (→ t_1 t_2))]

  [---
   (types (x : t Γ) x t)]

  [(types Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ---
   (types (x_2 : t_2 Γ) x_1 t_1)]

  [(types Γ e num) ...
   ---
   (types Γ (+ e ...) num)]

  [---
   (types Γ number num)]

  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   ---
   (types Γ (if0 e_1 e_2 e_3) t)]

  [(types Γ e t) ...
   ---
   (types Γ (amb e ... : t) t)])

(define-metafunction L+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

;; (judgment-holds (types ε ((λ (x num) (amb x 1)) (+ 1 2)) t) t)
;; fails without definition for different
;; (judgment-holds (types (x : num (y : num ε)) y t) t)

;; ambiguous without different side-condition
;; (judgment-holds (types (x : num (x : (→ num num) ε)) x t) t)
