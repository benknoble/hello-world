#lang racket

(module+ test (require rackunit))

;; models
(struct km (root vars children) #:transparent)

;; formulas
(struct conj (left right) #:transparent)
(struct disj (left right) #:transparent)
(struct impl (hyp conc) #:transparent)
(struct bot () #:transparent)
(define (not x) (impl x (bot)))

(define (descendants-contain? v k)
  (and (set-member? (km-vars k) v)
       (andmap (curry descendants-contain? v)
               (km-children k))))

(define/match (valid? k)
  [((km _ vars children))
   (and (for*/and ([v (in-set vars)]
                   [c (in-list children)])
          (descendants-contain? v c))
        (andmap valid? children))])

(module+ test
  (check-true
    (valid?
      (km 'r (set 'A)
          (list (km 's (set 'A) empty)
                (km 't (set 'A 'B) empty)))))
  (check-true
    (valid?
      (km 'r (set)
          (list (km 's (set 'A) empty))))))

(define (descendants-imply? p q k)
  (and (if (forced-at? k p) (forced-at? k q) #t)
       (andmap (curry descendants-imply? p q)
               (km-children k))))

(define (forced-at? k f)
  ;; #:when (valid? k)
  (match-define (km root vars children) k)
  (match f
    [(? symbol? x) (set-member? vars x)]
    [(bot) #f]
    [(disj p q) (or (forced-at? k p)
                    (forced-at? k q))]
    [(conj p q) (and (forced-at? k p)
                     (forced-at? k q))]
    [(impl p q)
     (descendants-imply? p q k)]))

(module+ test
  (let ([k (km 'r (set 'A)
               (list (km 's (set 'A) empty)
                     (km 't (set 'A 'B) empty)))])
    (check-true (forced-at? k 'A))
    (check-true (forced-at? k (disj 'A 'B)))
    (check-false (forced-at? k (impl 'A 'B))))
  (check-true
    (forced-at?
      (km 'r (set) empty)
      (impl 'A 'B)))
  (check-true
    (forced-at?
      (km 'r (set 'B)
          (list (km 's (set 'B) empty)
                (km 't (set 'A 'B) empty)))
      (impl 'A 'B)))

  (check-false
    (forced-at?
      (km 'r (set)
          (list (km 's (set 'A) empty)))
      (disj 'A (impl 'A (bot))))))

;; exercises

(module+ test

  ;; 1. ¬¬A → A
  ;; equivalent to ((A → ⊥) → ⊥) → A

  ;; need descendant which forces ((A → ⊥) → ⊥) but not A
  ;; thus we need a descendant which forces (A → ⊥) but not ⊥ and not A
  ;; thus we need a descendant which forces A but not ⊥ nor A?

  ;; or,
  ;; need descendant which forces ¬¬A but not A.
  ;; ¬¬A is forced exactly when ¬A is not forced in any descendant
  ;; so tree must have a descendant which:
  ;; - does not force A
  ;; - forces ¬¬A by not ever forcing ¬A
  ;; Now, ¬A is forced exactly when A is not forced in any descendant. So A
  ;; must be forced in a descendant to have ¬¬A.

  ;; r - s (A)
  ;; 1. s forces A.
  ;; 2. s does not force ¬A (because s does not force ⊥)
  ;; 3. r forces ¬¬A, since ¬P is forced if P is not forced in any descendants;
  ;;    substitute for P the formula ¬A.
  ;; 4. r does not force A.
  ;; 5. then r forces ¬¬A but not A, so r does not force ¬¬A → A.

  ;; same model as LEM, because LEM ⇔ 2neg elim?
  (define one
    (km 'r (set)
        (list (km 's (set 'A) empty))))

  (check-true (valid? one))
  (check-false (forced-at? one (impl (not (not 'A))
                                     'A)))

  ;; 2. ¬(A ∧ B) → ¬A ∨ ¬B

  ;; once again, need a tree with:
  ;; - a descendant that does force ¬(A ∧ B)
  ;; - a descendant that does NOT force ¬A ∨ ¬B,

  ;; To force ¬(A ∧ B), I must NOT force (A ∧ B) in any descendant worlds by not
  ;; forcing at least one of A or B.
  ;; To NOT force ¬A ∨ ¬B, I have to NOT force both disjuncts, which requires
  ;; descendants focring both A and B (to NOT force ¬A, I must have a descendant
  ;; forcing A).

  ;; r - s (A)
  ;;  \_ t (B)
  ;; 1. s forces A.
  ;; 2. s does not force B.
  ;; 3. s does not force A ∧ B.
  ;; 4. r forces ¬(A ∧ B) by above and symmetry with t.
  ;; 5. s does not force ¬A (est.)
  ;; 6. t does not force ¬B (est.)
  ;; 7. r does not force ¬A ∨ ¬B
  ;; 8. then r does not force the implication, since it forces the hypothesis
  ;;    (4) but not the conclusion (7).

  (define two
    (km 'r (set)
        (list (km 's (set 'A) empty)
              (km 't (set 'B) empty))))

  (check-true (valid? one))
  (check-false (forced-at? two (impl (not (conj 'A 'B))
                                     (disj (not 'A) (not 'B)))))

  ;; 3. ((A → B) → A) → A

  ;; r must force (A → B) → A and not force A
  ;; to force (A → B) → A, in all descdendant words forcing A → B we must also
  ;; force A.
  ;; a descendant world forcing A → B must have, in all descendants forcing A,
  ;; also B.
  ;; but remember that r is its own descendant!

  ;; r - s (A B)
  ;;  \_ t (A)
  ;; 1. s forces A → B, and also (A → B) → A.
  ;; 2. r does not force A → B, since we have a descendant forcing A but not B.
  ;; 3. therefore r forces (A → B) → A, since whenever a descendant does force
  ;;    the hypothesis it forces the conclusion (1). This is key: r blank must
  ;;    be made to not force the hypothesis, or it cannot force the implication,
  ;;    since it must not force the conclusion by construction.
  ;; 4. r does not force A.

  (define three (km 'r (set)
                    (list (km 's (set 'A 'B) empty)
                          (km 't (set 'A) empty))))

  (check-true (valid? three))
  (check-false (forced-at? three (impl (impl (impl 'A 'B) 'A) 'A)))

  ;; 4. (A → B) ∨ (B → A)

  ;; r must not force either term
  ;; thus r must force A and not B, and r must force B and not A…

  ;; r - s (A)
  ;;  \_ t (B)
  ;; 1. s does not force A → B (idem. t)
  ;; 2. r does not force A → B.
  ;; 3. t does not force B → A (idem. s)
  ;; 4. r does not force B → A.

  ;; an equivalence with DeMorgan?
  (define four (km 'r (set)
                   (list (km 's (set 'A) empty)
                         (km 't (set 'B) empty))))

  (check-true (valid? four))
  (check-false (forced-at? four (disj (impl 'A 'B)
                                      (impl 'B 'A)))))
