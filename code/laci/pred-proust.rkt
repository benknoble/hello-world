#lang racket

(provide (all-defined-out))

(require syntax/parse/define)

;; terms (types are now also terms!)
(struct lam (var body) #:transparent)
(struct fapp (rator rand) #:transparent)
(struct ann (expr type) #:transparent)
(struct arrow (var domain range) #:transparent)

;; sorts
(struct type () #:transparent)

(define parse-expr
  (match-lambda
    [`(,(or `λ `lambda) ,(? symbol? x) ,e) (lam x (parse-expr e))]
    [`(,(or `λ `lambda) ,(? symbol? x) ..1 ,e)
      (lam (car x) (parse-expr `(λ ,@(cdr x) ,e)))]
    [`(,(or `∀ `forall) [,(? symbol? x) : ,t] -> ,e)
      (arrow x (parse-expr t) (parse-expr e))]
    [`(,(or `∀ `forall) [,(? symbol? x) : ,t] ,(? list? rest) ..1 -> ,e)
      (arrow x (parse-expr t) (parse-expr `(∀ ,@rest -> ,e)))]
    [`(,e : ,t) (ann (parse-expr e) (parse-expr t))]
    ['type (type)]
    [`(,dom -> ,ran) (arrow '_ (parse-expr dom) (parse-expr ran))]
    [`(,dom -> ,ran -> ,rest ...)
      (arrow '_ (parse-expr dom) (parse-expr `(,ran -> ,@rest)))]
    [`(,rat ,ran) (fapp (parse-expr rat) (parse-expr ran))]
    [`(,rat ,ran ,rest ..1) (parse-expr `((,rat ,ran) ,@rest))]
    [(? symbol? (and x (not '_))) x]))

(define pp-expr
  (match-lambda
    [(? symbol? (or (app symbol->string (pregexp #px"-int-(.*?)-\\d+" (list _ x)))
                    x))
     (~a x)]
    [(lam x b) (format "(λ ~a ~a)" (pp-expr x) (pp-expr b))]
    [(fapp f x) (format "(~a ~a)" (pp-expr f) (pp-expr x))]
    [(ann e t) (format "(~a : ~a)" (pp-expr e) (pp-expr t))]
    [(type) "type"]
    [(arrow '_ dom ran) (format "(~a -> ~a)" (pp-expr dom) (pp-expr ran))]
    [(arrow var dom ran) (format "(∀ [~a : ~a] -> ~a)"
                                 var (pp-expr dom) (pp-expr ran))]))

(define (pp-context context)
  (string-append*
    (hash-map context (λ (e t) (format "~a: ~a\n" (pp-expr e) (pp-expr t))))))

;; old new -> expr -> expr
(define (subst old new)
  (match-lambda
    [(? symbol? (== old)) new]
    [(arrow '_ dom ran) (arrow '_ ((subst old new) dom) ((subst old new) ran))]
    [(arrow (and x (== old)) dom ran) (arrow x dom ran)]
    [(arrow x dom ran)
     #:when (side-cond? x (list new) #:check-binders? #t)
     (define repl (refresh x (list new ran)))
     (arrow repl
            ((subst old new) dom)
            ((subst old new) ((subst x repl) ran)))]
    [(arrow x dom ran) (arrow x ((subst old new) dom) ((subst old new) ran))]
    [(lam '_ b) (lam '_ ((subst old new) b))]
    [(lam (and x (== old)) b) (lam x b)]
    [(lam x b)
     #:when (side-cond? x (list new) #:check-binders? #f)
     (define repl (refresh x (list new b)))
     (lam repl ((subst old new) ((subst x repl) b)))]
    [(lam x b) (lam x ((subst old new) b))]
    [(fapp f x) (fapp ((subst old new) f) ((subst old new) x))]
    [(ann f x) (ann ((subst old new) f) ((subst old new) x))]
    [x x]))

(define (refresh x es)
  (if (side-cond? x es #:check-binders? #t)
    (refresh (freshen x) es)
    x))

(define (freshen x)
  ;; #px"-int-(.*?)-\\d+"
  (gensym (format "-int-~a-" x)))

(define (side-cond? x es #:check-binders? check?)
  (for/or ([e (in-list es)])
    ((sc-helper x check?) e)))

(define (sc-helper x check?)
  (match-lambda
    [(? symbol? (== x)) #t]
    [(? symbol? y) #f]
    [(arrow (== x) dom ran) #:when check? #t]
    [(arrow (== x) dom ran) #f]
    [(arrow y dom ran) (side-cond? x (list dom ran) #:check-binders? check?)]
    [(lam (== x) b) #:when check? #t]
    [(lam (== x) b) #f]
    [(lam y b) ((sc-helper x check?) b)]
    [(fapp f a) (side-cond? x (list f a) #:check-binders? check?)]
    [(ann e t) (side-cond? x (list e t) #:check-binders? check?)]
    [(type) #f]))

(define (alpha-equiv? e1 e2)
  (let loop ([e1 e1]
             [e2 e2]
             [vmap (hash)])
    (match* (e1 e2)
      [(x x) #t]
      [((? symbol? x) (? symbol? y)) (equal? y (hash-ref vmap x #f))]
      [((lam x t) (lam y u)) (loop t u (hash-set vmap x y))]
      [((fapp f x) (fapp g y)) (and (loop f g vmap)
                                    (loop x y vmap))]
      [((ann x t) (ann y u)) (and (loop x y vmap)
                                  (loop t u vmap))]
      [((arrow x t u) (arrow y v w)) (let ([vmap* (hash-set vmap x y)])
                                       (and (loop t v vmap*)
                                            (loop u w vmap*)))]
      [(_ _) #f])))

(define (reduce context)
  (match-lambda
    [(? symbol? x)
     #:when (and (not (hash-has-key? context x))
                 (hash-has-key? defs x))
     ((reduce context) (hash-ref defs x))]
    [(arrow '_ (app (reduce context) a) (app (reduce context) b))
     (arrow '_ a b)]
    [(arrow x (app (reduce context) a) b)
     (arrow x a ((reduce (hash-set context x a)) b))]
    [(lam '_ (app (reduce context) b)) (lam '_ b)]
    [(lam x b) (lam x ((reduce (hash-set context x null)) b))]
    [(fapp (app (reduce context) (lam x b))
           (app (reduce context) y))
     ((reduce context) ((subst x y) b))]
    [(fapp (app (reduce context) f)
           (app (reduce context) x))
     (fapp f x)]
    [(ann (app (reduce context) e) t) e]
    [x x]))

(define (equiv? context x y)
  (alpha-equiv? ((reduce context) x)
                ((reduce context) y)))

(define (used-in-context? context x)
  (or (hash-ref typedefs x #f)
      (for/or ([p (in-hash-values context)])
        (side-cond? x (list p) #:check-binders? #f))))

(define (refresh-with-context context x es)
  (if (or (side-cond? x es #:check-binders? #t)
          (used-in-context? context x))
    (refresh-with-context context (freshen x) es)
    x))

(define (type-check context expr t)
  (cond
    [(lam? expr)
     (type-check context t (type))
     (match* (expr ((reduce context) t))
       [((lam '_ b) (arrow '_ _ u)) (type-check context b u)]
       [((lam '_ b) (arrow x t u))
        #:when (nor (side-cond? x (list b) #:check-binders? #f)
                    (used-in-context? context x))
        (type-check (hash-set context x t) b u)]
       [((lam '_ b) (and tr (arrow x t u)))
        (define x* (refresh-with-context context x (list b tr)))
        (type-check (hash-set context x* t) b ((subst x x*) u))]
       [((lam x b) (and tr (arrow '_ t u)))
        #:when (nor (side-cond? x (list tr) #:check-binders? #f)
                    (used-in-context? context x))
        (type-check (hash-set context x t) b u)]
       [((lam x b) (and tr (arrow '_ t u)))
        (define x* (refresh-with-context context x (list b tr)))
        (type-check (hash-set context x* t) ((subst x x*) b) u)]
       [((lam x b) (arrow x t u))
        #:when (not (used-in-context? context x))
        (type-check (hash-set context x t) b u)]
       [((lam x b) (and tr (arrow y t u)))
        #:when (nor (side-cond? x (list tr) #:check-binders? #f)
                    (used-in-context? context x))
        (type-check (hash-set context x t) b ((subst y x) u))]
       [((lam x b) (and tr (arrow y t u)))
        (define x* (refresh-with-context context x (list expr tr)))
        (type-check (hash-set context x* t) ((subst x x*) b) ((subst y x*) u))])]
    [else (match expr
            [(app (curry type-synth context) type-s)
             #:when (equiv? context type-s t)
             #t])]))

(define (type-synth context expr)
  #;(when (equal? expr (fapp 'f 'p))
    (displayln (pp-context context)))
  (match expr
    [(? symbol? x) #:when (hash-has-key? context x) (hash-ref context x)]
    [(? symbol? x) #:when (hash-has-key? typedefs x) (hash-ref typedefs x)]
    [(fapp (app (compose1 (reduce context) (curry type-synth context))
                (arrow '_ t u))
           a)
     #:when (type-check context a t)
     u]
    [(fapp (app (compose1 (reduce context) (curry type-synth context))
                (arrow x t u))
           a)
     #:when (type-check context a t)
     ((subst x a) u)]
    [(ann e t) (type-check context t (type))
               (type-check context e t)
               t]
    [(arrow '_ t u) (type-check context t (type))
                    (type-check context u (type))
                    (type)]
    [(arrow x t u) (type-check context t (type))
                   (type-check (hash-set context x t) u (type))
                   (type)]
    [(type) (type)]))

;; defs

(define defs (make-hash))
(define typedefs (make-hash))

(define (clear-defs!)
  (hash-clear! defs)
  (hash-clear! typedefs))

(define (-def name expr)
  (when (hash-has-key? defs name)
    (raise-argument-error '-def "name not in defs" 1 name))
  (define e (parse-expr expr))
  (define et (type-synth (hash) e))
  (match e
    [(ann x t) (hash-set! defs name x)
               (hash-set! typedefs name t)]
    [else (hash-set! defs name e)
          (hash-set! typedefs name et)]))

(define-syntax-parse-rule (def name:id e:expr)
  (-def 'name 'e))

(define (-pp-def name)
  (when (hash-has-key? defs name)
    (format "~a~nreduced~n~a"
            (pp-expr (ann (hash-ref defs name)
                          (hash-ref typedefs name)))
            (pp-expr (ann ((reduce (hash)) (hash-ref defs name))
                          ((reduce (hash)) (hash-ref typedefs name)))))))

(define-syntax-parse-rule (pp-def name:id)
  (-pp-def 'name))

(def bool ((∀ [X : type] -> (X -> X -> X)) : type))
(def true ((λ X x y x) : bool))
(def false ((λ X x y y) : bool))
;; this is redundant!
;; since bool is ∀X.X->X->X, the type of if is essentially
;; ∀X.(∀X.X->X->X)->X->X->X
;; which is a tautology.
(def if ((λ X b t f (b X t f))
         : (∀ [X : type] -> (bool -> X -> X -> X))))
(def band ((λ x y (x bool y false)) : (bool -> bool -> bool)))

(def and ((λ P Q (∀ [C : type] -> ((P -> Q -> C) -> C)))
          : (type -> type -> type)))
(def conj ((λ P Q p q C f (f p q))
            : (∀ [P : type] [Q : type] -> (P -> Q -> (and P Q)))))
(def proj1 ((λ P Q pq (pq P (λ p q p)))
            : (∀ [P : type] [Q : type] -> ((and P Q) -> P))))
(def proj2 ((λ P Q pq (pq Q (λ p q q)))
            : (∀ [P : type] [Q : type] -> ((and P Q) -> Q))))

;; theorem!
(def and-commutes ((λ P Q pq (conj Q P (proj2 P Q pq) (proj1 P Q pq)))
                   : (∀ [P : type] [Q : type] -> ((and P Q) -> (and Q P)))))

(def nat ((∀ [X : type] -> ((X -> X) -> X -> X)) : type))
(def z ((λ X f b b) : nat))
(def s ((λ n X f b (f (n X f b))) : (nat -> nat)))
(def one ((s z) : nat))
(def two ((s one) : nat))
(def plus ((λ n m X f b (m X f (n X f b)))
           : (nat -> nat -> nat)))

(unless (equiv? (hash) (parse-expr '(plus one one)) (parse-expr 'two))
  (error 'plus "plus is wrong"))
