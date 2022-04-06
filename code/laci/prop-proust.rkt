#lang racket

(provide (all-defined-out))

(require syntax/parse/define)

;; terms
(struct lam (var body) #:transparent)
(struct fapp (rator rand) #:transparent)
(struct ann (expr type) #:transparent)
(struct hole (index) #:transparent)
(struct and-intro (elim0 elim1) #:transparent)
(struct and-elim0 (prod) #:transparent)
(struct and-elim1 (prod) #:transparent)
(struct or-left (e) #:transparent)
(struct or-right (e) #:transparent)
(struct or-elim (t f g) #:transparent)
(struct ! (e) #:transparent)

;; types
(struct arrow (domain range) #:transparent)
(struct prod (left right) #:transparent)
(struct sum (left right) #:transparent)
(struct bot () #:transparent)

;; state!
(define current-expr #f)
(define goal-table (make-hash))
(define c 0)
(define (counter)
  (begin0 c (set! c (add1 c))))

(define refining (make-parameter #f #f 'refining))

(define parse-expr
  (match-lambda
    [`? (hole #f)]
    [(? symbol? x) x]
    [`(lambda ,x ,e) (parse-expr `(λ ,x ,e))]
    [`(λ ,(? symbol? x) ,e) (lam x (parse-expr e))]
    [`(,(or `and-intro `*-intro `∧-intro) ,p ,q)
      (and-intro (parse-expr p) (parse-expr q))]
    [`(,(or `and-elim0 `*-elim0 `∧-elim0) ,x) (and-elim0 (parse-expr x))]
    [`(,(or `and-elim1 `*-elim1 `∧-elim1) ,x) (and-elim1 (parse-expr x))]
    [`(,(or `or-left `+-left `∨-left) ,x) (or-left (parse-expr x))]
    [`(,(or `or-right `+-right `∨-right) ,x) (or-right (parse-expr x))]
    [`(,(or `or-elim `+-elim `∨-elim) ,t ,f ,g)
      (or-elim (parse-expr t) (parse-expr f) (parse-expr g))]
    [`(! ,e) (! (parse-expr e))]
    [`(,rat ,ran) (fapp (parse-expr rat) (parse-expr ran))]
    [`(,e : ,t) (ann (parse-expr e) (parse-type t))]
    [`(,rat ,ran ,rest ..1) (parse-expr `((,rat ,ran) ,@rest))]))

(define parse-type
  (match-lambda
    [(or `False `false `bot `⊥) (bot)]
    [(? symbol? x) x]
    [`(,dom -> ,ran) (arrow (parse-type dom) (parse-type ran))]
    [`(,dom -> ,ran -> ,rest ...)
      (arrow (parse-type dom) (parse-type `(,ran -> ,@rest)))]
    [`(,p ,(or `prod `* `∧) ,q) (prod (parse-type p) (parse-type q))]
    [`(,p ,(or `sum `+ `∨) ,q) (sum (parse-type p) (parse-type q))]
    [`(,(or `not `neg `¬) ,p) (parse-type `(,p -> False))]))

(define pp-expr
  (match-lambda
    [(? symbol? x) (~a x)]
    [(lam x b) (format "(λ ~a ~a)" x (pp-expr b))]
    [(fapp f x) (format "(~a ~a)" (pp-expr f) (pp-expr x))]
    [(ann e t) (format "(~a : ~a)" (pp-expr e) (pp-type t))]
    [(and-intro p q) (format "(and-intro ~a ~a)" (pp-expr p) (pp-expr q))]
    [(and-elim0 x) (format "(and-elim0 ~a)" (pp-expr x))]
    [(and-elim1 x) (format "(and-elim1 ~a)" (pp-expr x))]
    [(or-left x) (format "(or-left ~a)" (pp-expr x))]
    [(or-right x) (format "(or-right ~a)" (pp-expr x))]
    [(or-elim t f g) (format "(or-elim ~a ~a ~a)"
                             (pp-expr t) (pp-expr f) (pp-expr g))]
    [(! e) (format "(! ~a)" (pp-expr e))]
    [(hole n) (format "?~a" n)]))

(define pp-type
  (match-lambda
    [(? symbol? x) (~a x)]
    [(arrow p (bot)) (format "(not ~a)" (pp-type p))]
    [(arrow dom ran) (format "(~a -> ~a)" (pp-type dom) (pp-type ran))]
    [(prod p q) (format "(~a * ~a)" (pp-type p) (pp-type q))]
    [(sum p q) (format "(~a + ~a)" (pp-type p) (pp-type q))]
    [(bot) (format "False")]))

(define (pp-ctx ctx)
  (string-append*
    (hash-map ctx (λ (e t) (format "~a: ~a\n" (pp-expr e) (pp-type t))))))

(define/match (type-check ctx expr type)
  [(_ (lam x b) (arrow dom ran))
   (type-check (hash-set ctx x dom) b ran)]
  [(_ (hole n) _) (when (refining)
                    (hash-set! goal-table n (cons type ctx)))
                  #t]
  [(_ (and-intro p q) (prod P Q))
   (and (type-check ctx p P)
        (type-check ctx q Q))]
  [(_ (or-left p) (sum P _)) (type-check ctx p P)]
  [(_ (or-right q) (sum _ Q)) (type-check ctx q Q)]
  [(_ (or-elim (app (curry type-synth ctx) (sum P Q)) f g) R)
   (and (type-check ctx f (arrow P R))
        (type-check ctx g (arrow Q R)))]
  [(_ (! t) T) (type-check ctx t (bot))]
  ;; type-synth in the pattern, so needs to come later
  [(_ (app (curry type-synth ctx) type) type) #t])

(define (type-synth ctx expr)
  (match expr
    [(? symbol? x) (hash-ref ctx x)]
    [(ann e t) (type-check ctx e t)
               t]
    [(and-elim0 (app (curry type-synth ctx) (prod t _))) t]
    [(and-elim1 (app (curry type-synth ctx) (prod _ u))) u]
    [(fapp (app (curry type-synth ctx) (arrow dom ran)) x)
     #:when (type-check ctx x dom)
     ran]))

(module+ test
  (require rackunit)
  (define (check-tauto p)
    (check-not-exn (thunk (type-synth (hash) (parse-expr p)))))
  (check-tauto '((λ x (λ y x)) : (A -> (B -> A))))
  (check-tauto '((λ x (λ y x)) : (A -> B -> A)))
  (check-tauto '((λ x (λ y (y x))) : (A -> ((A -> B) -> B)))))

(define (print-task)
  (printf "~a\n" (pp-expr current-expr)))
(define print-goal
  (case-lambda
    [() (hash-for-each goal-table (λ (n _) (print-goal n)))]
    [(n) (match-define `(,type . ,ctx) (hash-ref goal-table n))
         (printf "Goal ~a has type ~a\n" n (pp-type type))
         (unless (hash-empty? ctx)
           (printf "in context\n~a" (pp-ctx ctx)))]))

(define (set-task! goal)
  (define type (parse-type goal))
  (set! current-expr (ann (hole 0) type))
  (set! goal-table (make-hash (list (cons 0 (cons type (hash))))))
  (set! c 1)
  (printf "Current task:\n")
  (print-task))

;; main interaction with prover
(define (refine n subst)
  (match-define `(,type . ,ctx) (hash-ref goal-table n))
  (define e (parse-expr subst))
  (type-check ctx e type)
  (define en (number-new-holes e))
  (parameterize ([refining #t])
    (type-check ctx en type))
  (hash-remove! goal-table n)
  (set! current-expr (replace-goal-with n en current-expr))
  (define goals (hash-count goal-table))
  (printf "Current task with ~a goal~a:\n" goals (if (= 1 goals) "" "s"))
  (print-task)
  (print-goal))

(define number-new-holes
  (match-lambda
    [(lam x b) (lam x (number-new-holes b))]
    [(fapp f x) (fapp (number-new-holes f)
                      (number-new-holes x))]
    [(ann e t) (ann (number-new-holes e) t)]
    [(and-intro p q) (and-intro (number-new-holes p)
                                (number-new-holes q))]
    [(and-elim0 x) (and-elim0 (number-new-holes x))]
    [(and-elim1 x) (and-elim1 (number-new-holes x))]
    [(or-left x) (or-left (number-new-holes x))]
    [(or-right x) (or-right (number-new-holes x))]
    [(or-elim t f g) (or-elim (number-new-holes t)
                              (number-new-holes f)
                              (number-new-holes g))]
    [(! e) (! (number-new-holes e))]
    [(hole #f) (hole (counter))]
    [x x]))

(define (replace-goal-with n repl e)
  (match e
    [(lam x b) (lam x (replace-goal-with n repl b))]
    [(fapp f x) (fapp (replace-goal-with n repl f)
                      (replace-goal-with n repl x))]
    [(ann e t) (ann (replace-goal-with n repl e) t)]
    [(and-intro p q) (and-intro (replace-goal-with n repl p)
                                (replace-goal-with n repl q))]
    [(and-elim0 x) (and-elim0 (replace-goal-with n repl x))]
    [(and-elim1 x) (and-elim1 (replace-goal-with n repl x))]
    [(or-left x) (or-left (replace-goal-with n repl x))]
    [(or-right x) (or-right (replace-goal-with n repl x))]
    [(or-elim t f g) (or-elim (replace-goal-with n repl t)
                              (replace-goal-with n repl f)
                              (replace-goal-with n repl g))]
    [(! e) (! (replace-goal-with n repl e))]
    [(hole (== n)) repl]
    [x x]))

;; proof helpers and automation

(define (-intro n v)
  (refine n `(λ ,v ?)))

(define-syntax-parse-rule (intro n:number v:id)
  (-intro n 'v))

(define (-intros n . vs)
  (refine n
          (for/fold ([e '?])
            ([var (in-list (reverse vs))])
            `(λ ,var ,e))))

(define-syntax-parse-rule (intros n:number v:id ...+)
  (-intros n 'v ...))

(define (-destruct-or n v a b)
  (refine n `(or-elim ,v (λ ,a ?) (λ ,b ?))))

(define-syntax-parse-rule (destruct-or n:number e:expr a:id b:id)
  (-destruct-or n 'e 'a 'b))

(define-syntax-parse-rule (left n:number)
  (refine n `(or-left ?)))
(define-syntax-parse-rule (right n:number)
  (refine n `(or-right ?)))

(define-syntax-parse-rule (destruct-and n:number)
  (refine n '(and-intro ? ?)))

(define-syntax-parse-rule (exfalso n:number)
  (refine n `(! ?)))

(define-syntax-parse-rule (papply n:number e:expr)
  (refine n `(,'e ?)))

(define-syntax-parse-rule (exact n:number e:expr)
  (refine n 'e))

(define (assumption n)
  (match-define `(,type . ,ctx) (hash-ref goal-table n))
  (define assumption?
    (for/first ([(term ttype) (in-hash ctx)]
                #:when (equal? type ttype))
      term))
  (when assumption?
    (refine n assumption?)))
