#lang racket

(provide (all-defined-out))

;; (define (Y f)
;;   (let ([A (lambda (x) (f (x x)))])
;;    (A A)))

(define (Z f)
  (let ([A (lambda (x) (f (lambda (v) ((x x) v))))])
   (A A)))

(define czero (lambda (f) (lambda (x) x)))
(define cone (lambda (f) (lambda (x) (f x))))

(define csucc (lambda (n) (lambda (f) (lambda (x) (f ((n f) x))))))
(define cplus (lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x)))))))
(define cpred (lambda (n) (lambda (f) (lambda (x) (((n (lambda (g) (lambda (h) (h (g f))))) (lambda (u) x)) (lambda (u) u))))))
(define cmult (lambda (m) (lambda (n) (lambda (f) (m (n f))))))

(define c-to-nat
  (lambda (n)
    ((n add1) 0)))

;; just for me
(define (nat-to-c n)
  (if (zero? n)
    czero
    (csucc (nat-to-c (sub1 n)))))

(andmap (λ (i) (= (c-to-nat (nat-to-c i)) i))
        (range 100))
(andmap (λ (i) (= (c-to-nat (csucc (nat-to-c i))) (add1 i)))
        (range 100))
(andmap (λ (i) (= (c-to-nat ((cplus (nat-to-c i)) (nat-to-c i))) (+ i i)))
        (range 100))
(andmap (λ (i) (= (c-to-nat (cpred (nat-to-c i))) (if (zero? i) i (sub1 i))))
        (range 100))
(andmap (λ (i) (= (c-to-nat ((cmult (nat-to-c i)) (nat-to-c i))) (* i i)))
        (range 100))

(define ctrue (lambda (a) (lambda (b) a)))
(define cfalse (lambda (a) (lambda (b) b)))

(define c-to-bool
  (lambda (b)
    ((b (= 1 1)) (= 0 1))))

;; just for me
(define (bool-to-c b)
  (if b ctrue cfalse))

(andmap (λ (b) (equal? (c-to-bool (bool-to-c b)) b))
        '(#t #f))

(define czero? (lambda (n) ((n (lambda (x) cfalse)) ctrue)))

(andmap (λ (i) (equal? (zero? i) (c-to-bool (czero? (nat-to-c i)))))
        (range 100))

(define cif (lambda (p) (lambda (a) (lambda (b) ((p a) b)))))

(define !-prime
  (lambda (f)
    (lambda (n)
      ((((cif (czero? n))
         (lambda (x) cone))
        (lambda (x) ((cmult n) (f (cpred n)))))
       ;; this last just forces the thunk returned by cif
       ;; eta-expansion required because otherwise all arguments are fully
       ;; evaluated
       czero))))

(define (! n)
  (if (zero? n)
    1
    (apply * (map add1 (range n)))))

(andmap (λ (i) (= (! i) (c-to-nat ((Z !-prime) (nat-to-c i)))))
        (range 10))
