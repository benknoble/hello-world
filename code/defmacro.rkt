#lang racket

(require (for-syntax syntax/parse racket))

(module+ test
  (require rackunit))

(define-syntax defmacro
  (syntax-parser
    [(_ (name:id param:id ...) body:expr ...+)
     #'(define-syntax (name stx)
         (syntax-parse stx
           [(_ param ...)
            (datum->syntax stx
                           (let ([param (syntax->datum #'param)]
                                 ...)
                             body ...)
                           stx)]))]
    [(_ (name:id param:id ... . varargs:id) body:expr ...+)
     #'(define-syntax (name stx)
         (syntax-parse stx
           [(_ param ... . varargs)
            (datum->syntax stx
                           (let ([param (syntax->datum #'param)]
                                 ...
                                 [varargs (syntax->datum #'varargs)])
                             body ...)
                           stx)]))]))

(defmacro (nif num-expr neg-expr z-expr pos-expr)
  (let ([num-sym (gensym)])
    `(let ([,num-sym ,num-expr])
       (cond
         [(negative? ,num-sym) ,neg-expr]
         [(zero? ,num-sym) ,z-expr]
         [(positive? ,num-sym) ,pos-expr]))))

;; (defmacro (nif num-expr neg-expr z-expr pos-expr)
;;   `(let ([num ,num-expr])
;;      (cond
;;        [(negative? num) ,neg-expr]
;;        [(zero? num) ,z-expr]
;;        [(positive? num) ,pos-expr])))

(module+ test
  (test-true "nif works"
             (andmap
               (λ (n)
                 (equal? (nif n 'n 'z 'p)
                         (cond
                           [(negative? n) 'n]
                           [(zero? n) 'z]
                           [(positive? n) 'p])))
               (range -10 11))))

(defmacro (a-> e . exprs)
  (if (empty? exprs)
    e
    `(let ([that ,e])
       (a-> ,(first exprs)
            ,@(rest exprs)))))

(module+ test
  (test-true "a-> works"
             (andmap
               (λ (n)
                 (equal? (a-> n
                              (add1 that)
                              (if (positive? that)
                                (/ that 2)
                                (- that))
                              (sub1 that))
                         (sub1 (if (positive? (add1 n))
                                 (/ (add1 n) 2)
                                 (- (add1 n))))))
               (range -10 11))))
