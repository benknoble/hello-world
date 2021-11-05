#lang racket/base

;; vim: lw+=%rel

(provide (all-defined-out)
         (all-from-out racklog))

(require racket/list
         racket/function
         racket/set
         racket/generator
         racket/sequence
         rackunit
         racklog)

(define %product
  (%rel (As Bs Cs A B)
    [(As Bs Cs) ;-
     (%set-of (cons A B)
              (%and (%member A As)
                    (%member B Bs))
              Cs)]))

;; spoofed from https://stackoverflow.com/a/8608389/4400820
(define %between
  (%rel (Low High Value NewLow)
    [(Low High Low)]
    [(Low High Value) ;-
     (%is NewLow (add1 Low))
     (%<= NewLow High)
     (%between NewLow High Value)]))

(define %range
  (%rel (N L NN X)
    [(N L) ;-
     (%is NN (sub1 N))
     (%bag-of X (%between 0 NN X) L)]))

(define %coords
  (%rel (N Coords ToN)
    [(N Coords) ;-
     (%range N ToN)
     (%product ToN ToN Coords)]))

(define %square
  (%rel (Xss N)
    [(Xss N) ;-
     (%is N (length Xss))
     (%andmap (λ (Xs) (%is N (length Xs))) Xss)]))

(define %empty-assoc
  (%rel ()
    [((hash))]))

(define %put-assoc
  (%rel (Key Assoc Val New)
    [(Key Assoc Val New) ;-
     (%is New (hash-set Assoc Key Val))]))

;; more general than swipl's get_assoc, since we have
;; -Key +Assoc -Val
;; +Key +Assoc ?Val
;; though not
;; -Key +Assoc +Val
(define %get-assoc
  (%rel (Key Assoc Val Keys)
    [(Key Assoc Val) ;-
     (%assoc-to-keys Assoc Keys)
     (%member Key Keys)
     (%is Val (hash-ref Assoc Key #f))]))

(define %del-assoc
  (%rel (Key Assoc Val New)
    [(Key Assoc Val New) ;-
     (%get-assoc Key Assoc Val)
     (%is New (hash-remove Assoc Key))]))

(define %assoc-to-keys
  (%rel (Assoc Keys)
    [(Assoc Keys) ;-
     (%is Keys (hash-keys Assoc))]))

(define %foldl
  (%rel (Goal H T V0 V1 V)
    [(Goal empty V V)]
    [(Goal (cons H T) V0 V) ;-
     (Goal H V0 V1)
     (%foldl Goal T V1 V)]))

(define %make-board-fold-helper
  (%rel (Chars X Y Acc New Row Char)
    [(Chars (cons X Y) Acc New) ;-
     (%is Row (list-ref Chars X))
     (%is Char (list-ref Row Y))
     (%put-assoc (cons X Y) Acc Char New)]))

(define %make-board
  (%rel (Chars B N Coords B0)
    [(Chars B) ;-
     (%square Chars N)
     (%coords N Coords)
     (%empty-assoc B0)
     (%foldl (curry %make-board-fold-helper Chars)
             Coords B0 B)]))

(define %board-has-word
  (%rel (B W Cs C First X Y DX DY NewX NewY NewB)
    [(B W) ;-
     (%assoc-to-keys B Cs)
     (%member C Cs)
     (%board-has-word B W C)]
    [((_) empty (_))]
    [(B (cons First W) (cons X Y)) ;-
     (%get-assoc (cons X Y) B First)
     (%member DX '(-1 0 1))
     (%member DY '(-1 0 1))
     (%is NewX (+ X DX))
     (%is NewY (+ Y DY))
     (%del-assoc (cons X Y) B (_) NewB)
     (%board-has-word NewB W (cons NewX NewY))]))
