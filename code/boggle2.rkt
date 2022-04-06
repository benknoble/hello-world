#lang racket

(provide (all-defined-out))

(require racket/generator
         rackunit)

(define letters
  (string->list "abcdefghijklmnopqrstuvwxyz"))
(define (random-list-ref l)
  (list-ref l (random (length l))))
(define (random-letter)
  (random-list-ref letters))

(define board-n 4)
(define board-keys (range (* board-n board-n)))
(define (in-board-keys c)
  (<= 0 c (sub1 (* board-n board-n))))
(define board
  (for*/vector ([row (in-range board-n)]
                [col (in-range board-n)])
    (random-letter)))

(define (->board-ref row col)
  (+ (* row board-n) col))

(define (adjust-board-ref c row col)
  (+ c (->board-ref row col)))

(define board-ref
  (case-lambda
    [(board c) (vector-ref board c)]
    [(board row col) (board-ref board (->board-ref row col))]))

(define (printer)
  (for ([row (in-range board-n)])
    (for ([col (in-range board-n)])
      (display (board-ref board row col)))
    (newline)))

(printer)
(newline)

;; if we use _all_ elements of {-1,0,1}², like in previous solutions, we will
;; have made the board wrap around! for example, the "left" direction shouldn't
;; be taken on the left edge, etc., but it will be, creating a toroidal boggle
;; board.
;;
;;  0   1   2   3
;;  4   5   6   7
;;  8   9   10  11
;;  12  13  14  15
;;
;; (> c 3)                      -> move up (-4)
;; (not (= (modulo c 4) 3))     -> move right (+1)
;; (< c 12)                     -> move down (+4)
;; (not (zero? (modulo c 4)))   -> move left (-1)
;;
;; can we translate that in terms of N?
;;
;; (> c (sub1 N))                    -> move up (-N)
;; (not (= (modulo c N) (sub1 N)))   -> move right (+1)
;; (< c (* N (sub1 N)))              -> move down (+N)
;; (not (zero? (modulo c N)))        -> move left (-1)
;;
;; note that adjust-board-ref handles the translation of ±1 to ±N for the row,
;; so we only need to pass Δ(row,col) ∈ {-1,0,1}²
(define neutral 0)
(define down 1)
(define right 1)
(define up (- down))
(define left (- right))

;; could mostly be done with with curry[r]/compose1, but this is at least
;; readable
(define (has-up c) (> c (sub1 board-n)))
(define (has-right c) (not (= (modulo c board-n) (sub1 board-n))))
(define (has-down c) (< c (* board-n (sub1 board-n))))
(define (has-left c) (not (zero? (modulo c board-n))))

(define move-tests
  (list ;; item = (Δrow Δcol tests…)
    (list  up       neutral
           has-up)
    (list  up       right
           has-up   has-right)
    (list  neutral  right
                    has-right)
    (list  down     right
           has-down has-right)
    (list  down     neutral
           has-down)
    (list  down     left
           has-down has-left)
    (list  neutral  left
                    has-left)
    (list  up       left
           has-up   has-left)))

(check-equal? (length move-tests)
              (sub1 ;; no neutral-neutral; though, we could put (list 0 0 (const #f)) in
                (* (length (list up neutral down))
                   (length (list left neutral right)))))

(define (moves c)
  (in-generator
    (for-each
      (match-lambda [`(,row ,col ,tests ...)
                      (when (andmap (λ (test) (test c)) tests)
                        (yield (adjust-board-ref c row col)))])
      move-tests)))

(define (check word board)
  (ormap (curry check-start word board (set))
         board-keys))

(define (check-start word board seen c)
  (or (zero? (string-length word))
      ;; handle the out-of-bounds here to avoid dealing with it in all the
      ;; index computations
      (and (in-board-keys c)
           (not (set-member? seen c))
           (eq? (board-ref board c) (string-ref word 0))
           (let ([new-seen (set-add seen c)]
                 ;; better than recomputing it for each recursive call
                 [new-word (substring word 1)])
             (for/or ([move (moves c)])
               (check-start new-word board new-seen move))))))

(define (find-words board maximum-word-length)
  (apply in-sequences
         (map (curry find-words-at board maximum-word-length)
              board-keys)))

(define (find-words-at board maximum-word-length c)
  (in-generator
    (let loop ([path empty]
               [seen (set)]
               [c c])
      (define char (and (in-board-keys c)
                        (not (set-member? seen c))
                        (board-ref board c)))
      (when char
        (define new-path (cons char path))
        (when (<= minimum-word-length (length new-path) maximum-word-length)
          (yield (list->string (reverse new-path))))
        (unless (or (eq? (set-count seen) (length board-keys))
                    (>= (length new-path) maximum-word-length))
          (define new-seen (set-add seen c))
          (for ([move (moves c)])
            (loop new-path new-seen move)))))))

(define minimum-word-length 3)
(define maximum-word-length 8)

;; TORUS:
;; ~3 times as slow because find-words yields 4+ times as many words?
;; uniqueness isn't even the issue here…

;; CORRECT:
;; twice as slow, but correct amount of words (~2.85 as much gc time)
(time (displayln (for/fold ([count 0])
                   ([word (find-words board maximum-word-length)])
                   (check-true (check word board))
                   (add1 count))))

;; possible approach: generate (at compile-time? 00) the possible paths through
;; the NxN grid of bounded size; map those to words only later?

;; would also be fun to write this problem using the graph library to learn how
;; to use it
