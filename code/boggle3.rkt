#lang racket


(provide (all-defined-out))

(require racket/generator
         graph
         rackunit)

(define (hash-invert h)
  (for/fold ([inverted #hash()])
    ([k (in-hash-keys h)])
    (hash-update inverted
                 (hash-ref h k)
                 (curry cons k)
                 empty)))

(random-seed 123)

(define letters
  (string->list "abcdefghijklmnopqrstuvwxyz"))
(define (random-list-ref l)
  (list-ref l (random (length l))))
(define (random-letter)
  (random-list-ref letters))

(define board-n 4)

(struct board [coord->letter letter->coords coord-graph])

(define the-board
  (let ()
    (define coord->letter
      (for*/fold ([cell->char (hash)])
        ([row (in-range board-n)]
         [col (in-range board-n)])
        (hash-set cell->char (cons row col) (random-letter))))
    (define edges
      (for*/list ([row (in-range board-n)]
                  [col (in-range board-n)]
                  [dx (in-list '(-1 0 1))]
                  [dy (in-list '(-1 0 1))]
                  #:when (not (and (zero? dx) (zero? dy)))
                  #:when (hash-ref coord->letter (cons row col) #f)
                  #:when (hash-ref coord->letter (cons (+ row dx) (+ col dy)) #f))
        (list (cons row col)
              (cons (+ row dx) (+ col dy)))))
    (board coord->letter (hash-invert coord->letter) (undirected-graph edges))))

(define (printer)
  (for ([row (in-range board-n)])
    (for ([col (in-range board-n)])
      (display (hash-ref (board-coord->letter the-board) (cons row col))))
    (newline)))

(printer)
(newline)
(check-equal? (length (get-edges (board-coord-graph the-board)))
              ;; https://en.wikipedia.org/wiki/King%27s_graph
              (* 2 (- (* 2 board-n) 2) (- (* 2 board-n) 1)))

;; ,r /Users/Knoble/write/benknoble.github.io/scribblings/2021-10-27-boggle.scrbl
;; wbdu
;; qlhr
;; viqj
;; fwfn
;; 283300
;; cpu time: 5595 real time: 5605 gc time: 70

;; ,require-reloadable /Users/Knoble/write/junk-drawer/code/boggle3.rkt
;; ; reloading "~/write/junk-drawer/code/boggle3.rkt"
;; meqv
;; alhg
;; bgid
;; metp
;; cpu time: 10503 real time: 10519 gc time: 35
;; 283300

;; (let* ([word
;;          "meqv"
;;          ;; "mt"
;;          ;; "met"
;;          ;; "malhgig"
;;          ;; "malhgigetpd"
;;          ;; "meqvghlabgidptem"
;;          ;; "meqvghlabgidpteg"
;;          ]
;;        [letters (string->list word)]
;;        [seen (mutable-set)])
;;   (do-dfs (board-coord-graph the-board)
;;           #:break: (empty? letters)
;;           #:visit?: (and (not (set-member? seen $to))
;;                          (eq? (car letters) (hash-ref (board-coord->letter the-board) $to)))
;;           #:prologue:
;;           (set-add! seen $v)
;;           (set! letters (cdr letters))
;;           #:epilogue:
;;           (set-remove! seen $v)
;;           (set! letters (cons (hash-ref (board-coord->letter the-board) $v) letters))
;;           #:return: $broke?))

(define (check word the-board)
  (define letters (string->list word))
  (define-vertex-property (board-coord-graph the-board) seen #:init #f)
  (do-dfs (board-coord-graph the-board)
          #:break: (empty? letters)
          #:visit?: (and (not (seen $to))
                         (eq? (car letters) (hash-ref (board-coord->letter the-board) $to)))
          #:prologue:
          (seen-set! $v #t)
          (set! letters (cdr letters))
          #:epilogue:
          (seen-set! $v #f)
          (set! letters (cons (hash-ref (board-coord->letter the-board) $v) letters))
          #:return: $broke?))

(time (for/fold ([count 0])
        ([word (in-generator
                 (let ()
                   (define-vertex-property (board-coord-graph the-board) seen #:init #f)
                   (define letters null)
                   (do-dfs (board-coord-graph the-board)
                           ;; #:init: null
                           ;; need to visit all possible paths…
                           ;; currently only getting 6 3-8 letter long words out of 4x4
                           ;; probably need #:visit?: with custom mutable state,
                           ;; or a graph property…
                           ;;
                           ;; would love to also prune the depth by checking the
                           ;; length of the $acc, but the immutable style is
                           ;; kind of nice here. I'll do it if this is really
                           ;; slow, though.
                           #:visit?: (and (not (seen $v))
                                          (<= (length letters) 8))
                           #:prologue:
                           (seen-set! $v #t)
                           ;; (define new-acc (cons $v $acc))
                           (set! letters (cons $v letters))
                           (when (<= 3 (length #;new-acc letters) 8)
                             (define word
                               (list->string (map (curry hash-ref (board-coord->letter the-board))
                                                  (reverse #;new-acc letters))))
                             (yield word))
                           ;; new-acc
                           (void)
                           #:epilogue:
                           (seen-set! $v #f)
                           ;; (cdr $acc)
                           (set! letters (cdr letters)))))])
        ;; (displayln word)
        (check-true (check word the-board))
        (add1 count)))
