#lang racket

(require (only-in 2htdp/image regular-polygon)
         pict
         file/convertible
         racket/gui)

(current-print
  (let ([old-handler (current-print)])
    (λ (v)
      (cond
        [(pict? v) (show-pict v)]
        [else (old-handler v)]))))

;; old width = 2s
;; old height = sqrt(3) * s
;; new height = 5/2 * s
;; new width = 3/2 * sqrt(3) * s
;; where s is side length of hexagon

;; diagram with s = 6

#;#;
(require rackunit)
(define (diagram s*)
  (define s (* 15 s*))
  (define w (* 2 s))
  (define h (* (sqrt 3) s))
  (define h* (* 5/2 s))
  (define w* (* 3/2 (sqrt 3) s))

  (define w*-a (/ (* 4 s) (sqrt 3)))
  (define w*-b (/ s 2 (sqrt 3)))
  (define htl (* -3/2 s))

  (define h*-a w)
  (define h*-b (/ s 2))
  (define wtr (* 1/2 s (sqrt 3)))

  (check-equal? (+ w*-a w*-b) w*)
  (check-equal? (+ h*-a h*-b) h*)

  (cc-superimpose
   ;; bg
   (filled-rectangle (* s 3) (* s 3) #:color "white")
   ;; desired bounding box for rotated hex
   (filled-rectangle h w #:color "yellow")
   (rt-superimpose
    (lb-superimpose
     ;; hex + bounding box, rotated
     (rotate (cc-superimpose (filled-rectangle w h #:color "white")
                             (regular-polygon s 6 'outline 'black))
             (/ pi 6))
     ;; parts of width of new bounding box
     (translate (colorize (hline w*-a 1) "blue") 0 htl)
     (translate (colorize (hline w*-b 1) "green") w*-a htl)
     (hline w* 1))
    ;; parts of height of new bounding box
    (translate (colorize (vline 1 h*-a) "red") (- wtr) 0)
    (translate (colorize (vline 1 h*-b) "purple") (- wtr) h*-a)
    (vline 1 h*))
   ;; dead-center of picture
   (disk s*)))

#;
(diagram 6)

#;
(with-output-to-file (expand-user-path "~/Desktop/hexagon.svg")
  (thunk
   (write-bytes (convert (diagram 6) 'svg-bytes))))

(define (custom-hex s)
  (define h (* (sqrt 3) s))
  (define r (* 1/2 h))
  (define extra-dy (* 1/2 s))

  (define path
    (let ([p (new dc-path%)])
      (begin0 p
        (send* p
               (move-to 0 0)
               (line-to 0 s)
               (line-to r (* 3/2 s))
               (line-to (* 2 r) s)
               (line-to (* 2 r) 0)
               (line-to r (* -1/2 s))
               (close)))))

  (dc (λ (dc dx dy)
        (define old-pen (send dc get-pen))
        (send* dc
               (set-pen "black" 1 'solid)
               (draw-path path dx (+ dy (* 1/2 extra-dy)))
               (set-pen old-pen)))
      h (+ s extra-dy)
      (* 1/2 extra-dy) (* 1/2 extra-dy)))

(define size 30)
(define r (* 1/2 (sqrt 3) size))
(define S (custom-hex size))
(define X (cc-superimpose (colorize S "red")
                          (colorize (text "X" null (* 2/3 size)) "white")))
(define O (cc-superimpose (colorize S "cyan")
                          (colorize (custom-hex (* 2/3 size)) "blue")))
(define M (colorize S "gray"))
(define top (hc-append X X))
(define middle (translate (hc-append X X X M O) (- r) 0))
(define bottom (hc-append X X))
(define extra (translate (hc-append X (ghost S) X) (- r) 0))
(explain-child (cc-superimpose (rectangle 400 400)
                               (vl-append top middle bottom extra))
               top middle bottom extra
               #:scale 1)
