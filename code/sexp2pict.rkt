#lang racket

(require pict/tree-layout
         file/convertible
         (only-in pict [text pict:text])
         racket/draw
         threading)

(define (text s)
  (pict:text s
             (list (make-object color% 255 255 0))
             20))

(define (code->tree-pict d)
  (cond
    [(list? d)
     (apply tree-layout #:pict (text (symbol->string (first d)))
            (map code->tree-pict (rest d)))]
    [else (tree-layout #:pict (text (~s d)))]))

(~> (naive-layered (code->tree-pict '(let (binding x 1) (app + x 1))))
    (convert 'png-bytes)
    write-bytes)
