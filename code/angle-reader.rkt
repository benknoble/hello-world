#lang racket

(require syntax/readerr)

(define (make-delim)
  #f
  #;(letrec ([misplaced-delimiter
             (case-lambda
               [(ch port) (misplaced-delimiter ch port #f #f #f #f)]
               [(ch port src line col pos)
                (raise-read-error
                  "unexpected >"
                  src line col pos 1)])])
    (make-readtable (current-readtable)
                    #\> 'terminating-macro misplaced-delimiter)))

(define (skip-whitespace port)
  ; Skips whitespace characters, sensitive to the current
  ; readtable's definition of whitespace
  (let ([ch (peek-char port)])
    (unless (eof-object? ch)
      ; Consult current readtable:
      (let-values ([(like-ch/sym proc dispatch-proc)
                    (readtable-mapping (current-readtable) ch)])
        ; If like-ch/sym is whitespace, then ch is whitespace
        (when (and (char? like-ch/sym)
                   (char-whitespace? like-ch/sym))
          (read-char port)
          (skip-whitespace port))))))

(define (parse port read-one src)
  ; Need a comma or closer
  (skip-whitespace port)
  (case (peek-char port)
    [(#\>) (read-char port)
           ; Done
           null]
    [else
      ; Either another form, a comment or an error; grab location (in case of
      ; error) and read recursively to detect comments
      (let-values ([(l c p) (port-next-location port)]
                   [(v) (read-one)])
        (cond
          [(special-comment? v)
           ; It was a comment, so try again
           (parse port read-one src)]
          [(eof-object? v)
           ; Wasn't a comment or closer; error
           (raise-read-eof-error "expected `>`" src l c p 1)]
          [else (cons v (parse port read-one src))]))]))

(define rt
  (make-readtable
    #f
    #\< 'terminating-macro
    (case-lambda
      [(ch in)
       (parse in (thunk (read/recursive in #f (make-delim))) (object-name in))]
      [(ch in src line col pos)
       (datum->syntax
         #f
         (parse in (thunk (read-syntax/recursive src in #f (make-delim))) src)
         (let-values ([(l c p) (port-next-location in)])
           (list src line col pos (and pos (- p pos)))))])
    ;; not enough information
    #\> 'terminating-macro
    (case-lambda
      [(ch in)
       (raise-read-error "unexpected `>`" #f #f #f #f 1)]
      [(ch in src line col pos)
       (raise-read-error "unexpected `>`" #f line col pos 1)])))

(define (rr s)
  (parameterize ([current-readtable rt])
    (call-with-input-string
      s
      (λ (in)
        (let loop ()
          (define v (read in))
          (if (eof-object? v)
            null
            (cons v (loop))))))))

(rr "<")
