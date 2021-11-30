#lang racket/base

(require racket/function)

(define-namespace-anchor this-module)

(define x 1)

(parameterize ([current-namespace (namespace-anchor->namespace this-module)])
  (read-eval-print-loop))
