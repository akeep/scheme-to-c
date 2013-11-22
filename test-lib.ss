(library (test-lib)
  (export quote if or and not begin lambda let letrec set! cons make-vector box
    car cdr vector-ref vector-length unbox + - * / pair? null? boolean? vector?
    box? = < <= > >= eq? vector-set! set-box! canonicalize-result) 
  (import (rename (except (rnrs) /) (div /)) (rnrs mutable-pairs))

  ;; implement a box type since there is no box type in R6RS, even though it
  ;; may be included in our host implementations.
  (define-record-type (box-record box box?) (fields (mutable value unbox set-box!)))

  (define canonicalize-result
    (lambda (x)
      (cond
        [(box? x) (vector 'box (canonicalize-result (unbox x)))]
        [(vector? x) (vector-map canonicalize-result x)]
        [(pair? x) (cons (canonicalize-result (car x))
                     (canonicalize-result (cdr x)))]
        [(procedure? x) '#(procedure)]
        [(eq? (if #f #f) x) '#(void)]
        [else x]))))

