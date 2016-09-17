(library (tests)
  (export run-tests)
  (import (c) (rnrs) (rnrs eval) (implementation-helpers))
  
  (define-syntax define-tests
    (syntax-rules ()
      [(_ name test ...)
       (define name
         (list
           (cons 'test
             (eval `(canonicalize-result ,'test)
               (environment '(test-lib))))
           ...))]))

  ;; NB: need to add many more tests to make sure we're fully testing the compiler.
  (define-tests tests
    0
    -5
    5
    #t
    #f
    '()
    '(3 . 4)
    '(1 2 3 4)
    '(1 2 . 3)
    '(((1 . 2) (3 . 4)) (5 . 6))
    '((0 . #t) (1 . #f) (3 . #t))
    '#(1 2 3)
    '#((2 . 3) #f #t (#t . 4))
    (car '(1 . 2))
    (cdr '(1 . 2))
    (cons 1 2)
    (car (cons 1 2))
    (cdr (cons 1 2))
    (pair? '(1 . 2))
    (pair? (cons 1 2))
    (null? '())
    (null? (cdr (cons 1 '())))
    (vector-ref '#(1 2 3) 1)
    (vector-length '#(1 2 3))
    (vector-length (make-vector 10))
    (box 4)
    (box '(1 . 2))
    (unbox (box 10))
    (car (unbox (box (cons 1 2))))
    (+ 2 3)
    (+ (+ 4 5) (+ 6 7))
    (- 2 3)
    (- (- (- 1 2) 3) 4)
    (* 2 5)
    (* 3 (* 4 5))
    (/ 10 2)
    (/ 7 2)
    (/ (/ 10 2) 2)
    (+ (- 1 20) 30)
    (- 4 4)
    (box? (box 4))
    (box? (box #f))
    (box? (cons 1 2))
    (letrec ([! (lambda (n)
                  (if (zero? n)
                      1
                      (* n (! (- n 1)))))]
              [zero? (lambda (n) (= n 1))])
      (! 10))
    (letrec ([f (lambda (g x) (g x))]
             [a 5]
             [b (+ 5 7)]
             [g (lambda (h) (f h 5))]
             [c (let ([x 10]) ((letrec ([zero? (lambda (n) (= n 0))]
                                        [f (lambda (n) 
                                             (if (zero? n)
                                                 1
                                                 (* n (f (- n 1)))))])
                                 f)
                                x))]
             [m 10]
             [z (lambda (x) x)])
      (set! z (lambda (x) (+ x x)))
      (set! m (+ m m))
      (+ (+ (+ (f z a) (f z b)) (f z c)) (g z)))
    (let ([f (lambda (x y) (* x y))])
      (set! f (lambda (x y) (+ x y)))
      (f 5 3)))

  (define run-tests
    (lambda ()
      (let loop ([tests tests] [i 0])
        (unless (null? tests)
          (let ([test (car tests)])
            (let ([expr (car test)] [result (cdr test)])
              (printf "running test ~d:~%" i)
              (pretty-print expr)
              ;; NB: when we hit an exception, report the result as part of the string.
              (guard (c [else (printf "failed with exception (TBD)~%")])
                (let ([actual (my-tiny-compile expr)])
                  (if (equal? actual result)
                      (printf "passed~%")
                      (printf "expected ~s but got ~s~%" result actual))))
              (loop (cdr tests) (fx+ i 1)))))))))

