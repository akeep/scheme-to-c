;;; Copyright (c) 2013 Andrew W. Keep
;;; See the accompanying file Copyright for details
;;;
;;; A nanopass compiler developed to use as a demo during Clojure Conj 2013.
;;; The source language for the compiler is: 
;;;
;;; Expr      --> <Primitive>
;;;            |  <Var> 
;;;            |  <Const> 
;;;            |  (quote <Datum>)
;;;            |  (if <Expr> <Expr>)
;;;            |  (if <Expr> <Expr> <Expr>)
;;;            |  (or <Expr> ...)
;;;            |  (and <Expr> ...)
;;;            |  (not <Expr>)
;;;            |  (begin <Expr> ... <Expr>)
;;;            |  (lambda (<Var> ...) <Expr> ... <Expr>)
;;;            |  (let ([<Var> <Expr>] ...) <Expr> ... <Expr>)
;;;            |  (letrec ([<Var> <Expr>] ...) <Expr> ... <Expr>)
;;;            |  (set! <Var> <Expr>)
;;;            |  (<Expr> <Expr> ...)
;;;
;;; Primitive --> car | cdr | cons | pair? | null? | boolean? | make-vector
;;;            |  vector-ref | vector-set! | vector? | vector-length | box
;;;            |  unbox | set-box! | box? | + | - | * | / | = | < | <= | >
;;;            |  >= | eq? 
;;; Var       --> symbol
;;; Const     --> #t | #f | '() | integer between -2^60 and 2^60 - 1
;;; Datum     --> <Const> | (<Datum> . <Datum>) | #(<Datum> ...)
;;;
;;; or in nanopass parlance:
;;; (define-language Lsrc
;;;   (terminals
;;;     (symbol (x))
;;;     (primitive (pr))
;;;     (constant (c))
;;;     (datum (d)))
;;;   (Expr (e body)
;;;     pr
;;;     x
;;;     c
;;;     (quote d)
;;;     (if e0 e1)
;;;     (if e0 e1 e2)
;;;     (or e* ...)
;;;     (and e* ...)
;;;     (not e)
;;;     (begin e* ... e)
;;;     (lambda (x* ...) body* ... body)
;;;     (let ([x* e*] ...) body* ... body)
;;;     (letrec ([x* e*] ...) body* ... body)
;;;     (set! x e)
;;;     (e e* ...)))
;;;
;;; The following exports are defined for this library:
;;;
;;; (my-tiny-compile <exp>)
;;;     my-tiny-compile is the main interface the compiler, where <exp> is
;;;     a quoted expression for the compiler to evaluate.  This procedure will
;;;     run the nanopass parts of the compiler, produce a C output file in t.c,
;;;     compile it using gcc to a program t, run the program t, directing its
;;;     output to t.out, and finally use the Scheme reader to read t.out and
;;;     return the value to the host Scheme system.  For example, if we wanted
;;;     to run a program that calculates the factorial of 5, we could do the 
;;;     following:
;;;     (my-tiny-compile '(letrec ([f (lambda (n)
;;;                                     (if (= n 0)
;;;                                         1
;;;                                         (* n (f (- n 1)))))])
;;;                         (f 10)))
;;;
;;; (trace-passes)
;;; (trace-passes <pass-spec>)
;;;     trace-passes is a parameter used by my-tiny-compile to decide what
;;;     passees should have their output printed.  When it is called without
;;;     any arguments, it returns the list of passes to be traced.  When it
;;;     is called with an argument, the argument should be one of the
;;;     following:
;;;     '<pass-name>                       - sets this pass to be traced
;;;     '(<pass-name 0> <pass-name 1> ...) - set the list of passes to trace
;;;     #t                                 - traces all passes
;;;     #f                                 - turns off trace passing
;;;
;;; all-passes
;;;     lists all passes in the compiler.
;;;
;;; (use-boehm?)
;;; (use-boehm? <boolean>)
;;;     use-boehm? is a parameter that indicates if the generated C code should
;;;     attempt to use the boehm garbage collector.  This feature is, as of
;;;     yet, untested.
;;;
;;; Internals that are exported to make them available for programmers
;;; experimenting with the compiler.
;;;
;;; TBD
;;;
;;;
(library (c)
  (export
    Lsrc unparse-Lsrc
    L1 unparse-L1
    L2 unparse-L2
    L3 unparse-L3
    L4 unparse-L4
    L5 unparse-L5
    L6 unparse-L6 
    L7 unparse-L7
    L8 unparse-L8
    L9 unparse-L9
    L10 unparse-L10
    L11 unparse-L11
    L12 unparse-L12
    L13 unparse-L13
    L14 unparse-L14
    L15 unparse-L15
    L16 unparse-L16
    L17 unparse-L17
    L18 unparse-L18
    L19 unparse-L19
    ; L20 unparse-L20
    L21 unparse-L21
    L22 unparse-L22

    unique-var

    user-alloc-value-prims
    user-non-alloc-value-prims
    user-pred-prims
    user-effect-prims
    user-prims
    void+user-non-alloc-value-prims
    void+user-prims
    closure+user-alloc-value-prims
    closure+void+user-non-alloc-value-prims
    closure+user-effect-prims
    internal+closure+user-effect-prims
    closure+void+user-prims

    primitive?
    void+primitive?
    closure+void+primitive?
    effect-free-prim?
    predicate-primitive?
    effect-primitive?
    value-primitive?
    non-alloc-value-primitive?
    effect+internal-primitive?

    target-fixnum?
    constant?
    datum?
    integer-64?

    set-cons
    union
    difference
    intersect

    parse-and-rename
    remove-one-armed-if
    remove-and-or-not
    make-begin-explicit
    inverse-eta-raw-primitives
    quote-constants
    remove-complex-constants
    identify-assigned-variables 
    purify-letrec
    optimize-direct-call
    find-let-bound-lambdas
    remove-anonymous-lambda
    convert-assignments
    uncover-free
    convert-closures
    optimize-known-call
    expose-closure-prims
    lift-lambdas
    remove-complex-opera*
    recognize-context
    expose-allocation-primitives
    return-of-set!
    flatten-set!
    ; push-if
    specify-constant-representation
    expand-primitives
    generate-c

    use-boehm?
    
    my-tiny-compile
    trace-passes
    all-passes)
  (import (nanopass) (rnrs)
    (only (implementation-helpers) printf format system pretty-print))

  ;;; As of yet untested feature for using the boehm GC
  ;;; in the compiled output of our compiler.
  (define use-boehm?
    (let ([use? #f])
      (case-lambda
        [() use?]
        [(u?) (set! use? u?)])))

  ;;; Representation of our data types.
  ;;; We use tagged pointers, because all of our pointers are 8-byte aligned,
  ;;; leaving te bottom 3 bits always being 0.  Using these 3 bits for tags
  ;;; lets us store things like fixnums as pointers, and differentiate them
  ;;; from pointers like closures and vectors.  It also saves us using a word
  ;;; for a tag when in our representation of vectors, closures, etc.
  (define fixnum-tag   #b000)
  (define fixnum-mask  #b111)
  
  (define pair-tag     #b001)
  (define pair-mask    #b111)
  
  (define box-tag      #b010)
  (define box-mask     #b111)
  
  (define vector-tag   #b011)
  (define vector-mask  #b111)
  
  (define closure-tag  #b100)
  (define closure-mask #b111)
  
  ;;; NOTE: #b101 is used for constants

  (define boolean-tag    #b1101)
  (define boolean-mask   #b1111)

  (define true-rep     #b111101)
  (define false-rep    #b101101)

  (define null-rep     #b100101)
  (define void-rep     #b110101)

  (define fixnum-shift 3)
  (define word-size 8)



  ;;; Helper function for representing unique variables as symbols by adding a
  ;;; number to the variables (so if we start with f we get f.n where n might
  ;;;  be 1, 2, 3, etc, and is unique).
  (define unique-var
    (let ()
      (define count 0)
      (lambda (name)
        (let ([c count])
          (set! count (+ count 1))
          (string->symbol
            (string-append (symbol->string name) "." (number->string c)))))))

  ;; strip the numberic bit back off the unique-var
  (define base-var
    (lambda (x)
      (define s0
        (lambda (rls)
          (if (null? rls)
              (error 'base-var "not a unique-var created variable" x)
              (let ([c (car rls)])
                (cond
                  [(char-numeric? c) (s1 (cdr rls))]
                  [else (error 'base-var
                          "not a unique-var created variable" x)])))))
      (define s1
        (lambda (rls)
          (if (null? rls)
              (error 'base-var "not a unique-var created variable" x)
              (let ([c (car rls)])
                (cond
                  [(char-numeric? c) (s1 (cdr rls))]
                  [(char=? c #\.) (cdr rls)]
                  [else (error 'base-var
                          "not a unique-var created variable" x)])))))
      (string->symbol
        (list->string
          (reverse 
            (s0 (reverse (string->list (symbol->string x)))))))))
      

  ;;; Convenience procedure for building temporaries in the compiler.
  (define make-tmp (lambda () (unique-var 't)))

  ;;; Helpers for the various sets of primitives we have over the course of the
  ;;; compiler
  ;;; All primitives:
  ;;;
  ;;;                     |       |         | Langauge   | Language |
  ;;; primitive           | arity | context | introduced | removed  |
  ;;; --------------------+-------+---------+------------+----------+
  ;;; cons                |   2   |  value  |    Lsrc    |    L17   |
  ;;; make-vector         |   1   |  value  |    Lsrc    |    L17   |
  ;;; box                 |   1   |  value  |    Lsrc    |    L17   |
  ;;; car                 |   1   |  value  |    Lsrc    |    L22   |
  ;;; cdr                 |   1   |  value  |    Lsrc    |    L22   |
  ;;; vector-ref          |   2   |  value  |    Lsrc    |    L22   |
  ;;; vector-length       |   1   |  value  |    Lsrc    |    L22   |
  ;;; unbox               |   1   |  value  |    Lsrc    |    L22   |
  ;;; +                   |   2   |  value  |    Lsrc    |    L22   |
  ;;; -                   |   2   |  value  |    Lsrc    |    L22   |
  ;;; *                   |   2   |  value  |    Lsrc    |    L22   |
  ;;; /                   |   2   |  value  |    Lsrc    |    L22   |
  ;;; pair?               |   1   |  pred   |    Lsrc    |    L22   |
  ;;; null?               |   1   |  pred   |    Lsrc    |    L22   |
  ;;; boolean?            |   1   |  pred   |    Lsrc    |    L22   |
  ;;; vector?             |   1   |  pred   |    Lsrc    |    L22   |
  ;;; box?                |   1   |  pred   |    Lsrc    |    L22   |
  ;;; =                   |   2   |  pred   |    Lsrc    |    L22   |
  ;;; <                   |   2   |  pred   |    Lsrc    |    L22   |
  ;;; <=                  |   2   |  pred   |    Lsrc    |    L22   |
  ;;; >                   |   2   |  pred   |    Lsrc    |    L22   |
  ;;; >=                  |   2   |  pred   |    Lsrc    |    L22   |
  ;;; eq?                 |   2   |  pred   |    Lsrc    |    L22   |
  ;;; vector-set!         |   3   |  effect |    Lsrc    |    L22   |
  ;;; set-box!            |   2   |  effect |    Lsrc    |    L22   |
  ;;; --------------------+-------+---------+------------+----------+
  ;;; void                |   0   |  value  |    L1      |    L22   |
  ;;; --------------------+-------+---------+------------+----------+
  ;;; make-closure        |   1   |  value  |    L13     |    L17   |
  ;;; closure-code        |   2   |  value  |    L13     |    L22   |
  ;;; closure-ref         |   2   |  value  |    L13     |    L22   |
  ;;; closure-code-set!   |   2   |  effect |    L13     |    L22   |
  ;;; closure-data-set!   |   3   |  effect |    L13     |    L22   |
  ;;; --------------------+-------+---------+------------+----------+
  ;;; $vector-length-set! |   2   |  effect |    L17     |    L22   |
  ;;; $set-car!           |   2   |  effect |    L17     |    L22   |
  ;;; $set-cdr!           |   2   |  effect |    L17     |    L22   |
  ;;;
  ;;; This is a slightly cleaned up version, but this might still be better
  ;;; cleaned up by adding a define-primitives form, perhaps even one that can
  ;;; be used in the later parts of the compiler.

  ;;; user value primitives that perform allocation
  (define user-alloc-value-prims
    '((cons . 2) (make-vector . 1) (box . 1)))

  ;;; user value primitives that do not perform allocation
  (define user-non-alloc-value-prims
    '((car . 1) (cdr . 1) (vector-ref . 2) (vector-length . 1) (unbox . 1)
      (+ . 2) (- . 2) (* . 2) (/ . 2)))

  ;;; user predicate primitives
  ;;; TODO: add procedure?
  (define user-pred-prims
    '((pair? . 1) (null? . 1) (boolean? . 1) (vector? . 1) (box? . 1) (= . 2)
      (< . 2) (<= . 2) (> . 2) (>= . 2) (eq? . 2)))

  ;;; user effect primitives
  (define user-effect-prims
    '((vector-set! . 3) (set-box! . 2)))

  ;;; an association list with the user primitives
  (define user-prims
    (append user-alloc-value-prims user-non-alloc-value-prims user-pred-prims
      user-effect-prims))

  ;;; void primitive + non-allocation user value primitives
  (define void+user-non-alloc-value-prims
    (cons '(void . 0) user-non-alloc-value-prims))

  ;;; an association list with void and all the user primitives
  (define void+user-prims
    (append user-alloc-value-prims void+user-non-alloc-value-prims
      user-pred-prims user-effect-prims))

  ;;; all the allocation value primitives, including make-closure primitive
  (define closure+user-alloc-value-prims
    (cons '(make-closure . 1) user-alloc-value-prims))

  ;;; all the non-allocation value primitives, include the closure primitives
  (define closure+void+user-non-alloc-value-prims
    (cons* '(closure-code . 2) '(closure-ref . 2)
      void+user-non-alloc-value-prims))

  ;; all the user effect primitives with the closure primitives
  (define closure+user-effect-prims
    (cons* '(closure-code-set! . 2) '(closure-data-set! . 3)
      user-effect-prims))

  ;; all the user effect primitives, closure primitives, and internal primitives
  (define internal+closure+user-effect-prims
    (cons* '($vector-length-set! . 2) '($set-car! . 2) '($set-cdr! . 2)
      closure+user-effect-prims))

  ;; association list including all prims except the three final internal
  ;; primitives
  (define closure+void+user-prims
    (append closure+user-alloc-value-prims
      closure+void+user-non-alloc-value-prims user-pred-prims
      closure+user-effect-prims))

  ;;; various predicates for determining if a primitve is a valid prim.
  (define primitive?
    (lambda (x)
      (assq x user-prims)))

  (define void+primitive?
    (lambda (x)
      (assq x void+user-prims)))

  (define closure+void+primitive?
    (lambda (x)
      (assq x closure+void+user-prims)))
  
  (define effect-free-prim?
    (lambda (x)
      (assq x (append void+user-non-alloc-value-prims user-alloc-value-prims
                user-pred-prims))))

  (define predicate-primitive?
    (lambda (x)
      (assq x user-pred-prims)))

  (define effect-primitive?
    (lambda (x)
      (assq x closure+user-effect-prims)))

  (define value-primitive?
    (lambda (x)
      (assq x (append closure+user-alloc-value-prims
                closure+void+user-non-alloc-value-prims))))

  (define non-alloc-value-primitive?
    (lambda (x)
      (assq x closure+void+user-non-alloc-value-prims)))

  (define effect+internal-primitive?
    (lambda (x)
      (assq x internal+closure+user-effect-prims)))

  ;;;;;;;;;;
  ;;; Helper functions for identifying terminals in the nanopass languages.

  ;;; determine if we have a 61-bit signed integer
  (define target-fixnum?
    (lambda (x)
      (and (and (integer? x) (exact? x))
           (<= (- (expt 2 60)) x (- (expt 2 60) 1)))))

  ;;; determine if we have a constant: #t, #f, '(), or 61-bit signed integer.
  (define constant?
    (lambda (x)
      (or (target-fixnum? x) (boolean? x) (null? x))))

  ;;; determine if we have a valid datum (a constant, a pair of datum, or a
  ;;; vector of datum)
  (define datum?
    (lambda (x)
      (or (constant? x)
          (and (pair? x) (datum? (car x)) (datum? (cdr x)))
          (and (vector? x)
               (let loop ([i (vector-length x)])
                 (or (fx=? i 0)
                     (let ([i (fx- i 1)])
                       (and (datum? (vector-ref x i))
                            (loop i)))))))))

  ;;; determine if we have a 64-bit signed integer (used later in the compiler
  ;;; to hold the ptr representation).
  (define integer-64?
    (lambda (x)
      (and (and (integer? x) (exact? x))
           (<= (- (expt 2 63)) x (- (expt 2 63) 1)))))

  ;;; Random helper available on most Scheme systems, but irritatingly not in
  ;;; the R6RS standard.
  (define make-list
    (case-lambda
      [(n) (make-list n (if #f #f))]
      [(n v) (let loop ([n n] [ls '()])
               (if (zero? n)
                   ls
                   (loop (fx- n 1) (cons v ls))))]))

  ;;;;;;;;
  ;;; The standard (not very efficient) Scheme representation of sets as lists
  
  ;;; add an item to a set
  (define set-cons
    (lambda (x set)
      (if (memq x set)
          set
          (cons x set))))

  ;;; construct the intersection of 0 to n sets
  (define intersect
    (lambda set*
      (if (null? set*)
          '()
          (fold-left (lambda (seta setb)
                       (let loop ([seta seta] [fset '()])
                         (if (null? seta)
                             fset
                             (let ([a (car seta)])
                               (if (memq a setb)
                                   (loop (cdr seta) (cons a fset))
                                   (loop (cdr seta) fset))))))
            (car set*) (cdr set*)))))

  ;;; construct the union of 0 to n sets
  (define union
    (lambda set*
      (if (null? set*)
          '()
          (fold-left (lambda (seta setb)
                       (let loop ([setb setb] [seta seta])
                         (if (null? setb)
                             seta
                             (loop (cdr setb) (set-cons (car setb) seta)))))
            (car set*) (cdr set*)))))

  ;;; construct the difference of 0 to n sets
  (define difference
    (lambda set*
      (if (null? set*)
          '()
          (fold-right (lambda (setb seta)
                        (let loop ([seta seta] [final '()])
                          (if (null? seta)
                              final
                              (let ([a (car seta)])
                                (if (memq a setb)
                                    (loop (cdr seta) final)
                                    (loop (cdr seta) (cons a final)))))))
            (car set*) (cdr set*)))))

  ;;; Language definitions for Lsrc and L1 to L22
  ;;; Both the language extension and the fully specified language is included
  ;;; (though the fully specified language may be out of date).  This can be
  ;;; regenerated by doing:
  ;;; > (import (c))
  ;;; > (import (nanopass))
  ;;; > (language->s-expression L10) => generates L10 definition
  (define-language Lsrc
    (terminals
      (symbol (x))
      (primitive (pr))
      (constant (c))
      (datum (d)))
    (Expr (e body)
      pr
      x
      c
      (quote d)
      (if e0 e1)
      (if e0 e1 e2)
      (or e* ...)
      (and e* ...)
      (not e)
      (begin e* ... e)
      (lambda (x* ...) body* ... body)
      (let ([x* e*] ...) body* ... body)
      (letrec ([x* e*] ...) body* ... body)
      (set! x e)
      (e e* ...)))

  ;;; Language 1: removes one-armed if and adds the void primitive
  ;
  ; (define-language L1
  ;   (terminals (void+primitive (pr))
  ;     (symbol (x))
  ;     (constant (c))
  ;     (datum (d)))
  ;   (Expr (e body)
  ;     pr
  ;     x
  ;     c
  ;     (quote d)
  ;     (if e0 e1 e2)
  ;     (or e* ...)
  ;     (and e* ...)
  ;     (not e)
  ;     (begin e* ... e)
  ;     (lambda (x* ...) body* ... body)
  ;     (let ([x* e*] ...) body* ... body)
  ;     (letrec ([x* e*] ...) body* ... body)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L1
    (extends Lsrc)
    (terminals
      (- (primitive (pr)))
      (+ (void+primitive (pr))))
    (Expr (e body)
      (- (if e0 e1))))

  ;;; Language 2: removes or, and, and not forms
  ;
  ; (define-language L2
  ;   (terminals (void+primitive (pr))
  ;     (symbol (x))
  ;     (constant (c))
  ;     (datum (d)))
  ;   (Expr (e body)
  ;     pr
  ;     x
  ;     c
  ;     (quote d)
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (lambda (x* ...) body* ... body)
  ;     (let ([x* e*] ...) body* ... body)
  ;     (letrec ([x* e*] ...) body* ... body)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L2
    (extends L1)
    (Expr (e body)
      (- (or e* ...)
         (and e* ...)
         (not e))))

  ;;; Language 3: removes multiple expressions from the body of lambda, let,
  ;;; and letrec (to be replaced with a single begin expression that contains
  ;;; the expressions from the body).
  ;
  ; (define-language L3
  ;   (terminals (void+primitive (pr))
  ;     (symbol (x))
  ;     (constant (c))
  ;     (datum (d)))
  ;   (Expr (e body)
  ;     (letrec ([x* e*] ...) body)
  ;     (let ([x* e*] ...) body)
  ;     (lambda (x* ...) body)
  ;     pr
  ;     x
  ;     c
  ;     (quote d)
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L3
    (extends L2)
    (Expr (e body)
      (- (lambda (x* ...) body* ... body)
         (let ([x* e*] ...) body* ... body)
         (letrec ([x* e*] ...) body* ... body))
      (+ (lambda (x* ...) body)
         (let ([x* e*] ...) body)
         (letrec ([x* e*] ...) body))))

  ;;; Language 4: removes raw primitives (to be replaced with a lambda and a
  ;;; primitive call).
  ;
  ; (define-language L4
  ;   (terminals (void+primitive (pr))
  ;     (symbol (x))
  ;     (constant (c))
  ;     (datum (d)))
  ;   (Expr (e body)
  ;     (primcall pr e* ...)
  ;     (letrec ([x* e*] ...) body)
  ;     (let ([x* e*] ...) body)
  ;     (lambda (x* ...) body)
  ;     x
  ;     c
  ;     (quote d)
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L4
    (extends L3)
    (Expr (e body)
      (- pr)
      (+ (primcall pr e* ...) => (pr e* ...))))

  ;;; Language 5: removes raw constants (to be replaced with quoted constant).
  ;
  ; (define-language L5
  ;   (terminals
  ;     (void+primitive (pr))
  ;     (symbol (x))
  ;     (datum (d)))
  ;   (Expr (e body)
  ;     (primcall pr e* ...)
  ;     (letrec ([x* e*] ...) body)
  ;     (let ([x* e*] ...) body)
  ;     (lambda (x* ...) body)
  ;     x
  ;     (quote d)
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L5
    (extends L4)
    (terminals
      (- (constant (c))))
    (Expr (e body)
      (- c)))

  ;;; Language 6: removes quoted datum (to be replaced with explicit calls to
  ;;; cons and make-vector+vector-set!).
  ;
  ; (define-language L6
  ;   (terminals
  ;     (constant (c))
  ;     (void+primitive (pr))
  ;     (symbol (x)))
  ;   (Expr (e body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     (letrec ([x* e*] ...) body)
  ;     (let ([x* e*] ...) body)
  ;     (lambda (x* ...) body)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...)))
  ;
  (define-language L6
    (extends L5)
    (terminals
      (- (datum (d)))
      (+ (constant (c))))
    (Expr (e body)
      (- (quote d))
      (+ (quote c))))

  ;;; Language 7: adds a listing of assigned variables to the body of the
  ;;; binding forms: let, letrec, and lambda.
  ; (define-language L7
  ;   (terminals
  ;     (symbol (x a))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (letrec ([x* e*] ...) abody)
  ;     (let ([x* e*] ...) abody)
  ;     (lambda (x* ...) abody)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...))
  ;   (AssignedBody (abody)
  ;     (assigned (a* ...) body)))
  ;
  (define-language L7
    (extends L6)
    (terminals
      (- (symbol (x)))
      (+ (symbol (x a))))
    (Expr (e body)
      (- (lambda (x* ...) body)
         (let ([x* e*] ...) body)
         (letrec ([x* e*] ...) body))
      (+ (lambda (x* ...) abody)
         (let ([x* e*] ...) abody)
         (letrec ([x* e*] ...) abody)))
    (AssignedBody (abody)
      (+ (assigned (a* ...) body))))

  ;;; Language 8: letrec binding is changed to only bind variables to lambdas.
  ;
  ; (define-language L8
  ;   (terminals (symbol (x a))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (letrec ([x* le*] ...) body)
  ;     le
  ;     (let ([x* e*] ...) abody)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...))
  ;   (AssignedBody (abody)
  ;     (assigned (a* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) abody)))
  ;
  (define-language L8
    (extends L7)
    (Expr (e body)
      (- (lambda (x* ...) abody)
         (letrec ([x* e*] ...) abody))
      (+ le
         (letrec ([x* le*] ...) body)))
    (LambdaExpr (le)
      (+ (lambda (x* ...) abody))))

  ;;; Language 9: removes lambda expressions from expression context,
  ;;; effectively meaning we can only have lambdas bound in the right-hand-side
  ;;; of letrec expressions.
  ;
  ; (define-language L9
  ;   (terminals
  ;     (symbol (x a))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (letrec ([x* le*] ...) body)
  ;     (let ([x* e*] ...) abody)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (set! x e)
  ;     (e e* ...))
  ;   (AssignedBody (abody)
  ;     (assigned (a* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) abody)))
  ;
  (define-language L9
    (extends L8)
    (Expr (e body)
      (- le)))
      
  ;;; Language 10: removes set! and assigned bodies (to be replaced by set-box!
  ;;; primcall for set!, and unbox primcall for references of assigned variables).
  ;
  ; (define-language L10
  ;   (terminals
  ;     (symbol (x))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (let ([x* e*] ...) body)
  ;     (letrec ([x* le*] ...) body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (e e* ...))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) body)))
  ;
  (define-language L10
    (extends L9)
    (terminals
      (- (symbol (x a)))
      (+ (symbol (x))))
    (Expr (e body)
      (- (let ([x* e*] ...) abody)
         (set! x e))
      (+ (let ([x* e*] ...) body)))
    (LambdaExpr (le)
      (- (lambda (x* ...) abody))
      (+ (lambda (x* ...) body)))
    (AssignedBody (abody)
      (- (assigned (a* ...) body))))
  
  ;;; Language 11: add a list of free variables to the body of lambda
  ;;; expressions (starting closure conversion code).
  ;
  ; (define-language L11
  ;   (terminals
  ;     (symbol (x f))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (let ([x* e*] ...) body)
  ;     (letrec ([x* le*] ...) body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (e e* ...))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) fbody))
  ;   (FreeBody (fbody)
  ;     (free (f* ...) body)))
  ;
  (define-language L11
    (extends L10)
    (terminals
      (- (symbol (x)))
      (+ (symbol (x f))))
    (LambdaExpr (le)
      (- (lambda (x* ...) body))
      (+ (lambda (x* ...) fbody)))
    (FreeBody (fbody)
      (+ (free (f* ...) body))))

  ;;; Language L12: removes the letrec form and adds closure and labels forms
  ;;; to replace it.  The closure form binds a variable to a label (code
  ;;; pointer) and its set of free variables, and the labels form binds labels
  ;;; (code pointer) to lambda expressions.
  ;
  ; (define-language L12
  ;   (terminals
  ;     (symbol (x f l))
  ;     (constant (c))
  ;     (void+primitive (pr)))
  ;   (Expr (e body)
  ;     (label l)
  ;     (closures ((x* l* f** ...) ...) lbody)
  ;     (let ([x* e*] ...) body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (e e* ...))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) fbody))
  ;   (FreeBody (fbody)
  ;     (free (f* ...) body))
  ;   (LabelsBody (lbody)
  ;     (labels ([l* le*] ...) body)))
  ;
  (define-language L12
    (extends L11)
    (terminals
      (- (symbol (x f)))
      (+ (symbol (x f l))))
    (Expr (e body)
      (- (letrec ([x* le*] ...) body))
      (+ (closures ([x* l* f** ...] ...) lbody)
         (label l)))
    (LabelsBody (lbody)
      (+ (labels ([l* le*] ...) body))))

  ;;; Language 13: finishes closure conversion, removes the closures form,
  ;;; replacing it with primitive calls to deal with closure objects, and
  ;;; raises the labels from into the Expr non-terminal.
  ;
  ; (define-language L13
  ;   (terminals
  ;     (closure+void+primitive (pr))
  ;     (symbol (x f l))
  ;     (constant (c)))
  ;   (Expr (e body)
  ;     (labels ([l* le*] ...) body)
  ;     (label l)
  ;     (let ([x* e*] ...) body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (e e* ...))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) body)))
  ;
  (define-language L13
    (extends L12)
    (terminals
      (- (void+primitive (pr)))
      (+ (closure+void+primitive (pr))))
    (Expr (e body)
      (- (closures ([x* l* f** ...] ...) lbody))
      (+ (labels ([l* le*] ...) body)))
    (LabelsBody (lbody)
      (- (labels ([l* le*] ...) body)))
    (LambdaExpr (le)
      (- (lambda (x* ...) fbody))
      (+ (lambda (x* ...) body)))
    (FreeBody (fbody)
      (- (free (f* ...) body))))

  ;;; Language 14: removes labels form from the Expr nonterminal and puts a
  ;;; single labels form at the top.  Essentially this raises all of our
  ;;; closure  converted functions to the top.
  ;
  ; (define-language L14
  ;   (entry Program)
  ;   (terminals
  ;     (closure+void+primitive (pr))
  ;     (symbol (x f l))
  ;     (constant (c)))
  ;   (Expr (e body)
  ;     (label l)
  ;     (let ([x* e*] ...) body)
  ;     (quote c)
  ;     (primcall pr e* ...)
  ;     x
  ;     (if e0 e1 e2)
  ;     (begin e* ... e)
  ;     (e e* ...))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) body))
  ;   (Program (p)
  ;     (labels ([l* le*] ...) l)))
  ;
  (define-language L14
    (extends L13)
    (entry Program)
    (Program (p)
      (+ (labels ([l* le*] ...) l)))
    (Expr (e body)
      (- (labels ([l* le*] ...) body))))

  ;;; Language 15: moves simple expressions (constants and variable references)
  ;;; out of the Expr nonterminal, and replaces expressions referred to in
  ;;; calls and primcalls with simple expressions.  This effectively removes
  ;;; complex operands to calls and primcalls.
  ;
  ; (define-language L15
  ;   (entry Program)
  ;   (terminals
  ;     (closure+void+primitive (pr))
  ;     (symbol (x f l))
  ;     (constant (c)))
  ;   (Expr (e body)
  ;     (se se* ...)
  ;     (primcall pr se* ...)
  ;     se
  ;     (label l)
  ;     (let ([x* e*] ...) body)
  ;     (if e0 e1 e2)
  ;     (begin e* ... e))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) body))
  ;   (Program (p)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     x
  ;     (quote c)))
  ;
  (define-language L15
    (extends L14)
    (Expr (e body)
      (- x
         (quote c)
         (label l)
         (primcall pr e* ...)
         (e e* ...))
      (+ se
         (primcall pr se* ...) => (pr se* ...)
         (se se* ...)))
    (SimpleExpr (se)
      (+ x
         (label l)
         (quote c))))
  
  ;;; Language 16: separates the Expr nonterminal into the Value, Effect, and
  ;;; Predicate nonterminals.  This is needed to translate from our expression
  ;;; language into a language like C that has statements (effects) and
  ;;; expressions (values) and predicates that need to be simply values.
  (define-language L16
    (terminals
      (symbol (x l))
      (value-primitive (vpr))
      (effect-primitive (epr))
      (predicate-primitive (ppr))
      (constant (c)))
    (Program (prog)
      (labels ([l* le*] ...) l))
    (LambdaExpr (le)
      (lambda (x* ...) body))
    (SimpleExpr (se)
      x
      (label l)
      (quote c))
    (Value (v body)
      se
      (if p0 v1 v2)
      (begin e* ... v)
      (let ([x* v*] ...) body)
      (primcall vpr se* ...) => (vpr se* ...)
      (se se* ...))
    (Effect (e)
      (nop)
      (if p0 e1 e2)
      (begin e* ... e)
      (let ([x* v*] ...) e)
      (primcall epr se* ...) => (epr se* ...)
      (se se* ...))
    (Predicate (p)
      (true)
      (false)
      (if p0 p1 p2)
      (begin e* ... p)
      (let ([x* v*] ...) p)
      (primcall ppr se* ...) => (ppr se* ...)))

  ;;; Language 17: removes the allocation primitives: cons, box, make-vector,
  ;;; and make-closure and adds a generic alloc form for specifying allocation.  It
  ;;; also adds raw integers for specifying type tags in the alloc form.
  ;
  ; (define-language L17
  ;   (entry Program)
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr))
  ;     (constant (c)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) body))
  ;   (SimpleExpr (se)
  ;     x
  ;     (label l)
  ;     (quote c))
  ;   (Value (v body)
  ;     (alloc i se)
  ;     se
  ;     (if p0 v1 v2)
  ;     (begin e* ... v)
  ;     (let ([x* v*] ...) body)
  ;     (primcall vpr se* ...)
  ;     (se se* ...))
  ;   (Effect (e)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (let ([x* v*] ...) e)
  ;     (primcall epr se* ...)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2)
  ;     (begin e* ... p)
  ;     (let ([x* v*] ...) p)
  ;     (primcall ppr se* ...)))
  ;
  (define-language L17
    (extends L16)
    (terminals
      (- (value-primitive (vpr))
         (effect-primitive (epr)))
      (+ (non-alloc-value-primitive (vpr))
         (effect+internal-primitive (epr))
         (integer-64 (i))))
    (Value (v body)
      (+ (alloc i se))))

  ;;; Language L18: removes let forms and replaces them with a top-level locals
  ;;; form that indicates which variables are bound in the function (so they
  ;;; can be listed at the top of our C function) and set! that do simple
  ;;; assignments.
  ;
  ; (define-language L18
  ;   (entry Program)
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr))
  ;     (constant (c)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     x
  ;     (label l)
  ;     (quote c))
  ;   (Value (v body)
  ;     (alloc i se)
  ;     se
  ;     (if p0 v1 v2)
  ;     (begin e* ... v)
  ;     (primcall vpr se* ...)
  ;     (se se* ...))
  ;   (Effect (e)
  ;     (set! x v)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (primcall epr se* ...)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2)
  ;     (begin e* ... p)
  ;     (primcall ppr se* ...))
  ;   (LocalsBody (lbody)
  ;     (locals (x* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) lbody)))
  ;
  (define-language L18
    (extends L17)
    (Value (v body)
      (- (let ([x* v*] ...) body)))
    (Effect (e)
      (- (let ([x* v*] ...) e))
      (+ (set! x v)))
    (Predicate (p)
      (- (let ([x* v*] ...) p)))
    (LambdaExpr (le)
      (- (lambda (x* ...) body))
      (+ (lambda (x* ...) lbody)))
    (LocalsBody (lbody)
      (+ (locals (x* ...) body))))

  ;;; Language 19: simplify the right-hand-side of a set! so that it can
  ;;; contain, simple expression, allocations, primcalls, and function calls,
  ;;; but not ifs, or begins.
  ;
  ; (define-language L19
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr))
  ;     (constant (c)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     x
  ;     (label l)
  ;     (quote c))
  ;   (Value (v body)
  ;     rhs
  ;     (if p0 v1 v2)
  ;     (begin e* ... v))
  ;   (Effect (e)
  ;     (set! x rhs)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (primcall epr se* ...)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2)
  ;     (begin e* ... p)
  ;     (primcall ppr se* ...))
  ;   (LocalsBody (lbody)
  ;     (locals (x* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) lbody))
  ;   (Rhs (rhs)
  ;     se
  ;     (alloc i se)
  ;     (primcall vpr se* ...)
  ;     (se se* ...)))
  ;
  (define-language L19
    (extends L18)
    (Value (v body)
      (- se
         (alloc i se)
         (primcall vpr se* ...)
         (se se* ...))
      (+ rhs))
    (Rhs (rhs)
      (+ se
         (alloc i se)
         (primcall vpr se* ...) => (vpr se* ...)
         (se se* ...)))
    (Effect (e)
      (- (set! x v))
      (+ (set! x rhs))))

  ;;; Language L20: remove begin from the predicate production (effectively
  ;;; forcing the if to only have if, true, false, and predicate primitive
  ;;; calls).
  ;;; TODO: removed this language because our push-if pass was buggy, and
  ;;;       fixing it requires us to flatten code into something like
  ;;;       basic blocks, and we can avoid doing this since our target
  ;;;       is C.  We could revisit it for other backend targets.
  ;
  ; (define-language L20
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr))
  ;     (constant (c)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     x
  ;     (label l)
  ;     (quote c))
  ;   (Value (v body)
  ;     rhs
  ;     (if p0 v1 v2)
  ;     (begin e* ... v))
  ;   (Effect (e)
  ;     (set! x rhs)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (primcall epr se* ...)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2)
  ;     (primcall ppr se* ...))
  ;   (LocalsBody (lbody)
  ;     (locals (x* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) lbody))
  ;   (Rhs (rhs)
  ;     se
  ;     (alloc i se)
  ;     (primcall vpr se* ...)
  ;     (se se* ...)))
  ;
  ; (define-language L20
  ;   (extends L19)
  ;   (Predicate (p)
  ;     (- (begin e* ... p))))

  ;;; Language 21: remove quoted constants and replace it with our raw ptr
  ;;; representation (i.e. 64-bit integers)
  ;
  ; (define-language L21
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     i
  ;     x
  ;     (label l))
  ;   (Value (v body)
  ;     rhs
  ;     (if p0 v1 v2)
  ;     (begin e* ... v))
  ;   (Effect (e)
  ;     (set! x rhs)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (primcall epr se* ...)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2)
  ;     (primcall ppr se* ...))
  ;   (LocalsBody (lbody)
  ;     (locals (x* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) lbody))
  ;   (Rhs (rhs)
  ;     se
  ;     (alloc i se)
  ;     (primcall vpr se* ...)
  ;     (se se* ...)))
  ;
  (define-language L21
    (extends L19)
    (terminals
      (- (constant (c))))
    (SimpleExpr (se)
      (- (quote c))
      (+ i)))

  ;;; Language 22: remove the primcalls and replace them with mref (memory
  ;;; references), add, subtract, multiply, divide, shift-right, shift-left,
  ;;; logand, mset! (memory set), =, <, and <=.
  ;;;
  ;;; TODO: we should probably replace this with "machine" instructions
  ;;; instead, so that we can more easily extend the language and generate C
  ;;; code from it.
  ;
  ; (define-language L22
  ;   (terminals
  ;     (integer-64 (i))
  ;     (effect+internal-primitive (epr))
  ;     (non-alloc-value-primitive (vpr))
  ;     (symbol (x l))
  ;     (predicate-primitive (ppr)))
  ;   (Program (prog)
  ;     (labels ([l* le*] ...) l))
  ;   (SimpleExpr (se)
  ;     (logand se0 se1)
  ;     (shift-left se0 se1)
  ;     (shift-right se0 se1)
  ;     (divide se0 se1)
  ;     (multiply se0 se1)
  ;     (subtract se0 se1)
  ;     (add se0 se1)
  ;     (mref se0 (maybe se1?) i)
  ;     i
  ;     x
  ;     (label l))
  ;   (Value (v body)
  ;     rhs
  ;     (if p0 v1 v2)
  ;     (begin e* ... v))
  ;   (Effect (e)
  ;     (mset! se0 (maybe se1?) i se2)
  ;     (set! x rhs)
  ;     (nop)
  ;     (if p0 e1 e2)
  ;     (begin e* ... e)
  ;     (se se* ...))
  ;   (Predicate (p)
  ;     (<= se0 se1)
  ;     (< se0 se1)
  ;     (= se0 se1)
  ;     (true)
  ;     (false)
  ;     (if p0 p1 p2))
  ;   (LocalsBody (lbody)
  ;     (locals (x* ...) body))
  ;   (LambdaExpr (le)
  ;     (lambda (x* ...) lbody))
  ;   (Rhs (rhs)
  ;     se
  ;     (alloc i se)
  ;     (se se* ...)))
  ;
  (define-language L22
    (extends L21)
    (Rhs (rhs)
      (- (primcall vpr se* ...)))
    (SimpleExpr (se)
      (+ (mref se0 (maybe se1?) i)
         (add se0 se1)
         (subtract se0 se1)
         (multiply se0 se1)
         (divide se0 se1)
         (shift-right se0 se1)
         (shift-left se0 se1)
         (logand se0 se1)))
    (Effect (e)
      (- (primcall epr se* ...))
      (+ (mset! se0 (maybe se1?) i se2)))
    (Predicate (p)
      (- (primcall ppr se* ...))
      (+ (= se0 se1)
         (< se0 se1)
         (<= se0 se1))))

  ;;;;;;;;;
  ;;; beginning of our pass listings

  ;;; pass: parse-and-rename : S-expression -> Lsrc (or error)
  ;;; 
  ;;; parses an S-expression, and, if it conforms to the input language,
  ;;; renames the local variables to be represented with a unique variable.
  ;;; This helps us to separate keywords from varialbes and recognize one
  ;;; variable binding as different from another.  This step is also called
  ;;; alpha-renaming or alpha-conversion.  The output will be in the Lsrc
  ;;; language forms, represented as records.
  ;;;
  ;;; Some design decisions here:  We could have decided to have this pass
  ;;; remove one-armed ifs, remove and, or, and not, setup begins in the body
  ;;; of our letrec, let, and lambda, and potentially quoted constants and
  ;;; eta-expanded raw primitives, rather than doing each of these as separate
  ;;; passes.  I have not done this here, primarily for educational reasons,
  ;;; since these simple passes are a gentle introduction to how the passes are
  ;;; written.
  ;;;
  (define-pass parse-and-rename : * (e) -> Lsrc ()
    ;;; Helper functions for this pass.
    (definitions
      ;;; process-body - used to process the body of begin, let, letrec, and
      ;;; lambda expressions.  since all four of these have the same pattern in
      ;;; the body.
      (define process-body
        (lambda (who env body* f)
          (when (null? body*) (error who "invalid empty body"))
          (let loop ([body (car body*)] [body* (cdr body*)] [rbody* '()])
            (if (null? body*)
                (f (reverse rbody*) (Expr body env))
                (loop (car body*) (cdr body*)
                  (cons (Expr body env) rbody*))))))
      ;;; vars-unique? - processes the list of bindings to make sure all of the
      ;;; variable names are different (i.e. we don't want to allow
      ;;; (lambda (x x) x), since we would not know which x is which).
      (define vars-unique?
        (lambda (fmls)
          (let loop ([fmls fmls])
            (or (null? fmls)
                (and (not (memq (car fmls) (cdr fmls)))
                     (loop (cdr fmls)))))))
      ;;; unique-vars - builds a list of unique variables based on a set of
      ;;; formals and extends the environment.  it takes a function as an
      ;;; argument (effectively a continuation), and passes it the updated
      ;;; environment and a list of unique variables.
      (define unique-vars
        (lambda (env fmls f)
          (unless (vars-unique? fmls)
            (error 'unique-vars "invalid formals" fmls))
          (let loop ([fmls fmls] [env env] [rufmls '()])
            (if (null? fmls)
                (f env (reverse rufmls))
                (let* ([fml (car fmls)] [ufml (unique-var fml)])
                  (loop (cdr fmls) (cons (cons fml ufml) env)
                    (cons ufml rufmls)))))))
      ;;; process-bindings - processes the bindings of a let or letrec and
      ;;; produces bindings for unique variables for each of the original
      ;;; variables.  it also processes the right-hand sides of the variable
      ;;; bindings and selects either the original environment (for let) or the
      ;;; updated environment (for letrec).
      (define process-bindings
        (lambda (rec? env bindings f)
          (let loop ([bindings bindings] [rfml* '()] [re* '()])
            (if (null? bindings)
                (unique-vars env rfml*
                  (lambda (new-env rufml*)
                    (let ([env (if rec? new-env env)])
                      (let loop ([rufml* rufml*]
                                 [re* re*]
                                 [ufml* '()]
                                 [e* '()])
                        (if (null? rufml*)
                            (f new-env ufml* e*)
                            (loop (cdr rufml*) (cdr re*)
                              (cons (car rufml*) ufml*)
                              (cons (Expr (car re*) env) e*)))))))
                (let ([binding (car bindings)])
                  (loop (cdr bindings) (cons (car binding) rfml*)
                    (cons (cadr binding) re*)))))))
      ;;; Expr* - helper to process a list of expressions.
      (define Expr*
        (lambda (e* env)
          (map (lambda (e) (Expr e env)) e*)))
      ;;; with-output-language rebinds quasiquote so that it will build
      ;;; language records.
      (with-output-language (Lsrc Expr)
        ;;; build-primitive - this is a helper function to build entries in the
        ;;; initial environment for our user primitives.  the initial
        ;;; enviornment contains a mapping of keywords and primitives to
        ;;; processing functions that check their arity (in the case of
        ;;; primitives) or their forms (in the case of keywords).  These are
        ;;; put into an environment, because keywords and primitives can be
        ;;; rebound.  (i.e. (lambda (lambda) (lambda lambda)) is a perfectly
        ;;; valid function in Scheme that takes a function as an argument and
        ;;; applies the argument to itself).
        (define build-primitive
          (lambda (as)
            (let ([name (car as)] [argc (cdr as)])
              (cons name
                (if (< argc 0)
                    (error who
                      "primitives with arbitrary counts are not currently supported"
                      name)
                    ;;; we'd love to support arbitrary argument lists, but we'd
                    ;;; need to either:
                    ;;;   1. get rid of raw primitives, or
                    ;;;   2. add function versions of our raw primitives with
                    ;;;      arbitrary arguments, or (possibly and)
                    ;;;   3. add general handling for functions with arbitrary
                    ;;;      arguments. (i.e. support for (lambda args <body>)
                    ;;;      or (lambda (x y . args) <body>), which we don't
                    ;;;      currently support.
                    #;(let ([argc (bitwise-not argc)])
                      (lambda (env . e*)
                        (if (>= (length e*) argc)
                            `(,name ,(Expr* e* env) ...)
                            (error name "invalid argument count"
                              (cons name e*)))))
                    (lambda (env . e*)
                      (if (= (length e*) argc)
                          `(,name ,(Expr* e* env) ...)
                          (error name "invalid argument count"
                            (cons name e*)))))))))
        ;;; initial-env - this is our initial environment, expressed as an
        ;;; association list of keywords and primitives (represented as
        ;;; symbols) to procedure handlers (represented as procedures).  As the
        ;;; program is processed through this pass, it will be extended with
        ;;; local bidings from variables (represented as symbols) to unique
        ;;; variables (represented as symbols with a format of symbol.number).
        (define initial-env
          (cons*
            (cons 'quote (lambda (env d)
                           (unless (datum? d)
                             (error 'quote "invalid datum" d))
                           `(quote ,d)))
            (cons 'if (case-lambda
                        [(env e0 e1) `(if ,(Expr e0 env) ,(Expr e1 env))]
                        [(env e0 e1 e2)
                         `(if ,(Expr e0 env) ,(Expr e1 env) ,(Expr e2 env))]
                        [x (error 'if (if (< (length x) 3)
                                          "too few arguments"
                                          "too many arguments")
                             x)]))
            (cons 'or (lambda (env . e*) `(or ,(Expr* e* env) ...)))
            (cons 'and (lambda (env . e*) `(and ,(Expr* e* env) ...)))
            (cons 'not (lambda (env e) `(not ,(Expr e env))))
            (cons 'begin (lambda (env . e*)
                           (process-body 'begin env e*
                             (lambda (e* e)
                               `(begin ,e* ... ,e)))))
            (cons 'lambda (lambda (env fmls . body*)
                            (unique-vars env fmls
                              (lambda (env fmls)
                                (process-body 'lambda env body*
                                  (lambda (body* body)
                                    `(lambda (,fmls ...)
                                       ,body* ... ,body)))))))
            (cons 'let (lambda (env bindings . body*)
                         (process-bindings #f env bindings
                           (lambda (env x* e*)
                             (process-body 'let env body*
                               (lambda (body* body)
                                 `(let ([,x* ,e*] ...) ,body* ... ,body)))))))
            (cons 'letrec (lambda (env bindings . body*)
                            (process-bindings #t env bindings
                              (lambda (env x* e*)
                                (process-body 'letrec env body*
                                  (lambda (body* body)
                                    `(letrec ([,x* ,e*] ...)
                                       ,body* ... ,body)))))))
            (cons 'set! (lambda (env x e)
                          (cond
                            [(assq x env) =>
                             (lambda (as)
                               (let ([v (cdr as)])
                                 (if (symbol? v)
                                     `(set! ,v ,(Expr e env))
                                     (error 'set! "invalid syntax"
                                       (list 'set! x e)))))]
                            [else (error 'set! "set to unbound variable"
                                    (list 'set! x e))])))
            (map build-primitive user-prims)))
        ;;; App - helper for handling applications.
        (define App
          (lambda (e env)
            (let ([e (car e)] [e* (cdr e)])
              `(,(Expr e env) ,(Expr* e* env) ...))))))
    ;;; transformer: Expr: S-expression -> LSrc:Expr (or error)
    ;;;
    ;;; parses an S-expression, looking for a pair (which indicates, a
    ;;; keyword use, a primitive call, or a normal function call), a symbol
    ;;; (which indicates a variable reference or a primitive reference), or one of
    ;;; our constants (which indicates a raw constant).
    (Expr : * (e env) -> Expr ()
      (cond
        [(pair? e)
         (cond
           [(assq (car e) env) =>
            (lambda (as)
              (let ([v (cdr as)])
                (if (procedure? v)
                    (apply v env (cdr e))
                    (App e env))))]
           [else (App e env)])]
        [(symbol? e)
         (cond
           [(assq e env) =>
            (lambda (as)
              (let ([v (cdr as)])
                (cond
                  [(symbol? v) v]
                  [(primitive? e) e]
                  [else (error who "invalid syntax" e)])))]
           [else (error who "unbound variable" e)])]
        [(constant? e) e]
        [else (error who "invalid expression" e)]))
    ;;; kick off processing the S-expression by handing Expr our initial
    ;;; S-expression and the initial environment.
    (Expr e initial-env))
  
  ;;; pass: remove-one-armed-if : Lsrc -> L1
  ;;;
  ;;; this pass replaces the (if e0 e1) form with an if that will explicitly
  ;;; produce a void value when the predicate expression returns false. In
  ;;; other words:
  ;;; (if e0 e1) => (if e0 e1 (void))
  ;;;
  ;;; Design descision: kept seperate from parse-and-rename to make it easier
  ;;; to understand how the nanopass framework can be used.
  ;;;
  (define-pass remove-one-armed-if : Lsrc (e) -> L1 ()
    (Expr : Expr (e) -> Expr ()
      [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))
  
  ;;; pass: remove-and-or-not : L1 -> L2
  ;;;
  ;;; this pass looks for references to and, or, and not and replaces it with
  ;;; the appropriate if expressions.  this pass follows the standard
  ;;; expansions and has one small optimization:
  ;;;
  ;;; (if (not e0) e1 e2) => (if e0 e2 e1)           [optimization]
  ;;; (and)               => #t                      [from Scheme standard]
  ;;; (or)                => #f                      [from Scheme standard]
  ;;; (and e e* ...)      => (if e (and e* ...) #f)  [standard expansion]
  ;;; (or e e* ...)       => (let ([t e])            [standard expansion -
  ;;;                          (if t t (or e* ...)))  avoids computing e twice]
  ;;;
  ;;; Design decision: again kept separate from parse-and-rename to simplify
  ;;; the discussion of this pass (adding it to parse-and-rename doesn't really
  ;;; make parse-and-rename much more complicated, and if we had a macro
  ;;; system, which would likely be implemented in parse-and-rename, or before
  ;;; it, we would probably want and, or, and not defined as macros, rather
  ;;; than forms in the language, in which case this pass would be
  ;;; unnecessary).
  ;;;
  (define-pass remove-and-or-not : L1 (e) -> L2 ()
    (Expr : Expr (e) -> Expr ()
      [(if (not ,[e0]) ,[e1] ,[e2]) `(if ,e0 ,e2 ,e1)]
      [(not ,[e0]) `(if ,e0 #f #t)]
      [(and) #t]
      [(and ,[e] ,[e*] ...)
       ;; tiny inline loop (not tail recursive, so called f instead of loop)
       (let f ([e e] [e* e*])
         (if (null? e*)
             e
             `(if ,e ,(f (car e*) (cdr e*)) #f)))]
      [(or) #f]
      [(or ,[e] ,[e*] ...)
       ;; tiny inline loop (not tail recursive, so called f instead of loop)
       (let f ([e e] [e* e*])
         (if (null? e*)
             e
             (let ([t (make-tmp)])
               `(let ([,t ,e]) (if ,t ,t ,(f (car e*) (cdr e*)))))))]))

  ;;; pass: make-being-explicit : L2 -> L3
  ;;;
  ;;; this pass takes the L2 let, letrec, and lambda expressions (which have
  ;;; bodies that can contain more than one expression), and converts them into
  ;;; bodies with a single expression, wrapped in a begin if necessary.  To
  ;;; avoid polluting the output with extra begins that contain only one
  ;;; expression the build-begin helper checks to see if there is more then one
  ;;; expression and if there is builds a begin.
  ;;;
  ;;; Effectively this does the following:
  ;;; (let ([x* e*] ...) body0 body* ... body1) =>
  ;;;   (let ([x* e*] ...) (begin body0 body* ... body1))
  ;;; (letrec ([x* e*] ...) body0 body* ... body1) =>
  ;;;   (letrec ([x* e*] ...) (begin body0 body* ... body1))
  ;;; (lambda (x* ...) body0 body* ... body1) =>
  ;;;   (lambda (x* ...) (begin body0 body* ... body1))
  ;;;
  ;;; Design Decision: This could have been included with rename-and-parse,
  ;;; without making it significantly more compilicated, but was separated out
  ;;; to continue with simpler nanopass passes to help make it more obvious
  ;;; what is going on here.
  ;;;
  (define-pass make-begin-explicit : L2 (e) -> L3 ()
    (Expr : Expr (e) -> Expr ()
      ;;; Note: the defitions are within the body of the Expr transformer
      ;;; instead of being within the body of the pass.  This means the
      ;;; quasiquote is bound to the Expr form, and we don't need to use
      ;;; with-output-language.
      (definitions
        ;;; build-begin - helper function to build a begin only when the body
        ;;; contains more then one expression.  (this version of the helper
        ;;; is a little over-kill, but it makes our traces look a little 
        ;;; cleaner.  there should be a simpler way of doing this.)
        (define build-begin
          (lambda (e* e)
            (nanopass-case (L3 Expr) e
              [(begin ,e1* ... ,e) 
               (build-begin (append e* e1*) e)]
              [else
               (if (null? e*)
                   e
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,e)
                         (let ([e (car e*)])
                           (nanopass-case (L3 Expr) e
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(let ([,x* ,[e*]] ...) ,[body*] ... ,[body])
       `(let ([,x* ,e*] ...) ,(build-begin body* body))]
      [(letrec ([,x* ,[e*]] ...) ,[body*] ... ,[body])
       `(letrec ([,x* ,e*] ...) ,(build-begin body* body))]
      [(lambda (,x* ...) ,[body*] ... ,[body])
       `(lambda (,x* ...) ,(build-begin body* body))]))

  ;;; pass : inverse-eta-raw-primitives : L3 -> L4
  ;;;
  ;;; Eta reduction recognizes a function that takes a set of arguments and
  ;;; passes those arguments directly to another function, and unwraps the
  ;;; function.  For instance, the function:
  ;;;   (lambda (x y) (f x y))
  ;;; can be eta reduced to:
  ;;;   f
  ;;; Eta reduction is not always a semantics preserving transformation because
  ;;; it can change the termination properties of the program, for instance a
  ;;; program that terminates, could turn into one that does not because a
  ;;; function is applied directly, rather than a function that might never be
  ;;; applied.
  ;;;
  ;;; In this pass, we are applying the inverse operation and adding a lambda
  ;;; wrapper when we see a primitive.  We do this so that primitives, which we
  ;;; are going to open code into a C-code equivalent, can still be treated as
  ;;; though it was a Scheme procedure.  This allows us to map over primitives,
  ;;; which would otherwise not be possible with our code generation.  Our
  ;;; transformation looks for primitives in call position, marking them as
  ;;; primitive calls, and primitives not in call position are eta-expanded to move
  ;;; them into call position.
  ;;;
  ;;; (pr e* ...) => (primcall pr e* ...)
  ;;; pr          => (lambda (x* ...) (primcall pr x* ...))
  ;;; 
  ;;; Design decision: Another way to handle this would be to create a single
  ;;; function for each primitive, and lift these definitions to the top-level
  ;;; of the program, including just those primitives that are used.  This
  ;;; would avoid the potential to re-creating the same procedure over and over
  ;;; again, as we are now.
  ;;; 
  (define-pass inverse-eta-raw-primitives : L3 (e) -> L4 ()
    (Expr : Expr (e) -> Expr ()
      [(,pr ,[e*] ...) `(primcall ,pr ,e* ...)]
      [,pr (cond
             [(assq pr void+user-prims) =>
              (lambda (as)
                (do ((i (cdr as) (fx- i 1))
                     (x* '() (cons (make-tmp) x*)))
                  ((fx=? i 0) `(lambda (,x* ...) (primcall ,pr ,x* ...)))))]
             [else (error who "unexpected primitive" pr)])]))

  ;;; pass: quote-constants : L4 -> L5
  ;;;
  ;;; A simple pass to find raw constants and wrap them in a quote.
  ;;; c => (quote c)
  ;;;
  ;;; Design decision: This could simply be included in the next pass.
  ;;;
  (define-pass quote-constants : L4 (e) -> L5 ()
    (Expr : Expr (e) -> Expr ()
      [,c `(quote ,c)]))

  ;;; pass: remove-complex-constants : L5 -> L6
  ;;;
  ;;; Lifts creation of constants composed of vectors or pairs outside the body
  ;;; of the program and makes their creation explicit.  In place of the
  ;;; constants, a temporary variable reference is created.  The total
  ;;; transform looks something like the following:
  ;;;
  ;;; (letrec ([add-pair-parts (lambda (p) (+ (car p) (cdr p)))])
  ;;;   (+ (add-pair-parts '(4 . 5)) (add-pair-parts '(6 .7)))) =>
  ;;; (let ([t0 (cons 4 5)] [t1 (cons 6 7)])
  ;;;   (letrec ([add-pair-parts (lambda (p) (+ (car p) (cdr p)))])
  ;;;     (+ (add-pair-parts t0) (add-pair-parts t1))))
  ;;;
  ;;; Design decision: Another possibility is to simply convert the constants
  ;;; into their memory-layed out variations, rather than treating it in pieces
  ;;; like this.  We could extend our C run-time support to know about these
  ;;; pre-layed out items so that we do not need to construct them when the
  ;;; program starts running.
  ;;;
  (define-pass remove-complex-constants : L5 (e) -> L6 ()
    (definitions
      ;;; t* and e* used to gather up our final constant bindings (via set!)
      (define t* '())
      (define e* '()))
    (Expr : Expr (e) -> Expr ()
      (definitions
        ;;; datum->expr - a helper function for recurring through the parts of
        ;;; a vector or pair datum to construct its parts, until it reaches the
        ;;; constants in the leaves of the datum.  We put this definition
        ;;; within the Expr transformer so that quasiquote will be bound to the
        ;;; L6:Expr nonterminal creation code.
        (define datum->expr
          (lambda (x)
            (cond
              [(pair? x)  ;; if we have a pair, cons its recurred parts.
               `(primcall cons ,(datum->expr (car x)) ,(datum->expr (cdr x)))]
              [(vector? x) ;; if we have a vector ...
               (let ([l (vector-length x)] [t (make-tmp)])
                 ;; 1. create a vector of the proper size
                 `(let ([,t (primcall make-vector (quote ,l))])
                    (begin
                      ;; 2. set each elemenet in the vector with its recurred
                      ;;    parts.
                      ,(let loop ([l l] [e* '()])
                         (if (fx=? l 0)
                             e*
                             (let ([l (fx- l 1)])
                               (loop l
                                 (cons 
                                   `(primcall vector-set! ,t
                                      (quote ,l)
                                      ,(datum->expr (vector-ref x l)))
                                   e*)))))
                      ...
                      ;; and return the vector as the final expression
                      ,t)))]
              ;; if it is a constant, simply quote it.
              [(constant? x) `(quote ,x)]))))
      [(quote ,d)                    ;; look for quoted constants
       (if (constant? d)             ;; if they are already simple
           `(quote ,d)               ;; quote them
           (let ([t (make-tmp)])     ;; otherwise create a binding for them
             (set! t* (cons t t*))
             (set! e* (cons (datum->expr d) e*))
             t))])
    ;; in the body, call the Expr transformer, and if t* is null (indicating we
    ;; did not find any complex constants) don't bother creating the empty let
    ;; around it.
    (let ([e (Expr e)])
      (if (null? t*)
          e
          `(let ([,t* ,e*] ...) ,e))))

  ;;; pass: identify-assigned-variables : L6 -> L7
  ;;;
  ;;; This pass identifies which variables are assigned using set!. This is the
  ;;; first step in a process known as assignment conversion.  We separate
  ;;; assigned varaibles from unassigned variables, and assigned variables are
  ;;; converted into reference cells that can be manipulated through
  ;;; primitives.  In this compiler, we use the existing box type to create the
  ;;; cells (using the box primitive), reference the cells (using the unbox
  ;;; primitive), and mutating the cells (using the set-box! primitive).  One
  ;;; of the reasons we perform assignment conversion is it allows multiple
  ;;; closures to capture the same mutable variable and all of the closures
  ;;; will see the same, up-to-date, value for that variable since they all
  ;;; simply contain a pointer to the reference cell.  If we didn't do this
  ;;; conversion, we would need to figure out a different way to handle set! so
  ;;; that the updates are propagated to all the closures that close over the
  ;;; variable.  The eventual effect of assignemnt conversion is the following:
  ;;; (let ([x 5])
  ;;;   (set! x (+ x 5))
  ;;;   (+ x x)) =>
  ;;; (let ([t0 5])
  ;;;   (let ([x (box t0)])
  ;;;     (primcall set-box! x (+ (unbox x) 5)
  ;;;     (+ (unbox x) (unbox x))))
  ;;; (of course in this example, we could have simply shadowed x)
  ;;;
  ;;; This pass, however, is simply an analysis pass.  It gathers up the set of
  ;;; assigned variables and deposits them in an AssignedBody just inside their
  ;;; binding points.  The transformation in this pass is:
  ;;;
  ;;; (let ([x 5] [y 7] [z 10])
  ;;;   (set! x (+ x y))
  ;;;   (+ x z)) =>
  ;;; (let ([x 5] [y 7] [z 10])
  ;;;   (assigned (x)
  ;;;     (set! x (+ x y))
  ;;;     (+ x z)))
  ;;;
  ;;; The key operations we depend on are:
  ;;; set-cons   - to extend a set with a newly found assigned variable.
  ;;; intersect  - to determine which assigned variables are bound by a lambda,
  ;;;              let, or letrec.
  ;;; difference - to remove assigned variables from a set once we locate their
  ;;;              binding form.
  ;;; union      - to gather assigned variables from sub-expressions into a
  ;;;              single set.
  ;;; 
  ;;; Note: we are using a relatively inefficient representation of sets here,
  ;;; simply representing them as lists and using our set-cons, intersect,
  ;;; difference, and union procedures to maintain their set-ness.  We could
  ;;; choose a more efficient set representation, perhaps leveraging insertion
  ;;; sort or something similar, or we could choose to represent our variables
  ;;; using a mutable record, with a field to indicate if it is assigned.
  ;;; Either approach will improve the worst case performance of this pass,
  ;;; though the mutable record version will get us down to a linear cost,
  ;;; which is the best case for any pass in the current version of the
  ;;; nanopass framework.
  ;;;
  (define-pass identify-assigned-variables : L6 (e) -> L7 ()
    (Expr : Expr (e) -> Expr ('())
      ;; identify an assigned variable
      [(set! ,x ,[e assigned*]) (values `(set! ,x ,e) (set-cons x assigned*))]
      ;; deposit assigned variables at lambda, let, and letrec binding sites
      [(lambda (,x* ...) ,[body assigned*])
       (values
         `(lambda (,x* ...) (assigned (,(intersect x* assigned*) ...) ,body))
         (difference assigned* x*))]
      [(let ([,x* ,[e* assigned**]] ...) ,[body assigned*])
       (values
         `(let ([,x* ,e*] ...)
            (assigned (,(intersect x* assigned*) ...) ,body))
         (apply union (difference assigned* x*) assigned**))]
      [(letrec ([,x* ,[e* assigned**]] ...) ,[body assigned*])
       (let ([assigned* (apply union assigned* assigned**)])
         (values
           `(letrec ([,x* ,e*] ...)
              (assigned (,(intersect x* assigned*) ...) ,body))
           (difference assigned* x*)))]
      ;; traverse forms with nested expressions to gather up the assignments
      ;; from each sub-expression.  this could be simplified if the nanopass
      ;; framework had a way to automatically combine these.
      [(primcall ,pr ,[e* assigned**] ...)
       (values `(primcall ,pr ,e* ...) (apply union assigned**))]
      [(if ,[e0 assigned0*] ,[e1 assigned1*] ,[e2 assigned2*])
       (values `(if ,e0 ,e1 ,e2) (union assigned0* assigned1* assigned2*))]
      [(begin ,[e* assigned**] ... ,[e assigned*])
       (values `(begin ,e* ... ,e) (apply union assigned* assigned**))]
      [(,[e assigned*] ,[e* assigned**] ...)
       (values `(,e ,e* ...) (apply union assigned* assigned**))])
    ;; in the body, call 
    (let-values ([(e assigned*) (Expr e)])
      (unless (null? assigned*)
        (error who "found one or more unbound variables" assigned*))
      e))

  ;;; pass: purify-letrec : L7 -> L8
  ;;;
  ;;; this pass looks for places where letrec is used to bind something other
  ;;; than a lambda expression, or where a letrec bound variable is assigned
  ;;; and moves these bindings into let bindings.  when the pass is done all of
  ;;; the letrecs in our program will be immutable and bind only lambda
  ;;; expressions. For instance, the following example:
  ;;;
  ;;; (letrec ([f (lambda (g x) (g x))]
  ;;;          [a 5]
  ;;;          [b (+ 5 7)]
  ;;;          [g (lambda (h) (f h 5))]
  ;;;          [c (let ([x 10]) ((letrec ([zero? (lambda (n) (= n 0))]
  ;;;                                     [f (lambda (n) 
  ;;;                                          (if (zero? n)
  ;;;                                              1
  ;;;                                              (* n (f (- n 1)))))])
  ;;;                              f)
  ;;;                             x))]
  ;;;          [m 10]
  ;;;          [z (lambda (x) x)])
  ;;;   (set! z (lambda (x) (+ x x)))
  ;;;   (set! m (+ m m))
  ;;;   (+ (+ (+ (f z a) (f z b)) (f z c)) (g z))))
  ;;; =>
  ;;; (let ([z (quote #f)] [m '#f] [c '#f])
  ;;;   (let ([b (+ '5 '7)] [a '5])
  ;;;     (letrec ([g (lambda (h) (f h '5))]
  ;;;              [f (lambda (g x) (g x))])
  ;;;       (begin
  ;;;         (set! z (lambda (x) x))
  ;;;         (set! m '10)
  ;;;         (set! c
  ;;;           (let ([x '10])
  ;;;             ((letrec ([f (lambda (n)
  ;;;                               (if (zero? n)
  ;;;                                   '1
  ;;;                                   (* n (f (- n '1)))))]
  ;;;                       [zero? (lambda (n) (= n '0))])
  ;;;                f)
  ;;;               x)))
  ;;;         (begin
  ;;;           (set! z (lambda (x) (+ x x)))
  ;;;           (set! m (+ m m))
  ;;;           (+ (+ (+ (f z a) (f z b)) (f z c)) (g z)))))))
  ;;; 
  ;;; The algorithm for doing this is fairly simple.  We attempt to separate
  ;;; the bindings into simple bindings, lambda bindings, and complex bindings.
  ;;; Simple bindings bind a constant, a variable reference not bound in this
  ;;; letrec, the call to an effect free primitive, a begin that contains only
  ;;; simple expressions, or an if that contains only simple expressions to an
  ;;; immutable variable. The simple? predicate is used for determining when an
  ;;; expression is simple.  A lambda expression is simply a lambda, and a
  ;;; complex expression is any other expression.
  ;;;
  ;;; Design decision: There are many other approaches that we could use,
  ;;; including those described in the "Fixing Letrec: A Faithful Yet Efficient
  ;;; Implementation of Scheme’s Recursive Binding Construct" by Waddell, et.
  ;;; al. and "Fixing Letrec (reloaded)" by Ghuloum and Dybvig.  Earlier
  ;;; versions of Chez Scheme used the earlier paper, which documented how to
  ;;; properly handle R5RS letrecs, and newer versions use the latter paper
  ;;; which described how to properly handle R6RS letrec and letrec*.
  ;;;
  (define-pass purify-letrec : L7 (e) -> L8 ()
    (definitions
      ;; lambda? - use nanopass case to determine if an L8:Expr is a lambda
      ;; expression.
      (define lambda?
        (lambda (e)
          (nanopass-case (L8 Expr) e
            [(lambda (,x* ...) ,abody) #t]
            [else #f])))
      ;; simple? - use nanopass case to deteremin if an L8:Expr is a "simple",
      ;; effect free expression.
      (define simple?
        (lambda (x bound* assigned*)
          (let f ([x x])
            (nanopass-case (L8 Expr) x
              [(quote ,c) #t]
              [,x (not (or (memq x bound*) (memq x assigned*)))]
              [(primcall ,pr ,e* ...)
                (and (effect-free-prim? pr) (for-all f e*))]
              [(begin ,e* ... ,e) (and (for-all f e*) (f e))]
              [(if ,e0 ,e1 ,e2) (and (f e0) (f e1) (f e2))]
              [else #f])))))
    (Expr : Expr (e) -> Expr ()
      (definitions
        ;; build a let, when there are bindings, otherwise, just return the
        ;; body.
        (define build-let
          (lambda (x* e* a* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) (assigned (,a* ...) ,body)))))
        ;; build a letrec, when there are bindings, otherwise, just return the
        ;; body
        (define build-letrec
          (lambda (x* e* body)
            (if (null? x*)
                body
                `(letrec ([,x* ,e*] ...) ,body))))
        ;; build a begin when we have more then one expression, otherwise just
        ;; return the one expression.
        (define build-begin
          (lambda (e* e)
            (nanopass-case (L8 Expr) e
              [(begin ,e1* ... ,e) 
               (build-begin (append e* e1*) e)]
              [else
               (if (null? e*)
                   e
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,e)
                         (let ([e (car e*)])
                           (nanopass-case (L8 Expr) e
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(letrec ([,x* ,[e*]] ...) (assigned (,a* ...) ,[body]))
       ;; loop through our bindings, separating them into simple, lambda, and
       ;; complex.
       (let loop ([xb* x*] [e* e*]
                  [xs* '()] [es* '()]
                  [xl* '()] [el* '()]
                  [xc* '()] [ec* '()])
         (if (null? xb*)
             ;; when we're done bind the complex bindings to #f, they are now
             ;; all assigned, then bind the simple bindings, then create a
             ;; letrec binding for the lambda expressions (eliminate the
             ;; assigned body, since we know none of them are assigned), and
             ;; finally use set! to set the values of our complex bindings.
             (build-let xc* (make-list (length xc*) `(quote #f)) xc*
               (build-let xs* es* '()
                 (build-letrec xl* el*
                   (build-begin
                     (map (lambda (xc ec) `(set! ,xc ,ec)) xc* ec*)
                     body))))
             (let ([x (car xb*)] [e (car e*)])
               (cond
                 [(and (not (memq x a*)) (lambda? e))
                  (loop (cdr xb*) (cdr e*) xs* es*
                    (cons x xl*) (cons e el*) xc* ec*)]
                 [(and (not (memq x a*)) (simple? e x* a*))
                  (loop (cdr xb*) (cdr e*) (cons x xs*) (cons e es*)
                    xl* el* xc* ec*)]
                 [else (loop (cdr xb*) (cdr e*) xs* es* xl* el*
                         (cons x xc*) (cons e ec*))]))))]))

  ;;; pass: optimize-direct-call : L8 -> L8
  ;;;
  ;;; one of our simplest optimizations, we convert a directly applied lambdas
  ;;; into a let.  this allows us to avoid the creation of a closure for the
  ;;; let, and allows us instead to create a local binding within a function.
  ;;; the transform is simple:
  ;;;
  ;;; ((lambda (x* ...) body) e* ...) => (let ([x* e*] ...) body)
  ;;; where (length x*) == (length e*)
  ;;; 
  (define-pass optimize-direct-call : L8 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      [((lambda (,x* ...) ,[abody]) ,[e* -> e*] ...)
       (guard (fx=? (length x*) (length e*)))
       `(let ([,x* ,e*] ...) ,abody)]))

  ;;; pass: find-let-bound-lambdas : L8 -> L8
  ;;;
  ;;; this pass looks for places where let is used to bind a lambda expression
  ;;; to an immutable variable and converts this binding into a letrec binding.
  ;;; Part of the reason we can do this here, is because we have uniquely named
  ;;; each of our variables and none of these variables can be referenced in
  ;;; the right-hand side of the let bindings.  If it was still possible for
  ;;; variables to have same name, this would not be a legal transformation,
  ;;; since it might cause a lambda that did not capture a variable bound in
  ;;; this let to bind the variable in the resulting letrec.  The
  ;;; transformation looks like:
  ;;;
  ;;; (let ([x 5] [f (lambda (n) (+ n n))] [g (lambda (x) x)] [m 10])
  ;;;   (assigned (g m)
  ;;;     body)) =>
  ;;; (let ([x 5] [g (lambda (x) x)] [m 10])
  ;;;   (assigned (g m)
  ;;;     (letrec ([f (lambda (n) (+ n n))])
  ;;;       body)))
  ;;;
  ;;; Design decisions: Handling of let can be incorporated into the handling
  ;;; of letrec, either through one of the algorithms described in the design
  ;;; decisions of the purify-letrec pass, or in the existing letrec pass. It
  ;;; is kept separate here, largely to make the letrec pass more straight
  ;;; forward to understand.
  ;;; 
  (define-pass find-let-bound-lambdas : L8 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      (definitions
        ;; build-let - constructs a let if any variables are bound by the let,
        ;; or simply returns the body if there are no bindings.
        (define build-let
          (lambda (x* e* a* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) (assigned (,a* ...) ,body)))))
        ;; build-letrec - constructs a letrec if any variables are bound by the
        ;; letrec, or simple returns the body if there are no bindings.
        (define build-letrec
          (lambda (x* le* body)
            (if (null? x*)
                body
                `(letrec ([,x* ,le*] ...) ,body)))))
      [(let ([,x* ,[e*]] ...) (assigned (,a* ...) ,[body]))
       ;; executes a similar algorithm to the purify-letrec pass, though it
       ;; does not separate simple from complex bindings, since we currently
       ;; handle both in the let.
       (let loop ([xb* x*] [e* e*] [xl* '()] [el* '()] [xo* '()] [eo* '()])
         (if (null? xb*)
             (build-let xo* eo* a* (build-letrec xl* el* body))
             (let ([x (car xb*)] [e (car e*)])
               (nanopass-case (L8 Expr) e
                 [(lambda (,x* ...) ,abody)
                  (guard (not (memq x a*)))
                  (loop (cdr xb*) (cdr e*) (cons x xl*) (cons e el*) xo* eo*)]
                 [else (loop (cdr xb*) (cdr e*) xl* el*
                         (cons x xo*) (cons e eo*))]))))]))

  ;;; pass: remove-anonymous-lambda : L8 -> L9
  ;;;
  ;;; since we are generating a C function for each Scheme lambda, we need to
  ;;; have a name for each of these lambdas.  In addition we need a name to use
  ;;; as the code pointer label, so that we can lift the lambdas to the top
  ;;; level of the program.  The transformation is fairly simple.  If we find a
  ;;; lambda in expression position (i.e. not in the right-hand side of a
  ;;; letrec binding) then we wrap a letrec around it that gives it a new name.
  ;;;
  ;;; (letrec ([l* (lambda (x** ...) body*)] ...) body) => (no change)
  ;;; (letrec ([l* (lambda (x** ...) body*)] ...) body)
  ;;;
  ;;; (lambda (x* ...) body) => (letrec ([t0 (lambda (x* ...) body)]) t0)
  ;;;
  (define-pass remove-anonymous-lambda : L8 (e) -> L9 ()
    (Expr : Expr (e) -> Expr ()
      [(lambda (,x* ...) ,[abody])
       (let ([t (unique-var 'anon)])
         `(letrec ([,t (lambda (,x* ...) ,abody)]) ,t))]))

  ;;; pass: convert-assignments : L9 -> L10
  ;;;
  ;;; this pass completes the assignment conversion process that we started in
  ;;; identify-assigned-variables. We use the assigned variable list through
  ;;; our previous passes to make decisions about how bindings were separated.
  ;;; Now, we are ready to change these explicitly to the box, unbox, and
  ;;; set-box!  primitive calls described in the identified-assigned-variable
  ;;; pass.  We also introduce new temporaries to contain the value that will
  ;;; be put in the box.  this is largely because we don't want our
  ;;; representation of assigned variables to be observable from inside the
  ;;; program, and if we were to introduce an operator like call/cc to our
  ;;; implementation, then the order our variables were setup could potentially
  ;;; be identified by seeing that the allocation and computation of the values
  ;;; are intermixed.  Instead, we want all the computation to happen, then the
  ;;; allocation, and then the allocated locations are updated with the values.
  ;;;
  ;;; Our transform thus looks like the following:
  ;;;
  ;;; (let ([x0 e0] [x1 e1] ... [xa0 ea0] [xa1 xa0] ...)
  ;;;   (assigned (xa0 xa1 ...)
  ;;;     body))
  ;;; =>
  ;;; (let ([x0 e0] [x1 e1] ... [t0 ea0] [t1 ea1] ...)
  ;;;   (let ([xa0 (primcall box t0)] [xa1 (primcall box t1)] ...)
  ;;;     body^))
  ;;;
  ;;; (lambda (x0 x1 ... xa0 xa1 ...) (assigned (xa0 xa1 ...) body))
  ;;; =>
  ;;; (lambda (x0 x1 ... t0 t1 ...)
  ;;;   (let ([xa0 (primcall box t0)] [xa1 (primcall box t1)] ...)
  ;;;     body^))
  ;;;
  ;;; where 
  ;;; (set! xa0 e) => (primcall set-box! xa0 e^)
  ;;; and 
  ;;; xa0 => (primcall unbox xa0)
  ;;; in body^ and e^
  ;;;
  ;;; We could choose another data structure, or even create a new data
  ;;; structure to perform the conversion with, however, we've choosen the box
  ;;; because it contains exactly one cell, and takes up just one word in
  ;;; memory, where as our pair and vector take at least two words in memory.
  ;;; This decision might be different if we had other constraints on how we
  ;;; lay out memory.
  ;;;
  (define-pass convert-assignments : L9 (e) -> L10 ()
    (definitions
      ;; lookup - looks for assigned variables in the environment and maps them
      ;; to their temporaries.
      (define lookup
        (lambda (env)
          (lambda (x)
            (cond
              [(assq x env) => cdr]
              [else x]))))
      ;; build-env - generates temporaries, extends the environment, and
      ;; returns the final list of unassigned binding variables, the list of
      ;; emporaries, and the updated environment, through the call to f
      (define build-env
        (lambda (x* a* env f)
          (let ([t* (map (lambda (x) (make-tmp)) a*)])
            (let ([env (append (map cons a* t*) env)])
              (f (map (lookup env) x*) t* env)))))
      (with-output-language (L10 Expr)
        ;; make-boxes - build the calls to box to create the storage locations
        ;; for our assigned variables.
        (define make-boxes
          (lambda (t*)
            (map (lambda (t) `(primcall box ,t)) t*)))
        ;; build-let - builds a let if there are any bindings, or returns the
        ;; body if there are none.
        (define build-let
          (lambda (x* e* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) ,body))))))
    (Expr : Expr (e [env '()]) -> Expr ()
      [(let ([,x* ,[e*]] ...) (assigned (,a* ...) ,body))
       (build-env x* a* env
         (lambda (x* t* env)
           (build-let x* e*
             (build-let a* (make-boxes t*)
               (Expr body env)))))]
      [,x (if (assq x env) `(primcall unbox ,x) x)]
      [(set! ,x ,[e]) `(primcall set-box! ,x ,e)])
    (LambdaExpr : LambdaExpr (le env) -> LambdaExpr ()
      [(lambda (,x* ...) (assigned (,a* ...) ,body))
       (build-env x* a* env
         (lambda (x* t* env)
           `(lambda (,x* ...)
              ,(build-let a* (make-boxes t*) (Expr body env)))))]))

  ;;; pass: uncover-free : L10 -> L11
  ;;;
  ;;; this pass performs the first step in closure conversion, determining the
  ;;; set of free-variables for each lambda expression.  this list of free
  ;;; variables is an approximation of the values that need to be available to
  ;;; a procedure as its captured environment when a procedure is executed.
  ;;; there are numerous ways to shrink, or even eliminate this list, but in
  ;;; this compiler we are currently skipping any of these steps, and simply
  ;;; taking this set of free variables as the set we need to capture.  (For
  ;;; one possible closure optimization technique see "Optimizing Flat
  ;;; Closures" by Keep et. al. or Chapter 5. of "A Nanopass Compiler for
  ;;; Commercial Compiler Development" by Keep).  This is an analysis pass,
  ;;; so we are just gathering up the free variables.  This will look somewhat
  ;;; similar to the identify-assigned-variables, except we care about all
  ;;; variable references, but only the free variables at lambdas. 
  ;;;
  (define-pass uncover-free : L10 (e) -> L11 ()
    (Expr : Expr (e) -> Expr (free*)
      ;; quoted constants have no variable references
      [(quote ,c) (values `(quote ,c) '())]
      ;; gather up variable references
      [,x (values x (list x))]
      ;; if we find a let or a letrec remove the bound variables from the list
      ;; of references.
      [(let ([,x* ,[e* free**]] ...) ,[e free*])
       (values `(let ([,x* ,e*] ...) ,e)
         (apply union (difference free* x*) free**))]
      [(letrec ([,x* ,[le* free**]] ...) ,[body free*])
       (values `(letrec ([,x* ,le*] ...) ,body)
         (difference (apply union free* free**) x*))]
      ;; in all the other cases, we simply want to gather up the 
      ;; variable references from each sub expression
      [(if ,[e0 free0*] ,[e1 free1*] ,[e2 free2*])
       (values `(if ,e0 ,e1 ,e2) (union free0* free1* free2*))]
      [(begin ,[e* free**] ... ,[e free*])
       (values `(begin ,e* ... ,e) (apply union free* free**))]
      [(primcall ,pr ,[e* free**]...)
       (values `(primcall ,pr ,e* ...) (apply union free**))]
      [(,[e free*] ,[e* free**] ...)
       (values `(,e ,e* ...) (apply union free* free**))])
    (LambdaExpr : LambdaExpr (le) -> LambdaExpr (free*)
      ;; at the lambda expression, remove our bound variables, everything else
      ;; is free.  we continue to return the free variables until we find their
      ;; binding forms.
      [(lambda (,x* ...) ,[body free*])
       (let ([free* (difference free* x*)])
         (values `(lambda (,x* ...) (free (,free* ...) ,body)) free*))])
    ;; in the body, we kick off with the Expr call, and make sure that we have
    ;; an empty free list when we reach the top, because we expect our programs
    ;; to be self-contained with no free-references.
    (let-values ([(e free*) (Expr e)])
      (unless (null? free*) (error who "found unbound variables" free*))
      e))

  ;;; pass: convert-closures : L11 -> L12
  ;;;
  ;;; this pass begins closure conversion, using the free variable lists
  ;;; gathered in the previous pass to begin creating our closure data
  ;;; structures.  This pass splits letrec bindings into a 'closures' binding
  ;;; form, which lists the bound variable, a label that will refer to the code
  ;;; of the function (and will become the function name), and the list of free
  ;;; variables that will be included in the final closure datastructure.  The
  ;;; second binding form is the labels form, which binds the label for a
  ;;; procedure to the procedures code.  We also add an explicit closure
  ;;; pointer argument to each procedure. If we were compiling to assembly
  ;;; code, we might avoid this and just specify a register to hold the closure
  ;;; pointer.  We can also eliminate the need for the closure pointer if we
  ;;; use the correct optimizations.  Finally, we add the explicit closure
  ;;; argument to each procedure call site.
  ;;;
  ;;; These transformations look as follows:
  ;;;
  ;;; (letrec ([x* (lambda (x** ...) (free (f** ...) body*))] ...) body) =>
  ;;; (closures ([x* l* f** ...] ...)
  ;;;   (labels ([l* (lambda (cp* x** ...) (free (f** ...) body*))] ...) body))
  ;;; where l* is a list of labels for each lambda expression and cp* is a 
  ;;; list of variables representing an explicit closure argument
  ;;;
  ;;; (x e* ...) => (x x e* ...) ; a small optimization
  ;;; (e e* ...) => (let ([t e]) (t t e* ...))
  ;;; 
  ;;; Design decision: We separate the steps of closure creation and explicit
  ;;; allocation and setting of closure values, partially so that we can
  ;;; implement closure optimization passes that can help reduce the number of
  ;;; free variables, or even eliminate closures entirely, when we do not have
  ;;; any free variables.
  ;;;
  (define-pass convert-closures : L11 (e) -> L12 ()
    (definitions
      (define make-cp (lambda (x) (unique-var 'cp)))
      (define make-label
        (lambda (x)
          (unique-var
            (string->symbol
              (string-append "l:"
                (symbol->string (base-var x))))))))
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,x* (lambda (,x** ...) (free (,f** ...) ,[body*]))] ...)
         ,[body])
       (let ([l* (map make-label x*)] [cp* (map make-cp x*)])
         `(closures ([,x* ,l* ,f** ...] ...)
            (labels ([,l* (lambda (,cp* ,x** ...)
                            (free (,f** ...) ,body*))] ...)
              ,body)))]
      [(,x ,[e*] ...) `(,x ,x ,e* ...)]
      [(,[e] ,[e*] ...)
       (let ([t (make-tmp)])
         `(let ([,t ,e]) (,t ,t ,e* ...)))]))

  ;;; pass: optimize-known-call : L12 -> L12
  ;;;
  ;;; a tiny "optimization" pass that recognizes when we know what procedure
  ;;; is being called, and refers to the procedure directly, rather than
  ;;; requiring that the procedure pointer be accessed through a dereference
  ;;; of the closure pointer.  This allows the procedure to be called as:
  ;;;
  ;;; func_name_10(...)
  ;;;
  ;;; instead of:
  ;;;
  ;;; ((ptr (*)(ptr, ...))*(func_closure_10 + closure-code-offset - closure-tag)(...)
  ;;;
  ;;; in addition to looking simpler, it also avoids indirect calls, which
  ;;; means both that we can avoid an extra memory reference, and the C
  ;;; compiler has a better opportunity to optimize the call, and the processor
  ;;; can potentially handle the code faster (in addition avoiding the extra
  ;;; memory reference).
  ;;;
  ;;; Design decision: Our approach to determining when a call is known is
  ;;; pretty simple.  When we pass a closure binding we add the binding of the
  ;;; variable to the label to our environment, and if we encounter a call to
  ;;; one of these variables, we replace it with a reference to the label.
  ;;; This gives us good results, but it will not detect every known call that
  ;;; we might be able to find if we used a more expensive analysis like
  ;;; control-flow analysis.  For our purposes, the linear-time optimization
  ;;; is fast and simple, but if we want a more precise analysis, and we are
  ;;; willing to pay the additional cost (slightly less than cubic for 0CFA or
  ;;; exponential for 1CFA or higher), than we could perform a more precise
  ;;; analysis here. 
  ;;;
  (define-pass optimize-known-call : L12 (e) -> L12 ()
    (LabelsBody : LabelsBody (lbody env) -> LabelsBody ())
    (LambdaExpr : LambdaExpr (le env) -> LambdaExpr ())
    (FreeBody : FreeBody (fbody env) -> FreeBody ())
    (Expr : Expr (e [env '()]) -> Expr ()
      [(closures ([,x* ,l* ,f** ...] ...) ,lbody)
       (let ([env (fold-left
                    (lambda (env x l) (cons (cons x l) env))
                    env x* l*)])
         (let ([lbody (LabelsBody lbody env)])
           `(closures ([,x* ,l* ,f** ...] ...) ,lbody)))]
      [(,x ,[e*] ...)
       (cond
         [(assq x env) => (lambda (as) `((label ,(cdr as)) ,e* ...))]
         [else `(,x ,e* ...)])]))

  ;;; pass: expose-closure-prims : L12 -> L13
  ;;;
  ;;; this pass finishes closure conversion by turning our closures form into a
  ;;; let binding closure variables to explicit closure allocations (using the
  ;;; added make-closure primitive) and explicit closure set!s to fill in the
  ;;; code (with the closure-code-set!  primitive) and free variable values of
  ;;; the closure (with the closre-data-set! primitive).  We do this as
  ;;; separate creation and mutation steps, since we may have circular
  ;;; datastructures, where we need to place the value of a closure allocated
  ;;; in the let binding in a closure bound by the same let binding.  We also
  ;;; move the labels form into plae as an expression, discard the free
  ;;; variable list form the body of our lambda expressions, and make explicit
  ;;; references to the closure code slot (with the closure-code primitive)
  ;;; where closures are called, and the closure data slots (with the
  ;;; closure-ref primitive) where a free variable is referenced.
  ;;;
  ;;; The transform looks as follows:
  ;;; (closures ([x* l* f** ...] ...) lbody) =>
  ;;; (let ([x* (primcall make-closure ---)] ...)
  ;;;   (begin
  ;;;     (primcall closure-code-set! x* l*) ...
  ;;;     (primcall closure-data-set! x* 0 (car f**))
  ;;;     (primcall closure-data-set! x* 1 (cadr f**))
  ;;;     ...))
  ;;;
  ;;; (x e* ...) => ((closure-code x) e* ...)
  ;;; x          => (closure-ref cp idx)      ; where x is a free variable, and
  ;;;                                         ; idx is the offset of the free
  ;;;                                         ; variable in the closure.
  ;;; 
  ;;;
  ;;; Design decision: We could also combine this with the lift-lambdas pass
  ;;; and finish lifting (our now first-order) procedures to the top-level of
  ;;; the program.  It is reasonable to keep these separate, since their action
  ;;; on the code is a little different, but they could also be combined
  ;;; without much trouble.
  ;;;
  (define-pass expose-closure-prims : L12 (e) -> L13 ()
    (Expr : Expr (e [cp #f] [free* '()]) -> Expr ()
      (definitions
        (define handle-closure-ref
          (lambda (x cp free*)
            (let loop ([free* free*] [i 0])
              (cond
                [(null? free*) x]
                [(eq? x (car free*)) `(primcall closure-ref ,cp (quote ,i))]
                [else (loop (cdr free*) (fx+ i 1))]))))
        (define build-closure-set*
          (lambda (x* l* f** cp free*)
            (fold-left
              (lambda (e* x l f*)
                (let loop ([f* f*] [i 0] [e* e*])
                  (if (null? f*)
                      (cons `(primcall closure-code-set! ,x (label ,l)) e*)
                      (loop (cdr f*) (fx+ i 1)
                        (cons `(primcall closure-data-set! ,x (quote ,i)
                                 ,(handle-closure-ref (car f*) cp free*))
                          e*)))))
              '()
              x* l* f**))))
      [(closures ([,x* ,l* ,f** ...] ...)
         (labels ([,l2* ,[le*]] ...) ,[body]))
       (let ([size* (map length f**)])
         `(let ([,x* (primcall make-closure (quote ,size*))] ...)
            (labels ([,l2* ,le*] ...)
              (begin
                ,(build-closure-set* x* l* f** cp free*) ...
                ,body))))]
      [,x (handle-closure-ref x cp free*)]
      [((label ,l) ,[e*] ...) `((label ,l) ,e* ...)]
      [(,[e] ,[e*] ...) `((primcall closure-code ,e) ,e* ...)])
   (LabelsBody : LabelsBody (lbody) -> Expr ())
   (LambdaExpr : LambdaExpr (le) -> LambdaExpr ()
     [(lambda (,x ,x* ...) (free (,f* ...) ,[body x f* -> body]))
      `(lambda (,x ,x* ...) ,body)]))

  ;;; pass: lift-lambdas : L13 -> L14
  ;;;
  ;;; lifts all of the labels and lambda expressions to a top-level labels
  ;;; binding.  when we generate C code, these will become top-level C
  ;;; functions.
  ;;;
  ;;; Design decisions: This pass is written using mutation, largely to shorten
  ;;; the code that would gather up the label and lambda expression lists.
  ;;; Another approach would be to gather these up by returning extra values
  ;;; from each expression that has the list of labels and lambda expressions.
  ;;; This would be simpler if the nanopass framework supported a way to flow
  ;;; extra values through the data, but it doesn't currently support this
  ;;; (it's on my feature todo list :).
  ;;;
  (define-pass lift-lambdas : L13 (e) -> L14 ()
    (definitions
      (define *l* '())
      (define *le* '()))
    (Expr : Expr (e) -> Expr ()
      [(labels ([,l* ,[le*]] ...) ,[body])
       (set! *l* (append l* *l*))
       (set! *le* (append le* *le*))
       body])
    (let ([e (Expr e)] [l (unique-var 'l:program)])
      `(labels ([,l (lambda () ,e)] [,*l* ,*le*] ...) ,l)))

  ;;; pass: remove-complex-opera* : L14 -> L15
  ;;;
  ;;; this pass removes nested complex operators.  strictly speaking, this is
  ;;; not something that we need to do since C is our target, however if we
  ;;; want to taret assembly or something like LLVM.  If we target something
  ;;; like JavaScript, however, we might want to eliminate this.
  ;;;
  ;;; one reason I like this pass, is that it is a very simple pass for
  ;;; something that is relatively complicated because the nanopadd framework
  ;;; is really able to do a lot of work for us.
  ;;;
  ;;; Design decision: If we decide to remove this pass, the C code generation
  ;;; pass will have to be a bit smarter about how it generates code, because
  ;;; we will then have complex arguments, however, any decent C compiler
  ;;; should be able to keep up with the tricks we'd need to play.
  ;;;
  (define-pass remove-complex-opera* : L14 (e) -> L15 ()
    (definitions
      (with-output-language (L15 Expr)
        (define build-let
          (lambda (x* e* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) ,body)))))
      (define simplify*
        (lambda (e* f)
          (let loop ([e* e*] [t* '()] [te* '()] [re* '()])
            (if (null? e*)
                (build-let t* te* (f (reverse re*)))
                (let ([e (car e*)])
                  (nanopass-case (L15 Expr) e
                    [,x (loop (cdr e*) t* te* (cons x re*))]
                    [(quote ,c) (loop (cdr e*) t* te* (cons e re*))]
                    [(label ,l) (loop (cdr e*) t* te* (cons e re*))]
                    [else (let ([t (make-tmp)])
                            (loop (cdr e*) (cons t t*)
                              (cons e te*) (cons t re*)))])))))))
    (Expr : Expr (e) -> Expr ()
      [(primcall ,pr ,[e*] ...)
       (simplify* e*
         (lambda (e*)
           `(primcall ,pr ,e* ...)))]
      [(,[e] ,[e*] ...)
       (simplify* (cons e e*)
         (lambda (e*)
           `(,(car e*) ,(cdr e*) ...)))]))

  ;;; pass: recognize-context : L15 -> L16
  ;;;
  ;;; This pass seperates the Expr into Value, Effect, and Predicate cases.
  ;;; The basic idea is to recognize where we have primitive calls that are out
  ;;; of place for the value that they produce, the effect they perform, or the
  ;;; branching direction they cause us to select.  This is partially necessary
  ;;; because we are choosing our own represenation for values, which may not
  ;;; be the same as C's representation, and because we require that each
  ;;; procedure return a value.  The basic idea is pretty simple, the body of a
  ;;; procedure is in Value context, so this is the context we start in.  When
  ;;; we process an 'if' form, the test position is in predicate context.  In
  ;;; this context we need to produce a true or false value in C (i.e. 0 for
  ;;; true, or a non-zero integer, usually 1, for true).  If we are in Value
  ;;; context and we encounter a 'begin' form, the expressions before the end
  ;;; of the 'begin' form are in effect context.
  ;;;
  ;;; The rules are as follows:
  ;;; In Value context:
  ;;; (primcall effect-prim e* ...) =>
  ;;;   (begin (primcall effect-prim e* ...) (primcall void))
  ;;; (primcall pred-prim e* ...) =>
  ;;;   (if (primcall pred-prim e* ...) (quote #t) (quote #f))
  ;;;
  ;;; In Effect context:
  ;;;   x                             => (nop)
  ;;;   (quote c)                     => (nop)
  ;;;   (label l)                     => (nop)
  ;;;   (primcall value-prim e* ...)  => (nop)
  ;;;   (primcall effect-prim e* ...) => (nop)
  ;;;
  ;;; In Predicate context (remember in Scheme #f is the only false value):
  ;;;   x                => (if (primcall = x #f) (false) (true))
  ;;;   (quote #f)       => (false)
  ;;;   (quote (not #f)) => (true)
  ;;;   (primcall value-prim e* ...) =>
  ;;;     (if (let ([t (primcall value-prim e* ...)])
  ;;;           (= t (quote #f)))
  ;;;         (false)
  ;;;         (true))
  ;;;   (primcall effect-prim e* ...) =>
  ;;;      (begin (primcall effect-prim e* ...) (true)) ; (void) is not #f!
  ;;;   (se se* ...) =>
  ;;;     (if (let ([t (se se* ...)])
  ;;;           (primcall = t (quote #f)))
  ;;;         (false)
  ;;;         (true))
  ;;;   we also do a small optimization, if we see (true) or (false) in
  ;;;   the output of an 'if' test form, we choose either the consequent or
  ;;;   the alternative.
  ;;; 
  ;;; Design decision: We could swap recognize-context and
  ;;; remove-complex-expr*, which would allow us to avoid building the 'let'
  ;;; form when a Value prim or procedure call appears in the Predicate
  ;;; context.  On the other hand, we would need to process three contexts of
  ;;; Expr, and maintain the context separation.
  ;;;
  (define-pass recognize-context : L15 (e) -> L16 ()
    (Value : Expr (e) -> Value ()
      [(primcall ,pr ,[se*] ...)
       (guard (value-primitive? pr))
       `(primcall ,pr ,se* ...)]
      [(primcall ,pr ,[se*] ...)
       (guard (predicate-primitive? pr))
       `(if (primcall ,pr ,se* ...) (quote #t) (quote #f))]
      [(primcall ,pr ,[se*] ...)
       (guard (effect-primitive? pr))
       `(begin (primcall ,pr ,se* ...) (primcall void))]
      [(primcall ,pr ,se* ...)
       (error who "unexpected primitive found" pr)])
    (Effect : Expr (e) -> Effect ()
      [,se `(nop)]
      [(primcall ,pr ,[se*] ...)
       (guard (effect-primitive? pr))
       `(primcall ,pr ,se* ...)]
      [(primcall ,pr ,[se*] ...)
       (guard (or (value-primitive? pr) (predicate-primitive? pr)))
       `(nop)]
      [(primcall ,pr ,se* ...)
       (error who "unexpected primitive found" pr)])
    (Predicate : Expr (e) -> Predicate ()
      [(quote ,c) (if c `(true) `(false))]
      [,x `(if (primcall eq? x (quote #f)) (false) (true))]
      [(if ,[p0] ,[p1] ,[p2])
       (nanopass-case (L16 Predicate) p0
         [(true) p1]
         [(false) p2]
         [else `(if ,p0 ,p1 ,p2)])]
      [(,[se] ,[se*] ...)
       (let ([t (make-tmp)])
         `(if (let ([,t (,se ,se* ...)])
                (primcall = ,t (quote #f)))
              (false)
              (true)))]
      [(primcall ,pr ,[se*] ...)
       (guard (predicate-primitive? pr))
       `(primcall ,pr ,se* ...)]
      [(primcall ,pr ,[se*] ...)
       (guard (effect-primitive? pr))
       `(begin (primcall ,pr ,se* ...) (true))]
      [(primcall ,pr ,[se*] ...)
       (guard (value-primitive? pr))
       (let ([t (make-tmp)])
         `(if (let ([,t (primcall ,pr ,se* ...)])
                (primcall eq? ,t (quote #f)))
              (false)
              (true)))]
      [(primcall ,pr ,se* ...)
       (error who "unexpected primitive found" pr)]))

  ;;; pass: expose-allocation-primitives : L16 -> L17
  ;;;
  ;;; this pass replaces the primitives that allocate new Scheme data
  ;;; structures with a generic alloc form that takes the number of bytes to
  ;;; allocate and the tag to add.  (We cheat a little on the number of bytes
  ;;; by using the fact that our fixnum data type is going to be adjusted
  ;;; appropriately from representing the number of words in the data structure
  ;;; to the number of bytes in the data structure.)  This will eliminate
  ;;; primitive calls to make-vector, make-closure, box, and cons and replace
  ;;; it with allocs and explicit sets.  One thing to note is that in the case
  ;;; of box and cons, we want to be sure that the arguments are evaluated
  ;;; first, then the space is allocated, and finally the values are set in the
  ;;; data structure. We do this because, while we can evaluate the arguments
  ;;; in any order, however, we need to complete their evaluation before we
  ;;; start executing the primitive.  In our little compiler, we could get away
  ;;; with cheating, but if we added a feature like call/cc our cheats would be
  ;;; observable.
  ;;; 
  (define-pass expose-allocation-primitives : L16 (e) -> L17 ()
    (Value : Value (v) -> Value ()
      [(primcall ,vpr ,[se])
       (case vpr
         [(make-vector)
          (nanopass-case (L17 SimpleExpr) se
            [(quote ,c)
             (target-fixnum? c)
             (let ([t (make-tmp)])
               `(let ([,t (alloc ,vector-tag (quote ,(+ c 1)))])
                  (begin
                    (primcall $vector-length-set! ,t (quote ,c))
                    ,t)))]
            [else (let ([t0 (make-tmp)] [t1 (make-tmp)] [t2 (make-tmp)])
                    `(let ([,t0 ,se])
                       (let ([,t1 (primcall + ,t0 (quote 1))])
                         (let ([,t2 (alloc ,vector-tag ,t1)])
                           (begin
                             (primcall $vector-length-set! ,t2 ,t0)
                             ,t2)))))])]
         [(make-closure)
          (nanopass-case (L17 SimpleExpr) se
            [(quote ,c)
             (guard (target-fixnum? c))
             `(alloc ,closure-tag (quote ,(+ c 1)))]
            [else (error who
                    "expected constant argument for make-closure primcall"
                    (unparse-L16 v))])]
         [(box)
          (let ([t0 (make-tmp)] [t1 (make-tmp)])
            `(let ([,t0 ,se])
               (let ([,t1 (alloc ,box-tag (quote 1))])
                 (begin
                   (primcall set-box! ,t1 ,t0)
                   ,t1))))]
         [else `(primcall ,vpr ,se)])]
      [(primcall ,vpr ,[se0] ,[se1])
       (case vpr
         [(cons)
          (let ([t0 (make-tmp)] [t1 (make-tmp)] [t2 (make-tmp)])
            `(let ([,t0 ,se0] [,t1 ,se1])
               (let ([,t2 (alloc ,pair-tag (quote 2))])
                 (begin
                   (primcall $set-car! ,t2 ,t0)
                   (primcall $set-cdr! ,t2 ,t1)
                   ,t2))))]
         [else `(primcall ,vpr ,se0 ,se1)])]))
  
  ;;; pass: return-of-set! : L17 -> L18
  ;;;
  ;;; In this psss we remove the 'let' form and replace it with set!.  While
  ;;; this set! looks like the source-level set!, it really is not the same
  ;;; thing, since each of our variables only ever receive one value over the
  ;;; course of running the program.  If we were compiling to assembly or LLVM,
  ;;; these set!s would directly set the variable at its allocated position,
  ;;; i.e. in a register or memory location.  Here we leave the job of deciding
  ;;; where to allocate each of our single-assignemnt variables.  In this pass,
  ;;; we also gather up all of the variables as locals, so that we can put our
  ;;; variable declarations at the start of the C function.  (This is not
  ;;; required in a modern C compiler, but it does make our job easier, since
  ;;; we don't have to worry about needing to create variables in C contexts
  ;;; where it might not be allowed.)  This latter job is what causes all of
  ;;; the extra work, since there is not a good way to gather up the values
  ;;; without returning from every form in each of our three contexts.
  ;;;
  ;;; Design decision: We could simplify this pass by putting it before the
  ;;; recognize-context pass, but that would compilcate the recognize-context
  ;;; pass.  With all of these types of decisions, it is largely a balancing
  ;;; act of managing the complexity of individual passes, to try to keep the
  ;;; compiler as simple as possible.
  ;;;
  (define-pass return-of-set! : L17 (e) -> L18 ()
    (definitions
      (with-output-language (L18 Effect)
        (define build-set*!
          (lambda (x* v* body build-begin)
            (build-begin
              (map (lambda (x v) `(set! ,x ,v)) x* v*)
              body)))))
    (SimpleExpr : SimpleExpr (se) -> SimpleExpr ('()))
    (Value : Value (v) -> Value ('())
      (definitions
        (define build-begin
          (lambda (e* v)
            (nanopass-case (L18 Value) v
              [(begin ,e1* ... ,v) 
               (build-begin (append e* e1*) v)]
              [else
               (if (null? e*)
                   v
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,v)
                         (let ([e (car e*)])
                           (nanopass-case (L18 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(if ,[p0 var0*] ,[v1 var1*] ,[v2 var2*])
       (values `(if ,p0 ,v1 ,v2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[v var*])
       (values (build-begin e* v) (apply append var* var**))]
      [(primcall ,vpr ,[se* var**] ...)
       (values `(primcall ,vpr ,se* ...) (apply append var**))]
      [(,[se var*] ,[se* var**] ...)
       (values `(,se ,se* ...) (apply append var* var**))]
      [(let ([,x* ,[v* var**]] ...) ,[body var*])
       (values 
         (build-set*! x* v* body build-begin)
         (apply append x* var* var**))])
    (Effect : Effect (e) -> Effect ('())
      (definitions
        (define build-begin
          (lambda (e* e)
            (nanopass-case (L18 Effect) e
              [(begin ,e1* ... ,e) 
               (build-begin (append e* e1*) e)]
              [else
               (if (null? e*)
                   e
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,e)
                         (let ([e (car e*)])
                           (nanopass-case (L18 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(if ,[p0 var0*] ,[e1 var1*] ,[e2 var2*])
       (values `(if ,p0 ,e1 ,e2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[e var*])
       (values (build-begin e* e) (apply append var* var**))]
      [(primcall ,epr ,[se* var**] ...)
       (values `(primcall ,epr ,se* ...) (apply append var**))]
      [(,[se var*] ,[se* var**] ...)
       (values `(,se ,se* ...) (apply append var* var**))]
      [(let ([,x* ,[v* var**]] ...) ,[e var*])
       (values
         (build-set*! x* v* e build-begin)
         (apply append x* var* var**))])
    (Predicate : Predicate (p) -> Predicate ('())
      (definitions
        (define build-begin
          (lambda (e* p)
            (nanopass-case (L18 Predicate) p
              [(begin ,e1* ... ,p) 
               (build-begin (append e* e1*) p)]
              [else
               (if (null? e*)
                   p
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,p)
                         (let ([e (car e*)])
                           (nanopass-case (L18 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(if ,[p0 var0*] ,[p1 var1*] ,[p2 var2*])
       (values `(if ,p0 ,p1 ,p2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[p var*])
       (values (build-begin e* p) (apply append var* var**))]
      [(primcall ,ppr ,[se* var**] ...)
       (values `(primcall ,ppr ,se* ...) (apply append var**))]
      [(let ([,x* ,[v* var**]] ...) ,[p var*])
       (values
         (build-set*! x* v* p build-begin)
         (apply append x* var* var**))])
    (LambdaExpr : LambdaExpr (le) -> LambdaExpr ()
      [(lambda (,x* ...) ,[body var*])
       `(lambda (,x* ...) (locals (,var* ...) ,body))]))
  
  ;;; pass: flatten-set! : L18 -> L19
  ;;;
  ;;; In the previous pass we remove the 'let' form, but we now may have set!
  ;;; expressions on the right-hand side of a set!, such as the following:
  ;;;
  ;;; (set! x.0 (begin
  ;;;             (set! y.1 5)
  ;;;             (set! z.2 7)
  ;;;             (primcall + y.1 z.2)))
  ;;;
  ;;; However, while this is legal in C, we'd like to avoid this, which will
  ;;; help us generate a little easier to read code, and again if we were
  ;;; targeting something like assembly, would be required.  We can transform
  ;;; our example above into:
  ;;;
  ;;; (begin
  ;;;   (set! y.1 5)
  ;;;   (set! z.2 7)
  ;;;   (set! x.0 (primcall + y.1 z.2)))
  ;;;
  (define-pass flatten-set! : L18 (e) -> L19 ()
    (SimpleExpr : SimpleExpr (se) -> SimpleExpr ())
    (Effect : Effect (e) -> Effect ()
      [(set! ,x ,v) (flatten v x)])
    (flatten : Value (v x) -> Effect ()
      [,se `(set! ,x ,(SimpleExpr se))]
      [(primcall ,vpr ,[se*] ...) `(set! ,x (primcall ,vpr ,se* ...))]
      [(alloc ,i ,[se]) `(set! ,x (alloc ,i ,se))]
      [(,[se] ,[se*] ...) `(set! ,x (,se ,se* ...))]))   

  ;;; pass: push-if : L19 -> L20
  ;;;
  ;;; It turns out I was a little overzealous with this pass and didn't quite
  ;;; handle all of the cases.  In particular, in my hustle, I did not think
  ;;; about the `(if p0 p1 p2) where the result expressions contain effects...
  ;;; i.e.  (if (begin ,e0* ...  ,p0) (begin ,e1* ...  ,p1) (begin ,e2* ...
  ;;; ,p2)) can only be handled if:
  ;;;   1. we are willing to copy the code for the tail of our ifs (we aren't,
  ;;;      this can lead to exponential code explosion) or
  ;;;   2. if we are willing to flatten this code and use labels and gotos in
  ;;;      our generated code.
  ;;; Number 2 is a more reasonable solution, but lucky for us, C will allow us
  ;;; to generate code like the following:
  ;;; 
  ;;; (if (begin ,e0* ... ,p0) (begin ,e1* ... ,p1) (begin ,e2* ... ,p2)) =>
  ;;;
  ;;; (((e0*[0]), (e0*[1]), ..., (e0*[n]), p0) ?
  ;;;   ((e1*[0]), (e1*[1]), ..., (e1*[n]), p1) :
  ;;;   ((e2*[0]), (e2*[1]), ..., (e2*[n]), p2))
  ;;;
  ;;; I've left the pass here as an example that even when we think we've got a
  ;;; pass written and working, it easy to miss things, which is why we test,
  ;;; and why we need to think carefully as we work through the compiler.
  ;;;
  ; (define-pass push-if : L19 (e) -> L20 ()
  ;   (Value : Value (v) -> Value ()
  ;     (definitions
  ;       (define build-begin
  ;         (lambda (e* v)
  ;           (if (null? e*) v `(begin ,e* ... ,v)))))
  ;     [(if ,[p0 e*] ,[v1] ,[v2]) (build-begin e* `(if ,p0 ,v1 ,v2))])
  ;   (Effect : Effect (e) -> Effect ()
  ;     (definitions
  ;       (define build-begin
  ;         (lambda (e* e)
  ;           (if (null? e*) e `(begin ,e* ... ,e)))))
  ;     [(if ,[p0 e*] ,[e1] ,[e2]) (build-begin e* `(if ,p0 ,e1 ,e2))])
  ;   (Predicate : Predicate (p) -> Predicate ('())
  ;     [(begin ,[e*] ... ,[p more-e*]) (values p (append e* more-e*))]
  ;     [(if ,[p0 e0*] ,[p1 e1*] ,[p2 e2*])
  ;      (values `(if ,p0 (begin ,e1* ... p1) (begin ,e2* ... ,p2)) e0*)]))
 
  ;;; pass: specify-constant-representation : L19 -> L21
  ;;;
  ;;; This pass replaces our quoted constants with the explicit ptr
  ;;; representation we've decided to use.  This effectively replaces each of our
  ;;; constants with a 64-bit integer.  The conversion is pretty simple:
  ;;;
  ;;; #f     => false-rep
  ;;; #t     => true-rep
  ;;; '()    => null-rep
  ;;; fixnum => fixnum << fixnum-shift (yielding 64-bit integer)
  ;;;
  (define-pass specify-constant-representation : L19 (e) -> L21 ()
    (SimpleExpr : SimpleExpr (se) -> SimpleExpr ()
      [(quote ,c)
       (cond
         [(eq? c #f) false-rep]
         [(eq? c #t) true-rep]
         [(null? c) null-rep]
         [(target-fixnum? c)
          (bitwise-arithmetic-shift-left c fixnum-shift)])]))

  ;;; pass: expand-primitives : L21 -> L22
  ;;;
  ;;; this pass expands our Scheme primitives into something close to their
  ;;; C-language equivalents.  This changes our math primitives to do the
  ;;; adjustments required by changing the representation of fixnums (it works
  ;;; fine for + and -, but * and / require us to do some shifting in order to
  ;;; have a fixnum as a result).  We also translate all of our memory
  ;;; referencing primitives to mrefs and memory setting primitives into
  ;;; msets!.  When we generate C code for these, we will do the pointer
  ;;; arithmetic required and then dereference the calculated address.
  ;;; Remember, that because of our tags, we need to do some pointer arithmetic
  ;;; for any dereference we wish to perform.  This pointer arithmetic, though,
  ;;; can be handled in a single memory reference argument on an x86_64 (which
  ;;; is our assumed target platform).
  ;;;
  ;;; Design decision: Right now each of our "instructions" is a separate form
  ;;; in the language, however, if we were to extend our source language and
  ;;; primitive set much farther, it is likely that we would want to revisit
  ;;; this to choose a representation where a single form could represent
  ;;; several of these instructions.  This might also be desirable if we change
  ;;; the representation to LLVM or asm.js.
  ;;;;
  (define-pass expand-primitives : L21 (e) -> L22 ()
    (Value : Value (v) -> Value ()
      (definitions
        (define build-begin
          (lambda (e* v)
            (nanopass-case (L22 Value) v
              [(begin ,e1* ... ,v) 
               (build-begin (append e* e1*) v)]
              [else
               (if (null? e*)
                   v
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,v)
                         (let ([e (car e*)])
                           (nanopass-case (L22 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(begin ,[e*] ... ,[v]) (build-begin e* v)])
    (Rhs : Rhs (rhs) -> Rhs ()
      [(primcall ,vpr)
       (case vpr
         [(void) void-rep]
         [else (error who "unexpected value primitive" vpr)])]
      [(primcall ,vpr ,[se])
       (case vpr
         [(car) `(mref ,se #f ,(- pair-tag))]
         [(cdr) `(mref ,se #f ,(- word-size pair-tag))]
         [(unbox) `(mref ,se #f ,(- box-tag))]
         [(closure-code) `(mref ,se #f ,(- closure-tag))]
         [(vector-length) `(mref ,se #f ,(- vector-tag))]
         [else (error who "unexpected value primitive" vpr)])]
      [(primcall ,vpr ,[se0] ,[se1])
       (case vpr
         [(closure-ref) `(mref ,se0 ,se1 ,(- word-size closure-tag))]
         [(vector-ref) `(mref ,se0 ,se1 ,(- word-size vector-tag))]
         [(+) `(add ,se0 ,se1)]
         [(-) `(subtract ,se0 ,se1)]
         ;; when we multiply or divide, we need to shift either one of the
         ;; arguments or the result. we could also be a bit more clever here,
         ;; if one of the arguments is a constant, we can perform the shift
         ;; ahead of time (assuming the constant still fits within the 64-bit
         ;; width
         [(*) `(multiply ,se0 (shift-right ,se1 ,fixnum-shift))]
         [(/) `(shift-left (divide ,se0 ,se1) ,fixnum-shift)]
         [else (error who "unexpected value primitive" vpr)])]
      [(primcall ,vpr ,se* ...)
       (error who "unexpected value primitive" vpr)])
    (Effect : Effect (e) -> Effect ()
      (definitions
        (define build-begin
          (lambda (e* e)
            (nanopass-case (L22 Effect) e
              [(begin ,e1* ... ,e) 
               (build-begin (append e* e1*) e)]
              [else
               (if (null? e*)
                   e
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,e)
                         (let ([e (car e*)])
                           (nanopass-case (L22 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(begin ,[e*] ... ,[e]) (build-begin e* e)]
      [(primcall ,epr ,[se0] ,[se1])
       (case epr
         [(set-box!) `(mset! ,se0 #f ,(- box-tag) ,se1)]
         [($set-car!) `(mset! ,se0 #f ,(- pair-tag) ,se1)]
         [($set-cdr!) `(mset! ,se0 #f ,(- word-size pair-tag) ,se1)]
         [($vector-length-set!) `(mset! ,se0 #f ,(- vector-tag) ,se1)]
         [(closure-code-set!) `(mset! ,se0 #f ,(- closure-tag) ,se1)]
         [else (error who "unexpected effect primitive" epr)])]
      [(primcall ,epr ,[se0] ,[se1] ,[se2])
       (case epr
         [(vector-set!) `(mset! ,se0 ,se1 ,(- word-size vector-tag) ,se2)]
         [(closure-data-set!)
          `(mset! ,se0 ,se1 ,(- word-size closure-tag) ,se2)]
         [else (error who "unexpected effect primitive" epr)])]
      [(primcall ,epr ,se* ...)
       (error who "unexpected effect primitive" epr)])
    (Predicate : Predicate (p) -> Predicate ()
      (definitions
        (define build-begin
          (lambda (e* p)
            (nanopass-case (L22 Predicate) p
              [(begin ,e1* ... ,p) 
               (build-begin (append e* e1*) p)]
              [else
               (if (null? e*)
                   p
                   (let loop ([e* e*] [re* '()])
                     (if (null? e*)
                         `(begin ,(reverse re*) ... ,p)
                         (let ([e (car e*)])
                           (nanopass-case (L22 Effect) e
                             [(nop) (loop (cdr e*) re*)]
                             [(begin ,e0* ... ,e0)
                               (loop (append e0* (cons e0 (cdr e*))) re*)]
                             [else (loop (cdr e*) (cons (car e*) re*))])))))]))))
      [(begin ,[e*] ... ,[p]) (build-begin e* p)]
      [(primcall ,ppr ,[se])
       (case ppr
         [(pair?) `(= (logand ,se ,pair-mask) ,pair-tag)]
         [(null?) `(= ,se ,null-rep)]
         [(boolean?) `(= (logand ,se ,boolean-mask) ,boolean-tag)]
         [(vector?) `(= (logand ,se ,vector-mask) ,vector-tag)]
         [(box?) `(= (logand ,se ,box-mask) ,box-tag)]
         [else (error who "unexpected predicate primitive" ppr)])]
      [(primcall ,ppr ,[se0] ,[se1])
       (case ppr
         [(eq? =) `(= ,se0 ,se1)]
         [(<) `(< ,se0 ,se1)]
         [(<=) `(<= ,se0 ,se1)]
         [(>) `(<= ,se1 ,se0)]
         [(>=) `(< ,se1 ,se0)]
         [else (error who "unexpected predicate primitive" ppr)])]
      [(primcall ,ppr ,se* ...)
       (error who "unexpected predicate primitive" ppr)]))

  ;;; pass: generate-C : L22 -> printed-output
  ;;;
  ;;; this pass takes a program in the L22 language and produces a printed C
  ;;; program.  using a string or file port, the results of this can be
  ;;; captured in a string or sent to a file to be compiled.  The code that it
  ;;; produces can be a little difficult to read, particularly with all of the
  ;;; casts to and from ptr values.
  ;;;
  ;;; TODO: this pass is fairly convoluted, and could use some refactoring.  We
  ;;;       might also want to try to pretty-print the C code so that it prints
  ;;;       out a bit better.
  ;;;
  (define-pass generate-c : L22 (e) -> * ()
    (definitions
      (define string-join
        (lambda (str* jstr)
          (cond
            [(null? str*) ""]
            [(null? (cdr str*)) (car str*)]
            [else (string-append (car str*) jstr (string-join (cdr str*) jstr))])))
      ;;; symbol->c-id - converts any Scheme symbol into a valid C identifier.
      (define symbol->c-id
        (lambda (sym)
          (let ([ls (string->list (symbol->string sym))])
            (if (null? ls)
                "_"
                (let ([fst (car ls)])
                  (list->string
                    (cons
                      (if (char-alphabetic? fst) fst #\_)
                      (map (lambda (c)
                             (if (or (char-alphabetic? c)
                                     (char-numeric? c))
                                 c
                                 #\_))
                        (cdr ls)))))))))
      ;;; emit-function-header - generates a function header to be used in the
      ;;; declaration of a function or the definition of a function.
      (define format-function-header
        (lambda (l x*)
          (format "ptr ~a(~a)" l
            (string-join
              (map
                (lambda (x)
                  (format "ptr ~a" (symbol->c-id x)))
                x*)
              ", "))))
      (define format-label-call
        (lambda (l se*)
          (format "  ~a(~a)" (symbol->c-id l)
            (string-join
              (map (lambda (se)
                     (format "(ptr)~a" (format-simple-expr se)))
                se*)
              ", "))))
      (define format-general-call
        (lambda (se se*)
          (format "((ptr (*)(~a))~a)(~a)"
            (string-join (make-list (length se*) "ptr") ", ")
            (format-simple-expr se)
            (string-join
              (map (lambda (se)
                     (format "(ptr)~a" (format-simple-expr se)))
                se*)
              ", "))))
      (define format-binop
        (lambda (op se0 se1)
          (format "((long)~a ~a (long)~a)"
            (format-simple-expr se0)
            op
            (format-simple-expr se1))))
      (define format-set!
        (lambda (x rhs)
          (format "~a = (ptr)~a" (symbol->c-id x) (format-rhs rhs)))))
    ;; transformer to print our function declarations
    (emit-function-decl : LambdaExpr (le l) -> * ()
      [(lambda (,x* ...) ,lbody)
       (printf "~a;~%" (format-function-header l x*))])
    ;; transformer to print our function definitions
    (emit-function-def : LambdaExpr (le l) -> * ()
      [(lambda (,x* ...) ,lbody)
       (printf "~a {~%" (format-function-header l x*))
       (emit-function-body lbody)
       (printf "}~%~%")])
    ;; transformer to emit the body of a function
    (emit-function-body : LocalsBody (lbody) -> * ()
      [(locals (,x* ...) ,body)
       (for-each (lambda (x) (printf "  ptr ~a;~%" (symbol->c-id x))) x*)
       (emit-value body x*)])
    ;; transformer to emit expressions in value context
    (emit-value : Value (v locals*) -> * ()
      [(if ,p0 ,v1 ,v2)
       (printf "  if (~a) {~%" (format-predicate p0))
       (emit-value v1 locals*)
       (printf "  } else {~%")
       (emit-value v2 locals*)
       (printf "  }~%")]
      [(begin ,e* ... ,v)
       (for-each emit-effect e*)
       (emit-value v locals*)]
      [,rhs (printf "  return (ptr)~a;\n" (format-rhs rhs))])
    ;; transformer to format Predicate expressions into strings
    (format-predicate : Predicate (p) -> * (str)
      [(if ,p0 ,p1 ,p2)
       (format "((~a) ? (~a) : (~a))"
         (format-predicate p0)
         (format-predicate p1)
         (format-predicate p2))]
      [(<= ,se0 ,se1) (format-binop "<=" se0 se1)]
      [(< ,se0 ,se1) (format-binop "<" se0 se1)]
      [(= ,se0 ,se1) (format-binop "==" se0 se1)]
      [(true) "1"]
      [(false) "0"]
      [(begin ,e* ... ,p)
       (string-join
         (fold-right (lambda (e s*) (cons (format-effect e) s*))
           (list (format-predicate p)) e*)
         ", ")])
    ;; transformer to format effects in predicate context into strings
    (format-effect : Effect (e) -> * (str)
      [(if ,p0 ,e1 ,e2)
       (format "((~a) ? (~a) : (~a))"
         (format-predicate p0)
         (format-effect e1)
         (format-effect e2))]
      [((label ,l) ,se* ...) (format-label-call l se*)]
      [(,se ,se* ...) (format-general-call se se*)]
      [(set! ,x ,rhs) (format-set! x rhs)]
      [(nop) "0"]
      [(begin ,e* ... ,e)
       (string-join
         (fold-right (lambda (e s*) (cons (format-effect e) s*))
           (list (format-effect e)) e*)
         ", ")]
      [(mset! ,se0 ,se1? ,i ,se2)
       (if se1?
           (format "((*((ptr*)((long)~a + (long)~a + ~d))) = (ptr)~a)"
             (format-simple-expr se0) (format-simple-expr se1?)
             i (format-simple-expr se2))
           (format "((*((ptr*)((long)~a + ~d))) = (ptr)~a)"
             (format-simple-expr se0) i (format-simple-expr se2)))])
    ;; formats simple expressions in to strings
    (format-simple-expr : SimpleExpr (se) -> * (str)
      [,x (symbol->c-id x)]
      [,i (number->string i)]
      [(label ,l) (format "(*~a)" (symbol->c-id l))]
      [(logand ,se0 ,se1) (format-binop "&" se0 se1)]
      [(shift-right ,se0 ,se1) (format-binop ">>" se0 se1)]
      [(shift-left ,se0 ,se1) (format-binop "<<" se0 se1)]
      [(divide ,se0 ,se1) (format-binop "/" se0 se1)]
      [(multiply ,se0 ,se1) (format-binop "*" se0 se1)]
      [(subtract ,se0 ,se1) (format-binop "-" se0 se1)]
      [(add ,se0 ,se1) (format-binop "+" se0 se1)]
      [(mref ,se0 ,se1? ,i) 
       (if se1?
           (format "(*((ptr)((long)~a + (long)~a + ~d)))"
             (format-simple-expr se0)
             (format-simple-expr se1?) i)
           (format "(*((ptr)((long)~a + ~d)))" (format-simple-expr se0) i))])
    ;; prints expressions in effect position into C statements
    (emit-effect : Effect (e) -> * ()
      [(if ,p0 ,e1 ,e2)
       (printf "  if (~a) {~%" (format-predicate p0))
       (emit-effect e1)
       (printf "  } else {~%")
       (emit-effect e2)
       (printf "  }~%")]
      [((label ,l) ,se* ...) (printf "  ~a;\n" (format-label-call l se*))]
      [(,se ,se* ...) (printf "  ~a;\n" (format-general-call se se*))]
      [(set! ,x ,rhs) (printf "  ~a;\n" (format-set! x rhs))]
      [(nop) (if #f #f)]
      [(begin ,e* ... ,e)
       (for-each emit-effect e*)
       (emit-effect e)]
      [(mset! ,se0 ,se1? ,i ,se2)
       (if se1?
           (printf "(*((ptr*)((long)~a + (long)~a + ~d))) = (ptr)~a;\n"
             (format-simple-expr se0) (format-simple-expr se1?)
             i (format-simple-expr se2))
           (printf "(*((ptr*)((long)~a + ~d))) = (ptr)~a;\n"
             (format-simple-expr se0) i (format-simple-expr se2)))])
    ;; formats the right-hand side of a set! into a C expression
    (format-rhs : Rhs (rhs) -> * (str)
      [((label ,l) ,se* ...) (format-label-call l se*)]
      [(,se ,se* ...) (format-general-call se se*)]
      [(alloc ,i ,se)
       (if (use-boehm?)
           (format "(ptr)((long)GC_MALLOC(~a) + ~dl)"
             (format-simple-expr se) i)
           (format "(ptr)((long)malloc(~a) + ~dl)"
             (format-simple-expr se) i))]
      [,se (format-simple-expr se)])
    ;; emits a C program for our progam expression
    (Program : Program (p) -> * ()
      [(labels ([,l* ,le*] ...) ,l)
       (let ([l (symbol->c-id l)] [l* (map symbol->c-id l*)])
         (define-syntax emit-include
           (syntax-rules ()
             [(_ name) (printf "#include <~s>\n" 'name)]))
         (define-syntax emit-predicate
           (syntax-rules ()
             [(_ PRED_P mask tag)
              (emit-c-macro PRED_P (x) "(((long)x & ~d) == ~d)" mask tag)]))
         (define-syntax emit-eq-predicate
           (syntax-rules ()
             [(_ PRED_P rep)
              (emit-c-macro PRED_P (x) "((long)x == ~d)" rep)]))
         (define-syntax emit-c-macro
           (lambda (x)
             (syntax-case x()
               [(_ NAME (x* ...) fmt args ...)
                #'(printf "#define ~s(~a) ~a\n" 'NAME
                    (string-join (map symbol->string '(x* ...)) ", ")
                    (format fmt args ...))])))
         ;; the following printfs output the tiny C runtime we are using
         ;; to wrap the result of our compiled Scheme program.
         (emit-include stdio.h)
         (if (use-boehm?)
             (emit-include gc.h)
             (emit-include stdlib.h))
         (emit-predicate FIXNUM_P fixnum-mask fixnum-tag)
         (emit-predicate PAIR_P pair-mask pair-tag)
         (emit-predicate BOX_P box-mask box-tag)
         (emit-predicate VECTOR_P vector-mask vector-tag)
         (emit-predicate PROCEDURE_P closure-mask closure-tag)
         (emit-eq-predicate TRUE_P true-rep)
         (emit-eq-predicate FALSE_P false-rep)
         (emit-eq-predicate NULL_P null-rep)
         (emit-eq-predicate VOID_P void-rep)
         (printf "typedef long* ptr;\n")
         (emit-c-macro FIX (x) "((long)x << ~d)" fixnum-shift)
         (emit-c-macro UNFIX (x) "((long)x >> ~d)" fixnum-shift)
         (emit-c-macro UNBOX (x) "((ptr)*((ptr)((long)x - ~d)))" box-tag)
         (emit-c-macro VECTOR_LENGTH_S (x) "((ptr)*((ptr)((long)x - ~d)))" vector-tag)
         (emit-c-macro VECTOR_LENGTH_C (x) "UNFIX(VECTOR_LENGTH_S(x))")
         (emit-c-macro VECTOR_REF (x i) "((ptr)*((ptr)((long)x - ~d + ((i+1) * ~d))))" vector-tag word-size)
         (emit-c-macro CAR (x) "((ptr)*((ptr)((long)x - ~d)))" pair-tag)
         (emit-c-macro CDR (x) "((ptr)*((ptr)((long)x - ~d + ~d)))" pair-tag word-size)
         (printf "void print_scheme_value(ptr x) {\n")
         (printf "  long i, veclen;\n")
         (printf "  ptr p;\n")
         (printf "  if (TRUE_P(x)) {\n")
         (printf "    printf(\"#t\");\n")
         (printf "  } else if (FALSE_P(x)) {\n")
         (printf "    printf(\"#f\");\n")
         (printf "  } else if (NULL_P(x)) {\n")
         (printf "    printf(\"()\");\n")
         (printf "  } else if (VOID_P(x)) {\n")
         (printf "    printf(\"(void)\");\n")
         (printf "  } else if (FIXNUM_P(x)) {\n")
         (printf "    printf(\"%ld\", UNFIX(x));\n")
         (printf "  } else if (PAIR_P(x)) {\n")
         (printf "    printf(\"(\");\n")
         (printf "    for (p = x; PAIR_P(p); p = CDR(p)) {\n")
         (printf "      print_scheme_value(CAR(p));\n")
         (printf "      if (PAIR_P(CDR(p))) { printf(\" \"); }\n")
         (printf "    }\n")
         (printf "    if (NULL_P(p)) {\n")
         (printf "      printf(\")\");\n")
         (printf "    } else {\n")
         (printf "      printf(\" . \");\n")
         (printf "      print_scheme_value(p);\n")
         (printf "      printf(\")\");\n")
         (printf "    }\n")
         (printf "  } else if (BOX_P(x)) {\n")
         (printf "    printf(\"#(box \");\n")
         (printf "    print_scheme_value(UNBOX(x));\n")
         (printf "    printf(\")\");\n")
         (printf "  } else if (VECTOR_P(x)) {\n")
         (printf "    veclen = VECTOR_LENGTH_C(x);\n")
         (printf "    printf(\"#(\");\n")
         (printf "    for (i = 0; i < veclen; i += 1) {\n")
         (printf "      print_scheme_value(VECTOR_REF(x,i));\n")
         (printf "      if (i < veclen) { printf(\" \"); } \n")
         (printf "    }\n")
         (printf "    printf(\")\");\n")
         (printf "  } else if (PROCEDURE_P(x)) {\n")
         (printf "    printf(\"#(procedure)\");\n")
         (printf "  }\n")
         (printf "}\n")
         (map emit-function-decl le* l*)
         (map emit-function-def le* l*)
         (printf "int main(int argc, char * argv[]) {\n")
         (printf "  print_scheme_value(~a());\n" l)
         (printf "  printf(\"\\n\");\n")
         (printf "  return 0;\n")
         (printf "}\n"))]))

  ;;; a little helper mostly shamelesly stolen from 
  ;;; the Chez Scheme User's Guide
  (define-syntax with-implicit
    (syntax-rules ()
      [(_ (tid id ...) body0 ... body1)
       (with-syntax ([id (datum->syntax #'tid 'id)] ...)
         body0 ... body1)]))

  ;;; a little macro to make building a compiler with tracing that we can turn
  ;;; off and on easier.  no support for looping in this, but the syntax is very
  ;;; simple:
  ;;; (define-compiler my-compiler-name
  ;;;   (pass1 unparser)
  ;;;   (pass2 unparser)
  ;;;   ...
  ;;;   pass-to-generate-c)
  ;;;
  (define-syntax define-compiler
    (lambda (x)
      (syntax-case x ()
        [(_ name (pass unparser) ... gen-c)
         (with-implicit (name all-passes trace-passes)
           #`(begin
               (define all-passes '(pass ... gen-c))
               (define trace-passes
                 (let ([passes '()])
                   (case-lambda
                     [() passes]
                     [(x)
                      (cond
                        [(symbol? x)
                         (unless (memq x all-passes)
                           (error 'trace-passes "invalid pass name" x))
                         (set! passes (list x))]
                        [(list? x)
                         (unless (for-all (lambda (x) (memq x all-passes)) x)
                           (error 'trace-passes
                             "one or more invalid pass names" x))
                         (set! passes x)]
                        [(eq? x #t) (set! passes all-passes)]
                        [(eq? x #f) (set! passes '())]
                        [else (error 'trace-passes
                                "invalid pass specifier" x)])])))
               (define name
                 (lambda (x)
                   #,(let loop ([pass* #'(pass ...)]
                                [unparser* #'(unparser ...)])
                       (if (null? pass*)
                           #'(begin
                               (when (file-exists? "t.c") (delete-file "t.c"))
                               (with-output-to-file "t.c"
                                 (lambda () (gen-c x)))
                               (when (memq 'gen-c (trace-passes))
                                 (printf "output of pass ~s~%" 'gen-c)
                                 (call-with-input-file "t.c"
                                   (lambda (ip)
                                     (let f ()
                                       (let ([s (get-string-n ip 512)])
                                         (unless (eof-object? s)
                                           (display s)
                                           (f)))))))
                               (system
                                 (format "gcc -m64 ~a t.c -o t"
                                   (if (use-boehm?) "-lgc" "")))
                               (when (file-exists? "t.out")
                                 (delete-file "t.out"))
                               (system "./t > t.out")
                               (call-with-input-file "t.out" read))
                           (with-syntax ([pass (car pass*)]
                                         [unparser (car unparser*)])
                             #`(let ([x (pass x)])
                                 (when (memq 'pass (trace-passes))
                                   (printf "output of pass ~s~%" 'pass)
                                   (pretty-print (unparser x)))
                                 #,(loop (cdr pass*)
                                     (cdr unparser*))))))))))])))

  ;;; the definition of our compiler that pulls in all of our passes and runs
  ;;; them in sequence checking to see if the programmer wants them traced.
  (define-compiler my-tiny-compile
    (parse-and-rename unparse-Lsrc)
    (remove-one-armed-if unparse-L1)
    (remove-and-or-not unparse-L2)
    (make-begin-explicit unparse-L3)
    (inverse-eta-raw-primitives unparse-L4)
    (quote-constants unparse-L5)
    (remove-complex-constants unparse-L6)
    (identify-assigned-variables unparse-L7)
    (purify-letrec unparse-L8)
    (optimize-direct-call unparse-L8)
    (find-let-bound-lambdas unparse-L8)
    (remove-anonymous-lambda unparse-L9)
    (convert-assignments unparse-L10)
    (uncover-free unparse-L11)
    (convert-closures unparse-L12)
    (optimize-known-call unparse-L12)
    (expose-closure-prims unparse-L13)
    (lift-lambdas unparse-L14)
    (remove-complex-opera* unparse-L15)
    (recognize-context unparse-L16)
    (expose-allocation-primitives unparse-L17)
    (return-of-set! unparse-L18)
    (flatten-set! unparse-L19)
    ; (push-if unparse-L20)
    (specify-constant-representation unparse-L21)
    (expand-primitives unparse-L22)
    generate-c))
