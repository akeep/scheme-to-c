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
;;;            |  unbox | box-set! | box? | + | - | * | / | = | < | <= | >
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
    L20 unparse-L20
    L21 unparse-L21
    L22 unparse-L22

    unique-var
    primitive-map
    primitive?
    target-fixnum?
    constant?
    datum?

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
    push-if
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
  (define make-tmp (lambda () (unique-var 't)))

  ;;; Helpers for the various sets of primitives we have over the course of the
  ;;; compiler
  ;;; TODO: we shoould clean this up so there is less redundancy here.
  (define primitive-map
    '((car . 1) (cdr . 1) (cons . 2) (pair? . 1) (null? . 1) (boolean? . 1)
       (make-vector . 1) (vector-ref . 2) (vector-length . 1)
       (vector-set! . 3) (vector? . 1) (box . 1) (unbox . 1) (box-set! . 2)
       (box? . 1) (+ . 2) (- . 2) (* . 2) (/ . 2) (= . 2) (< . 2) (<= . 2)
       (> . 2) (>= . 2) (eq? . 2)))

  (define extended-primitive-map
    (cons '(void . 0) primitive-map))

  (define extended+closure-primitive-map
    (cons* '(closure-code-set! . 2) '(closure-data-set! . 3)
      '(closure-code . 1) '(closure-ref . 2) '(make-closure . 1)
      extended-primitive-map))

  (define primitive?
    (lambda (x)
      (and (assq x primitive-map) #t)))

  (define extended-primitive?
    (lambda (x)
      (and (assq x extended-primitive-map) #t)))

  (define extended+closure-primitive?
    (lambda (x)
      (and (assq x extended+closure-primitive-map) #t)))
  
  (define effect-free-prim?
    (lambda (x)
      (memq x '(car cdr cons make-vector vector-ref box unbox + - * / = < <= >
                >= eq? make-closure closure-ref vector-length))))

  (define predicate-primitive?
    (lambda (x)
      (memq x '(pair? null? boolean? vector? box? = < <= > >= eq?))))

  (define effect-primitive?
    (lambda (x)
      (memq x '(vector-set! box-set! closure-code-set! closure-data-set!))))

  (define value-primitive?
    (lambda (x)
      (memq x '(car cdr cons make-vector vector-ref box unbox + - * /
                closure-code closure-ref make-closure vector-length void))))

  (define non-alloc-value-primitive?
    (lambda (x)
      (memq x '(car cdr vector-ref unbox + - * / closure-code closure-ref
                vector-length void))))

  (define effect+internal-primitive?
    (lambda (x)
      (memq x '(vector-set! box-set! closure-code-set! closure-data-set!
                $vector-length-set! $set-car! $set-cdr!))))

  ;;; Helper functions for identifying terminals in the nanopass languages.
  (define target-fixnum?
    (lambda (x)
      (and (and (integer? x) (exact? x))
           (<= (- (expt 2 60)) x (- (expt 2 60) 1)))))

  (define constant?
    (lambda (x)
      (or (target-fixnum? x) (boolean? x) (null? x))))

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

  ;;; The standard (not very efficient) Scheme representation of sets as lists
  (define set-cons
    (lambda (x set)
      (if (memq x set)
          set
          (cons x set))))

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

  (define difference
    (lambda set*
      (if (null? set*)
          '()
          (fold-right (lambda (setb seta)
                        (let loop ([seta seta] [setb setb])
                          (if (null? seta)
                              setb
                              (let ([a (car seta)])
                                (if (memq a setb)
                                    (loop (cdr seta) (remq a setb))
                                    (loop (cdr seta) (cons a setb)))))))
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

  #;(define-language L1
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c))
        (datum (d)))
      (Expr (e body)
        pr
        x
        c
        (quote d)
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

  (define-language L1
    (extends Lsrc)
    (terminals
      (- (primitive (pr)))
      (+ (extended-primitive (pr))))
    (Expr (e body)
      (- (if e0 e1))))

  #;(define-language L2
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c))
        (datum (d)))
      (Expr (e body)
        pr
        x
        c
        (quote d)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body* ... body)
        (let ([x* e*] ...) body* ... body)
        (letrec ([x* e*] ...) body* ... body)
        (set! x e)
        (e e* ...)))

  (define-language L2
    (extends L1)
    (Expr (e body)
      (- (or e* ...)
         (and e* ...)
         (not e))))

  #;(define-language L3
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c))
        (datum (d)))
      (Expr (e body)
        pr
        x
        c
        (quote d)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (e e* ...)))

  (define-language L3
    (extends L2)
    (Expr (e body)
      (- (lambda (x* ...) body* ... body)
         (let ([x* e*] ...) body* ... body)
         (letrec ([x* e*] ...) body* ... body))
      (+ (lambda (x* ...) body)
         (let ([x* e*] ...) body)
         (letrec ([x* e*] ...) body))))

  #;(define-language L4
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c))
        (datum (d)))
      (Expr (e body)
        x
        c
        (quote d)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...)))

  (define-language L4
    (extends L3)
    (Expr (e body)
      (- pr)
      (+ (primcall pr e* ...) => (pr e* ...))))

  #;(define-language L5
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (datum (d)))
      (Expr (e body)
        x
        (quote d)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...)))

  (define-language L5
    (extends L4)
    (terminals
      (- (constant (c))))
    (Expr (e body)
      (- c)))

  #;(define-language L6
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...)))

  (define-language L6
    (extends L5)
    (terminals
      (- (datum (d)))
      (+ (constant (c))))
    (Expr (e body)
      (- (quote d))
      (+ (quote c))))

  #;(define-language L7
      (terminals
        (symbol (x a))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) abody)
        (let ([x* e*] ...) abody)
        (letrec ([x* e*] ...) abody)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...))
      (AssignedBody (abody)
        (assigned (a* ...) body) => body))

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
      (+ (assigned (a* ...) body) => body)))

  #;(define-language L8
      (terminals
        (symbol (x ))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        le
        (let ([x* e*] ...) abody)
        (letrec ([x* le*] ...) body)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) abody))
      (AssignedBody (abody)
        (assigned (a* ...) body) => body))

  (define-language L8
    (extends L7)
    (Expr (e body)
      (- (lambda (x* ...) abody)
         (letrec ([x* e*] ...) abody))
      (+ le
         (letrec ([x* le*] ...) body)))
    (LambdaExpr (le)
      (+ (lambda (x* ...) abody))))

  #;(define-language L9
      (terminals
        (symbol (x ))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) abody)
        (letrec ([x* le*] ...) body)
        (set! x e)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) abody))
      (AssignedBody (abody)
        (assigned (a* ...) body) => body))

  (define-language L9
    (extends L8)
    (Expr (e body)
      (- le)))
      
  #;(define-language L10
      (terminals
        (symbol (x))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (letrec ([x* le*] ...) body)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) abody)))

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
  
  #;(define-language L11
      (terminals
        (symbol (x f))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (letrec ([x* le*] ...) body)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) fbody))
      (FreeBody (fbody)
        (free (f* ...) body)))

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

  #;(define-language L12
      (terminals
        (symbol (x f l))
        (extended-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (label l)
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (closures ([x* l* f** ...] ...) lbody)
        (primcall pr e* ...)
        (e e* ...))
      (LabelsBody (lbody)
        (labels (l* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) fbody))
      (FreeBody (fbody)
        (free (f* ...) body)))

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

  #;(define-language L13
      (terminals
        (symbol (x f l))
        (extended+closure-primitive (pr))
        (constant (c)))
      (Expr (e body)
        x
        (label l)
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (labels ([l* le*] ...) body)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) body)))
  
  (define-language L13
    (extends L12)
    (terminals
      (- (extended-primitive (pr)))
      (+ (extended+closure-primitive (pr))))
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

  #;(define-language L14
      (terminals
        (symbol (x f))
        (extended+closure-primitive (pr))
        (constant (c)))
      (Program (p)
        (labels ([l* le*] ...) body))
      (Expr (e body)a
        x
        (quote c)
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (primcall pr e* ...)
        (e e* ...))
      (LambdaExpr (le)
        (lambda (x* ...) body)))
  
  (define-language L14
    (extends L13)
    (entry Program)
    (Program (p)
      (+ (labels ([l* le*] ...) l)))
    (Expr (e body)
      (- (labels ([l* le*] ...) body))))

  #;(define-language L15
      (terminals
        (symbol (x f))
        (extended+closure-primitive (pr))
        (constant (c)))
      (Program (p)
        (labels ([l* le*] ...) body))
      (Expr (e body)
        se
        (if e0 e1 e2)
        (begin e* ... e)
        (let ([x* e*] ...) body)
        (primcall pr se* ...)
        (se se* ...))
      (SimpleExpr (se)
        x
        (quote c))
      (LambdaExpr (le)
        (lambda (x* ...) body)))
  
  (define-language L15
    (extends L14)
    (Expr (e body)
      (- x
         (quote c)
         (primcall pr e* ...)
         (e e* ...))
      (+ se
         (primcall pr se* ...)
         (se se* ...)))
    (SimpleExpr (se)
      (+ x
         (quote c))))
  
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
      (primcall vpr se* ...)
      (se se* ...))
    (Effect (e)
      (nop)
      (if p0 e1 e2)
      (begin e* ... e)
      (let ([x* v*] ...) e)
      (primcall epr se* ...)
      (se se* ...))
    (Predicate (p)
      (true)
      (false)
      (if p0 p1 p2)
      (begin e* ... p)
      (let ([x* v*] ...) p)
      (primcall ppr se* ...)))

  #;(define-language L17
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr))
        (constant (c)))
      (Program (prog)
        (labels ((l* le*) ...) l))
      (LambdaExpr (le)
        (lambda (x* ...) body))
      (SimpleExpr (se)
        x
        (label l)
        (quote c))
      (Value (v body)
        (alloc i se)
        se
        (if p0 v1 v2)
        (begin e* ... v)
        (let ([x* v*] ...) body)
        (primcall vpr se* ...)
        (se se* ...))
      (Effect (e)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (let ([x* v*] ...) e)
        (primcall epr se* ...)
        (se se* ...))
      (Predicate (p)
        (true)
        (false)
        (if p0 p1 p2)
        (begin e* ... p)
        (let ([x* v*] ...) p)
        (primcall ppr se* ...)))

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

  #;(define-language L18
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr))
        (constant (c)))
      (Program (prog)
        (labels ((l* le*) ...) l))
      (SimpleExpr (se)
        x
        (label l)
        (quote c))
      (Value (v body)
        (alloc i se)
        se
        (if p0 v1 v2)
        (begin e* ... v)
        (primcall vpr se* ...)
        (se se* ...))
      (Effect (e)
        (set! x v)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (primcall epr se* ...)
        (se se* ...))
      (Predicate (p)
        (true)
        (false)
        (if p0 p1 p2)
        (begin e* ... p)
        (primcall ppr se* ...))
      (LocalsBody (lbody)
        (locals (x* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) lbody)))
  
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

  #;(define-language L19
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr))
        (constant (c)))
      (Program (prog)
        (labels ((l* le*) ...) l))
      (SimpleExpr (se)
        x
        (label l)
        (quote c))
      (Value (v body)
        rhs
        (if p0 v1 v2)
        (begin e* ... v))
      (Effect (e)
        (set! x rhs)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (primcall epr se* ...)
        (se se* ...))
      (Predicate (p)
        (true)
        (false)
        (if p0 p1 p2)
        (begin e* ... p)
        (primcall ppr se* ...))
      (LocalsBody (lbody)
        (locals (x* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) lbody))
      (Rhs (rhs)
        se
        (alloc i se)
        (primcall vpr se* ...)
        (se se* ...)))

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
         (primcall vpr se* ...)
         (se se* ...)))
    (Effect (e)
      (- (set! x v))
      (+ (set! x rhs))))

  #;(define-language L20 
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr))
        (constant (c)))
      (Program (prog)
        (labels ((l* le*) ...) l))
      (SimpleExpr (se)
        x
        (quote c))
      (Value (v body)
        rhs 
        (if p0 v1 v2)
        (begin e* ... v))
      (Effect (e)
        (set! x rhs)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (primcall epr se* ...)
        (se se* ...))
      (Predicate (p)
        (true)
        (false)
        (if p0 p1 p2)
        (primcall ppr se* ...))
      (LocalsBody (lbody)
        (locals (x* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) lbody))
      (Rhs (rhs)
        se
        (alloc i se)
        (primcall vpr se* ...)
        (se se* ...)))

  (define-language L20
    (extends L19)
    (Predicate (p)
      (- (begin e* ... p))))

  #;(define-language L21
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr)))
      (Program (prog) 
        (labels ((l* le*) ...) l))
      (SimpleExpr (se)
        i
        (label l)
        x)
      (Value (v body)
        rhs
        (if p0 v1 v2)
        (begin e* ... v))
      (Effect (e)
        (set! x rhs)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (primcall epr se* ...)
        (se se* ...))
      (Predicate (p)
        (true)
        (false)
        (if p0 p1 p2)
        (primcall ppr se* ...))
      (LocalsBody (lbody)
        (locals (x* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) lbody))
      (Rhs (rhs)
        se
        (alloc i se)
        (primcall vpr se* ...)
       (se se* ...)))
  
  (define-language L21
    (extends L20)
    (terminals
      (- (constant (c))))
    (SimpleExpr (se)
      (- (quote c))
      (+ i)))

  #;(define-language L22
      (entry Program)
      (terminals
        (integer-64 (i))
        (effect+internal-primitive (epr))
        (non-alloc-value-primitive (vpr))
        (symbol (x l))
        (predicate-primitive (ppr)))
      (Program (prog)
        (labels ((l* le*) ...) l))
      (SimpleExpr (se)
        (logand se0 se1)
        (shift-right se0 se1)
        (shift-left se0 se1)
        (divide se0 se1)
        (multiply se0 se1)
        (subtract se0 se1)
        (add se0 se1)
        (mref se0 (maybe se1?) i)
        (label l)
        i
        x)
      (Value (v body)
        rhs
        (if p0 v1 v2)
        (begin e* ... v))
      (Effect (e)
        (mset! se0 (maybe se1?) i se2)
        (set! x rhs)
        (nop)
        (if p0 e1 e2)
        (begin e* ... e)
        (se se* ...))
      (Predicate (p)
        (<= se0 se1)
        (< se0 se1)
        (= se0 se1)
        (true)
        (false)
        (if p0 p1 p2))
      (LocalsBody (lbody)
        (locals (x* ...) body))
      (LambdaExpr (le)
        (lambda (x* ...) lbody))
      (Rhs (rhs)
        se
        (alloc i se)
        (se se* ...)))

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

  (define-pass parse-and-rename : * (e) -> Lsrc ()
    (definitions
      (define process-body
        (lambda (who env body* f)
          (when (null? body*) (error who "invalid empty body"))
          (let loop ([body (car body*)] [body* (cdr body*)] [rbody* '()])
            (if (null? body*)
                (f (reverse rbody*) (Expr body env))
                (loop (car body*) (cdr body*)
                  (cons (Expr body env) rbody*))))))
      (define vars-unique?
        (lambda (fmls)
          (let loop ([fmls fmls])
            (or (null? fmls)
                (and (not (memq (car fmls) (cdr fmls)))
                     (loop (cdr fmls)))))))
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
      (define Expr*
        (lambda (e* env)
          (map (lambda (e) (Expr e env)) e*)))
      (with-output-language (Lsrc Expr)
        (define build-primitive
          (lambda (as)
            (let ([name (car as)] [argc (cdr as)])
              (cons name
                (if (< argc 0)
                    (error who
                      "primitives with arbitrary counts are not currently supported"
                      name)
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
                           (process-body env e*
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
            (map build-primitive primitive-map)))
        (define App
          (lambda (e env)
            (let ([e (car e)] [e* (cdr e)])
              `(,(Expr e env) ,(Expr* e* env) ...))))))
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
    (Expr e initial-env))
  
  (define-pass remove-one-armed-if : Lsrc (e) -> L1 ()
    (Expr : Expr (e) -> Expr ()
      [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))
  
  (define-pass remove-and-or-not : L1 (e) -> L2 ()
    (Expr : Expr (e) -> Expr ()
      [(if (not ,[e0]) ,[e1] ,[e2]) `(if ,e0 ,e2 ,e1)]
      [(not ,[e0]) `(if ,e0 #f #t)]
      [(and) #t]
      [(and ,[e] ,[e*] ...)
       (let f ([e e] [e* e*])
         (if (null? e*)
             e
             `(if ,e ,(f (car e*) (cdr e*)) #f)))]
      [(or) #f]
      [(or ,[e] ,[e*] ...)
       (let f ([e e] [e* e*])
         (if (null? e*)
             e
             (let ([t (make-tmp)])
               `(let ([,t ,e]) (if ,t ,t ,(f (car e*) (cdr e*)))))))]))

  (define-pass make-begin-explicit : L2 (e) -> L3 ()
    (Expr : Expr (e) -> Expr ()
      (definitions
        (define build-begin
          (lambda (body* body)
            (if (null? body*)
                body
                `(begin ,body* ... ,body)))))
      [(let ([,x* ,[e*]] ...) ,[body*] ... ,[body])
       `(let ([,x* ,e*] ...) ,(build-begin body* body))]
      [(letrec ([,x* ,[e*]] ...) ,[body*] ... ,[body])
       `(letrec ([,x* ,e*] ...) ,(build-begin body* body))]
      [(lambda (,x* ...) ,[body*] ... ,[body])
       `(lambda (,x* ...) ,(build-begin body* body))]))

  (define-pass inverse-eta-raw-primitives : L3 (e) -> L4 ()
    (Expr : Expr (e) -> Expr ()
      [(,pr ,[e*] ...) `(primcall ,pr ,e* ...)]
      [,pr (cond
             [(assq pr extended-primitive-map) =>
              (lambda (as)
                (do ((i (cdr as) (fx- i 1))
                     (x* '() (cons (make-tmp) x*)))
                  ((fx=? i 0) `(lambda (,x* ...) (primcall ,pr ,x* ...)))))]
             [else (error who "unexpected primitive" pr)])]))

  (define-pass quote-constants : L4 (e) -> L5 ()
    (Expr : Expr (e) -> Expr ()
      [,c `(quote ,c)]))

  (define-pass remove-complex-constants : L5 (e) -> L6 ()
    (definitions
      (define t* '())
      (define e* '())
      (with-output-language (L6 Expr)
        (define datum->expr
          (lambda (x)
            (cond
              [(pair? x)
               `(primcall cons ,(datum->expr (car x)) ,(datum->expr (cdr x)))]
              [(vector? x)
               (let ([l (vector-length x)] [t (make-tmp)])
                 `(let ([,t (primcall make-vector (quote ,l))])
                    (begin
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
                      ,t)))]
              [(constant? x) `(quote ,x)])))))
    (Expr : Expr (e) -> Expr ()
      [(quote ,d)
       (if (constant? d)
           `(quote ,d)
           (let ([t (make-tmp)])
             (set! t* (cons t t*))
             (set! e* (cons (datum->expr d) e*))
             t))])
    (let ([e (Expr e)])
      (if (null? t*)
          e
          `(let ([,t* ,e*] ...) ,e))))

  (define-pass identify-assigned-variables : L6 (e) -> L7 ()
    (Expr : Expr (e) -> Expr ('())
      [(set! ,x ,[e assigned*]) (values `(set! ,x ,e) (cons x assigned*))]
      [(primcall ,pr ,[e* assigned**] ...)
       (values `(primcall ,pr ,e* ...) (apply union assigned**))]
      [(if ,[e0 assigned0*] ,[e1 assigned1*] ,[e2 assigned2*])
       (values `(if ,e0 ,e1 ,e2) (union assigned0* assigned1* assigned2*))]
      [(begin ,[e* assigned**] ... ,[e assigned*])
       (values `(begin ,e* ... ,e) (apply union assigned* assigned**))]
      [(,[e assigned*] ,[e* assigned**] ...)
       (values `(,e ,e* ...) (apply union assigned* assigned**))]
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
           (difference assigned* x*)))])
    (let-values ([(e assigned*) (Expr e)])
      e))

  (define-pass purify-letrec : L7 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      (definitions
        (define build-let
          (lambda (x* e* a* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) (assigned (,a* ...) ,body)))))
        (define build-letrec
          (lambda (x* e* body)
            (if (null? x*)
                body
                `(letrec ([,x* ,e*] ...) ,body))))
        (define build-begin
          (lambda (body* body)
            (if (null? body*)
                body
                `(begin ,body* ... ,body)))))
      [(letrec ([,x* ,[e*]] ...) (assigned (,a* ...) ,[body]))
       (let loop ([xb* x*] [e* e*]
                  [xs* '()] [es* '()]
                  [xl* '()] [el* '()]
                  [xc* '()] [ec* '()])
         (if (null? xb*)
             (build-let xc* (make-list (length xc*) `(quote #f)) a*
               (build-let xs* es* '()
                 (build-letrec xl* el*
                   (build-begin
                     (map (lambda (xc ec) `(set! ,xc ,ec)) xc* ec*)
                     body))))
             (let ([x (car xb*)] [e (car e*)])
               (nanopass-case (L8 Expr) e
                 [(lambda (,x* ...) ,abody)
                  (guard (not (memq x a*)))
                  (loop (cdr xb*) (cdr e*) xs* es*
                    (cons x xl*) (cons e el*) xc* ec*)]
                 [,x
                  (guard (not (memq x x*)) (not (memq x a*)))
                  (loop (cdr xb*) (cdr e*) (cons x xs*) (cons e es*)
                    xl* el* xc* ec*)]
                 [(primcall ,pr ,e* ...)
                  (guard (effect-free-prim? pr) (memq x a*))
                  (loop (cdr xb*) (cdr e*) (cons x xs*) (cons e es*)
                    xl* el* xc* ec*)]
                 [else (loop (cdr xb*) (cdr e*) xs* es* xl* el*
                         (cons x xc*) (cons e ec*))]))))]))

  (define-pass optimize-direct-call : L8 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      [((lambda (,x* ...) ,[abody]) ,[e* -> e*] ...)
       (guard (fx=? (length x*) (length e*)))
       `(let ([,x* ,e*] ...) ,abody)]))

  (define-pass find-let-bound-lambdas : L8 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      (definitions
        (define build-let
          (lambda (x* e* a* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) (assigned (,a* ...) ,body)))))
        (define build-letrec
          (lambda (x* le* body)
            (if (null? x*)
                body
                `(letrec ([,x* ,le*] ...) ,body)))))
      [(let ([,x* ,[e*]] ...) (assigned (,a* ...) ,[body]))
       (let loop ([xb* x*] [e* e*] [xl* '()] [el* '()] [xo* '()] [eo* '()])
         (if (null? xb*)
             (build-let xo* eo* a* (build-letrec xl* el* body))
             (let ([x (car xb*)] [e (car e*)])
               (nanopass-case (L8 Expr) e
                 [(lambda (,x* ...) ,abody)
                  (guard (not (memq x e*)))
                  (loop (cdr xb*) (cdr e*) (cons x xl*) (cons e el*) xo* eo*)]
                 [else (loop (cdr xb*) (cdr e*) xl* el*
                         (cons x xo*) (cons e eo*))]))))]))

  (define-pass remove-anonymous-lambda : L8 (e) -> L9 ()
    (Expr : Expr (e) -> Expr ()
      [(lambda (,x* ...) ,[abody])
       (let ([t (make-tmp)])
         `(letrec ([,t (lambda (,x* ...) ,abody)]) ,t))]))

  (define-pass convert-assignments : L9 (e) -> L10 ()
    (definitions
      (define lookup
        (lambda (env)
          (lambda (x)
            (cond
              [(assq x env) => cdr]
              [else x]))))
      (define build-env
        (lambda (x* a* env f)
          (let ([t* (map (lambda (x) (make-tmp)) a*)])
            (let ([env (append (map cons a* t*) env)])
              (f (map (lookup env) x*) t* env)))))
      (with-output-language (L10 Expr)
        (define make-boxes
          (lambda (t*)
            (map (lambda (t) `(primcall box ,t)) t*)))
        (define build-let
          (lambda (x* e* body)
            (if (null? x*)
                body
                `(let ([,x* ,e*] ...) ,body))))))
    (Expr : Expr (e [env '()]) -> Expr ()
      [(let ([,x* ,[e*]] ...) (assigned (,a* ...) ,body))
       (build-env x* a* env
         (lambda (x* t* env)
           (let ([box* (make-boxes t*)] [body (Expr body env)])
             `(let ([,x* ,e*] ...) 
                (let ([,a* ,box*] ...)
                  ,body)))))]
      [,x (if (assq x env) `(primcall unbox ,x) x)]
      [(set! ,x ,[e]) `(primcall box-set! ,x ,e)])
    (LambdaExpr : LambdaExpr (le env) -> LambdaExpr ()
      [(lambda (,x* ...) (assigned (,a* ...) ,body))
       (build-env x* a* env
         (lambda (x* t* env)
           (let ([box* (make-boxes t*)] [body (Expr body env)])
             `(lambda (,x* ...)
                (let ([,a* ,box*] ...) ,body)))))]))
  
  (define-pass uncover-free : L10 (e) -> L11 ()
    (Expr : Expr (e) -> Expr (free*)
      [(quote ,c) (values `(quote ,c) '())]
      [,x (values x (list x))]
      [(let ([,x* ,[e* free**]] ...) ,[e free*])
       (values `(let ([,x* ,e*] ...) ,e)
         (apply union (difference free* x*) free**))]
      [(letrec ([,x* ,[le* free**]] ...) ,[body free*])
       (values `(letrec ([,x* ,le*] ...) ,body)
         (difference (apply union free* free**) x*))]
      [(if ,[e0 free0*] ,[e1 free1*] ,[e2 free2*])
       (values `(if ,e0 ,e1 ,e2) (union free0* free1* free2*))]
      [(begin ,[e* free**] ... ,[e free*])
       (values `(begin ,e* ... ,e) (apply union free* free**))]
      [(primcall ,pr ,[e* free**]...)
       (values `(primcall ,pr ,e* ...) (apply union free**))]
      [(,[e free*] ,[e* free**] ...)
       (values `(,e ,e* ...) (apply union free* free**))])
    (LambdaExpr : LambdaExpr (le) -> LambdaExpr (free*)
      [(lambda (,x* ...) ,[body free*])
       (let ([free* (difference free* x*)])
         (values `(lambda (,x* ...) (free (,free* ...) ,body)) free*))])
    (let-values ([(e free*) (Expr e)])
      (unless (null? free*) (error who "found unbound variables" free*))
      e))
      
  (define-pass convert-closures : L11 (e) -> L12 ()
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,x* (lambda (,x** ...) (free (,f** ...) ,[body*]))] ...)
         ,[body])
       (let ([l* (map unique-var x*)] [cp* (map unique-var x*)])
         `(closures ([,x* ,l* ,f** ...] ...)
            (labels ([,l* (lambda (,cp* ,x** ...)
                            (free (,f** ...) ,body*))] ...)
              ,body)))]
      [(,x ,[e*] ...) `(,x ,x ,e* ...)]
      [(,[e] ,[e*] ...)
       (let ([t (make-tmp)])
         `(let ([,t ,e]) (,t ,t ,e* ...)))]))
              
   (define-pass optimize-known-call : L12 (e) -> L12 ()
     (LabelsBody : LabelsBody (lbody env) -> LabelsBody ())
     (LambdaExpr : LambdaExpr (le env) -> LambdaExpr ())
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
      [(closures ([,x* ,l* ,f** ...] ...) ,lbody)
       (let ([size* (map length f**)])
         `(let ([,x* (primcall make-closure (quote ,size*))] ...)
            (begin
              ,(build-closure-set* x* l* f** cp free*) ...
              ,(LabelsBody lbody))))]
      [,x (handle-closure-ref x cp free*)]
      [((label ,l) ,[e*] ...) `((label ,l) ,e* ...)]
      [(,[e] ,[e*] ...) `((primcall closure-code ,e) ,e* ...)])
   (LabelsBody : LabelsBody (lbody) -> Expr ())
   (LambdaExpr : LambdaExpr (le) -> LambdaExpr ()
     [(lambda (,x ,x* ...) (free (,f* ...) ,body))
      `(lambda (,x ,x* ...) ,(Expr body x f*))]))

  (define-pass lift-lambdas : L13 (e) -> L14 ()
    (definitions
      (define *l* '())
      (define *le* '()))
    (Expr : Expr (e) -> Expr ()
      [(labels ([,l* ,[le*]] ...) ,[body])
       (set! *l* (append l* *l*))
       (set! *le* (append le* *le*))
       body])
    (let ([e (Expr e)] [l (make-tmp)])
      `(labels ([,l (lambda () ,e)] [,*l* ,*le*] ...) ,l)))

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
                   (primcall box-set! ,t1 ,t0)
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
            (if (null? e*)
                v
                `(begin ,e* ... ,v)))))
      [(if ,[p0 var0*] ,[v1 var1*] ,[v2 var2*])
       (values `(if ,p0 ,v1 ,v2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[v var*])
       (values `(begin ,e* ... ,v) (apply append var* var**))]
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
            (if (null? e*)
                e
                `(begin ,e* ... ,e)))))
      [(if ,[p0 var0*] ,[e1 var1*] ,[e2 var2*])
       (values `(if ,p0 ,e1 ,e2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[e var*])
       (values `(begin ,e* ... ,e) (apply append var* var**))]
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
            (if (null? e*)
                p
                `(begin ,e* ... ,p)))))
      [(if ,[p0 var0*] ,[p1 var1*] ,[p2 var2*])
       (values `(if ,p0 ,p1 ,p2) (append var0* var1* var2*))]
      [(begin ,[e* var**] ... ,[p var*])
       (values `(begin ,e* ... ,p) (apply append var* var**))]
      [(primcall ,ppr ,[se* var**] ...)
       (values `(primcall ,ppr ,se* ...) (apply append var**))]
      [(let ([,x* ,[v* var**]] ...) ,[p var*])
       (values
         (build-set*! x* v* p build-begin)
         (apply append x* var* var**))])
    (LambdaExpr : LambdaExpr (le) -> LambdaExpr ()
      [(lambda (,x* ...) ,[body var*])
       `(lambda (,x* ...) (locals (,var* ...) ,body))]))
  
  (define-pass flatten-set! : L18 (e) -> L19 ()
    (SimpleExpr : SimpleExpr (se) -> SimpleExpr ())
    (Effect : Effect (e) -> Effect ()
      [(set! ,x ,v) (Value v x)])
    (Value : Value (v x) -> Effect ()
      [,se `(set! ,x ,(SimpleExpr se))]
      [(primcall ,vpr ,[se*] ...) `(set! ,x (primcall ,vpr ,se* ...))]
      [(alloc ,i ,[se]) `(set! ,x (alloc ,i ,se))]
      [(,[se] ,[se*] ...) `(set! ,x (,se ,se* ...))]))   

  (define-pass push-if : L19 (e) -> L20 ()
    (Value : Value (v) -> Value ()
      (definitions
        (define build-begin
          (lambda (e* v)
            (if (null? e*) v `(begin ,e* ... ,v)))))
      [(if ,[p0 e*] ,[v1] ,[v2]) (build-begin e* `(if ,p0 ,v1 ,v2))])
    (Effect : Effect (e) -> Effect ()
      (definitions
        (define build-begin
          (lambda (e* e)
            (if (null? e*) e `(begin ,e* ... ,e)))))
      [(if ,[p0 e*] ,[e1] ,[e2]) (build-begin e* `(if ,p0 ,e1 ,e2))])
    (Predicate : Predicate (p) -> Predicate ('())
      [(begin ,[e*] ... ,[p more-e*]) (values p (append e* more-e*))]))
 
  (define-pass specify-constant-representation : L20 (e) -> L21 ()
    (SimpleExpr : SimpleExpr (se) -> SimpleExpr ()
      [(quote ,c)
       (cond
         [(eq? c #f) false-rep]
         [(eq? c #t) true-rep]
         [(null? c) null-rep]
         [(target-fixnum? c)
          (bitwise-arithmetic-shift-left c fixnum-shift)])]))

  (define-pass expand-primitives : L21 (e) -> L22 ()
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
         [(*) `(multiply ,se0 (shift-right ,se1 ,fixnum-shift))]
         [(/) `(shift-left (divide
                             (shift-right ,se0 ,fixnum-shift)
                             (shift-right ,se1 ,fixnum-shift))
                 ,fixnum-shift)]
         [else (error who "unexpected value primitive" vpr)])]
      [(primcall ,vpr ,se* ...)
       (error who "unexpected value primitive" vpr)])
    (Effect : Effect (e) -> Effect ()
      [(primcall ,epr ,[se0] ,[se1])
       (case epr
         [(box-set!) `(mset! ,se0 #f ,(- box-tag) ,se1)]
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

  (define-pass generate-c : L22 (e) -> * ()
    (definitions
      (define symbol->c-id
        (lambda (sym)
          (let ([ls (string->list (symbol->string sym))])
            (if (null? ls)
                ""
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
      (define emit-function-header
        (lambda (l x*)
          (printf "ptr ~a(" l)
          (unless (null? x*)
            (let loop ([x (car x*)] [x* (cdr x*)])
              (if (null? x*)
                  (printf "ptr ~a" (symbol->c-id x))
                  (begin
                    (printf "ptr ~a, " (symbol->c-id x))
                    (loop (car x*) (cdr x*))))))

          (printf ")"))))
    (emit-function-decl : LambdaExpr (le l) -> * ()
      [(lambda (,x* ...) ,lbody)
       (emit-function-header l x*)
       (printf ";~%")])
    (emit-function-def : LambdaExpr (le l) -> * ()
      [(lambda (,x* ...) ,lbody)
       (emit-function-header l x*)
       (printf " {~%")
       (emit-function-body lbody)
       (printf "}~%~%")])
    (emit-function-body : LocalsBody (lbody) -> * ()
      [(locals (,x* ...) ,body)
       (for-each (lambda (x) (printf "  ptr ~a;~%" (symbol->c-id x))) x*)
       (emit-value body x*)])
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
      [,rhs (let ([rhs (format-rhs rhs)])
              (printf "  return (ptr)~a;\n" rhs))])
    (format-predicate : Predicate (p) -> * (str)
      [(if ,p0 ,p1 ,p2)
       (format "((~a) ? (~a) : (~a))"
         (format-predicate p0)
         (format-predicate p1)
         (format-predicate p2))]
      [(<= ,se0 ,se1)
       (format "((long)~a <= (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(< ,se0 ,se1)
       (format "((long)~a < (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(= ,se0 ,se1)
       (format "((long)~a == (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(true) "1"]
      [(false) "0"])
    (format-simple-expr : SimpleExpr (se) -> * (str)
      [,x (symbol->c-id x)]
      [,i (number->string i)]
      [(label ,l) (format "(*~a)" (symbol->c-id l))]
      [(logand ,se0 ,se1)
       (format "((long)~a & (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(shift-right ,se0 ,se1)
       (format "((long)~a >> (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(shift-left ,se0 ,se1)
       (format "((long)~a << (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(divide ,se0 ,se1)
       (format "((long)~a / (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(multiply ,se0 ,se1)
       (format "((long)~a * (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(subtract ,se0 ,se1)
       (format "((long)~a - (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(add ,se0 ,se1)
       (format "((long)~a + (long)~a)"
         (format-simple-expr se0)
         (format-simple-expr se1))]
      [(mref ,se0 ,se1? ,i) 
       (if se1?
           (format "(*((ptr)((long)~a + (long)~a + ~d)))"
             (format-simple-expr se0)
             (format-simple-expr se1?) i)
           (format "(*((ptr)((long)~a + ~d)))" (format-simple-expr se0) i))])
    (emit-effect : Effect (e) -> * ()
      [(if ,p0 ,e1 ,e2)
       (printf "  if (~a) {~%" (format-predicate p0))
       (emit-effect e1)
       (printf "  } else {~%")
       (emit-effect e2)
       (printf "  }~%")]
      [((label ,l) ,se* ...)
       (printf "  ~a(" (symbol->c-id l))
       (unless (null? se*)
         (let loop ([se (car se*)] [se* (cdr se*)])
           (if (null? se*)
               (printf "(ptr)~a" (format-simple-expr se))
               (begin
                 (printf "(ptr)~a, " (format-simple-expr se))
                 (loop (car se*) (cdr se*))))))
       (printf ");\n")]
      [(,se ,se* ...)
       (printf "  ((ptr (*)(~a))~a)("
         (let loop ([i (length se*)])
           (cond
             [(zero? i) ""]
             [(fx=? i 1) "ptr"]
             [else (format "ptr, ~a" (loop (fx- i 1)))]))
         (format-simple-expr se))
       (unless (null? se*)
         (let loop ([se (car se*)] [se* (cdr se*)])
           (if (null? se*)
               (printf "(ptr)~a" (format-simple-expr se))
               (begin
                 (printf "(ptr)~a, " (format-simple-expr se))
                 (loop (car se*) (cdr se*))))))
       (printf ");\n")]
      [(set! ,x ,rhs)
       (printf "  ~a = (ptr)" (symbol->c-id x))
       (printf "~a;\n" (format-rhs rhs))]
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
    (format-rhs : Rhs (rhs) -> * (str)
      [((label ,l) ,se* ...)
       (format "  ~a(~a)" (symbol->c-id l)
         (if (null? se*)
             ""
             (let loop ([se (car se*)] [se* (cdr se*)])
               (if (null? se*)
                   (format "(ptr)~a" (format-simple-expr se))
                   (format "(ptr)~a, ~a" (format-simple-expr se)
                     (loop (car se*) (cdr se*)))))))]
      [(,se ,se* ...)
       (format "  ((ptr (*)(~a))~a)(~a)"
         (let loop ([i (length se*)])
           (cond
             [(zero? i) ""]
             [(fx=? i 1) "ptr"]
             [else (format "ptr, ~a" (loop (fx- i 1)))]))
         (format-simple-expr se)
         (let loop ([se (car se*)] [se* (cdr se*)])
           (if (null? se*)
               (format "(ptr)~a" (format-simple-expr se))
               (format "(ptr)~a, ~a"
                 (format-simple-expr se)
                 (loop (car se*) (cdr se*))))))]
      [(alloc ,i ,se)
       (if (use-boehm?)
           (format "(ptr)((long)GC_MALLOC(~a) + ~dl)"
             (format-simple-expr se) i)
           (format "(ptr)((long)malloc(~a) + ~dl)"
             (format-simple-expr se) i))]
      [,se (format-simple-expr se)])
    (Program : Program (p) -> * ()
      [(labels ([,l* ,le*] ...) ,l)
       (let ([l (symbol->c-id l)] [l* (map symbol->c-id l*)])
         (printf "#include <stdio.h>\n")
         (if (use-boehm?)
             (printf "#include <gc.h>\n")
             (printf "#include <stdlib.h>\n"))
         (printf "typedef long* ptr;\n")
         (printf "#define PAIR_P(x) (((long)x & ~d) == ~d)\n"
           pair-mask pair-tag)
         (printf "#define NULL_P(x) ((long)x == ~d)\n" null-rep)
         (printf "#define CAR(x) ((ptr)*((ptr)((long)x - ~d)))\n" pair-tag)
         (printf "#define CDR(x) ((ptr)*((ptr)((long)x + ~d - ~d)))\n"
           word-size pair-tag)
         (printf "void print_scheme_value(ptr x) {\n")
         (printf "  long i, vecbytes;\n")
         (printf "  ptr p;\n")
         (printf "  if ((long)x == ~d) {\n" true-rep)
         (printf "    printf(\"#t\");\n")
         (printf "  } else if ((long)x == ~d) {\n" false-rep)
         (printf "    printf(\"#f\");\n")
         (printf "  } else if (NULL_P(x)) {\n")
         (printf "    printf(\"()\");\n")
         (printf "  } else if ((long)x == ~d) {\n" void-rep)
         (printf "    printf(\"(void)\");\n")
         (printf "  } else if (((long)x & ~d) == ~d) {\n"
           fixnum-mask fixnum-tag)
         (printf "    printf(\"%ld\", ((long)x >> ~d));\n" fixnum-shift)
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
         (printf "  } else if (((long)x & ~d) == ~d) {\n" box-mask box-tag)
         (printf "    printf(\"#(box \");\n")
         (printf "    print_scheme_value((ptr)*((ptr)((long)x - ~d)));\n"
           box-tag)
         (printf "    printf(\")\");\n")
         (printf "  } else if (((long)x & ~d) == ~d) {\n"
           vector-mask vector-tag)
         (printf "    // printf(\"got vector %p\\n\", x);\n")
         (printf "    vecbytes = (long)*((ptr)((long)x - ~d));\n" vector-tag)
         (printf "    //printf(\"vecbytes: %ld\\n\", vecbytes);\n")
         (printf "    printf(\"#(\");\n")
         (printf "    for (i = (~d - ~d); i <= vecbytes; i += ~d) {\n"
           word-size vector-tag word-size)
         (printf "      print_scheme_value((ptr)*((ptr)((long)x + i)));\n")
         (printf "      if (i < vecbytes) { printf(\" \"); } \n")
         (printf "    }\n")
         (printf "    printf(\")\");\n")
         (printf "  } else if (((long)x & ~d) == ~d) {\n"
           closure-mask closure-tag)
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

  ;; a little helper mostly shamelesly stolen from 
  ;; the Chez Scheme User's Guide
  (define-syntax with-implicit
    (syntax-rules ()
      [(_ (tid id ...) body0 ... body1)
       (with-syntax ([id (datum->syntax #'tid 'id)] ...)
         body0 ... body1)]))

  ;; a little macro to make building a compiler with tracing that we can turn
  ;; off and on easier.  no support for looping in this, but the syntax is very
  ;; simple:
  ;; (define-compiler my-compiler-name
  ;;   (pass1 unparser)
  ;;   (pass2 unparser)
  ;;   ...
  ;;   pass-to-generate-c)
  ;;
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
                               (system "t > t.out")
                               (call-with-input-file "t.out" read))
                           (with-syntax ([pass (car pass*)]
                                         [unparser (car unparser*)])
                             #`(let ([x (pass x)])
                                 (when (memq 'pass (trace-passes))
                                   (printf "output of pass ~s~%" 'pass)
                                   (pretty-print (unparser x)))
                                 #,(loop (cdr pass*)
                                     (cdr unparser*))))))))))])))

  ;; the definition of our compiler that pulls in all of our passes and runs
  ;; them in sequence checking to see if the programmer wants them traced.
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
    (push-if unparse-L20)
    (specify-constant-representation unparse-L21)
    (expand-primitives unparse-L22)
    generate-c))
