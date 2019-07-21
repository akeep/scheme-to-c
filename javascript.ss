;;; Copyright (c) 2013 Andrew W. Keep
;;; Copyright (c) 2019 Amirouche Boubekki
;;;
;;; See the accompanying file Copyright for details
;;;
;;; A nanopass compiler developed to use as a demo during Clojure Conj 2013.
;;; modified to output javascript code.
;;;
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
;;;
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
;;; (my-tiny-compile <exp>) my-tiny-compile is the main interface the
;;;     compiler, where <exp> is a quoted expression for the compiler
;;;     to evaluate.  This procedure will run the nanopass parts of
;;;     the compiler, produce a javascript output file in t.js, run it
;;;     with nodejs directing its output to t.out, and finally use the
;;;     Scheme reader to read t.out and return the value to the host
;;;     Scheme system.  For example, if we wanted to run a program
;;;     that calculates the factorial of 5, we could do the following:
;;;     (my-tiny-compile '(letrec ([f (lambda (n) (if (= n 0) 1 (* n
;;;     (f (- n 1)))))]) (f 10)))
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
;;; Internals that are exported to make them available for programmers
;;; experimenting with the compiler.
;;;
;;; TBD
;;;
;;;
(import (only (chezscheme) import)
        (nanopass)
        (rnrs)
        (only (implementation-helpers) printf format system pretty-print))
(import (only (chezscheme) eval))


(define (pk . args)
  (display args)(newline)
  (car (reverse args)))

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
    '((times . 2) (add . 2) (cons . 2) (make-vector . 1) (box . 1)))

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

  ;;; Language 3: removes multiple expressions from the body of
  ;;; lambda, let, and letrec (to be replaced with a single begin
  ;;; expression that contains the expressions from the body).
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

  (define-language L4
    (extends L3)
    (Expr (e body)
      (- (letrec ([x* e*] ...) body))))

  (define-language L5
    (extends L4)
    (Expr (e body)
      (- (let ([x* e*] ...) body))))

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
  (trace-define-pass parse-and-rename : * (e) -> Lsrc ()
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
  (trace-define-pass remove-one-armed-if : Lsrc (e) -> L1 ()
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

  ;;; pass: make-begin-explicit : L2 -> L3
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
                               (gen-c x))
			   (with-syntax ([pass (car pass*)]
					 [unparser (car unparser*)])
			     #`(let ([x (pass x)])
				 (when (memq 'pass (trace-passes))
				   (printf "output of pass ~s~%" 'pass)
				   (pretty-print (unparser x)))
				 #,(loop (cdr pass*)
				     (cdr unparser*))))))))))])))


  (trace-define-pass letrec-as-let-and-set : L3 (e) -> L4 ()
    (Expr : Expr (e) -> Expr ()
          [(letrec ([,x ,[e]]) ,[body])
           `(let ((,x ,e))
              ,body)]
          [(letrec ([,x* ,[e*]] ...) ,[body])
           (let ((void* (map (lambda _ `(void)) x*)))
             `(let ([,x* ,void*] ...)
                (begin [set! ,x* ,e*] ...
                       ,body)))]))

(trace-define-pass let-as-lambda : L4 (e) -> L5 ()
    (Expr : Expr (e) -> Expr ()
          [(let ([,x* ,[e*]] ...) ,[body])
           `((lambda (,x* ...) ,body) ,e* ...)]))

(trace-define-pass cps : L5 (e) -> L5 ()
    (Expr : Expr (e) -> Expr ()
          [(if ,[e0] ,[e1] ,[e2])
           `(lambda (k)
              (,e0
               (lambda (b)
                 (if b
                     (,e1 k)
                     (,e2 k)))))]
          [(set! ,x ,[e])
           `(lambda (k)
              (set! ,x ,e)
              (k (void)))]
          [(begin ,[e*] ... ,[e])
           (pk '!!!!!!!)
           `(lambda (k)
              ,(let f ((e* e*))
                 ;; the continuation of expressions that are in the
                 ;; `begin` form are thrown away except the last.
                 (if (null? e*)
                     `(,e k) ;; return the result of the last expression
                     `(,(car e*) (lambda (,(make-tmp)) ,(f (cdr e*)))))))]
          [(lambda (,x* ...) ,[body])
           `(lambda (k)
              `lambda-definition
              (k (lambda (ky ,x* ...) ,(if (symbol? body) `(ky ,body) `(,body ky)))))]
          [(quote ,d) `(lambda (k) (k ,d))]
          ;; primitive application
          [(,pr ,[e*] ...)
           `(lambda (k)
              (k (,pr ,e* ...)))]
          ;; lambda application
          [(,[e0] ,[e*] ...)
           `(lambda (k)
              `lambda-application
              (,e0 (lambda (a)
                     (a k (,e* (lambda (kk) kk)) ...))))]))




  ;;; the definition of our compiler that pulls in all of our passes and runs
  ;;; them in sequence checking to sexe if the programmer wants them traced.
  (define-compiler my-tiny-compile
    (parse-and-rename unparse-Lsrc)
    (remove-one-armed-if unparse-L1)
    (remove-and-or-not unparse-L2)
    (make-begin-explicit unparse-L3)
    (letrec-as-let-and-set unparse-L4)
    (let-as-lambda unparse-L5)
    (cps unparse-L5)
    (lambda (x) (unparse-L5 x)))

;; (define program
;;    '(letrec ((input 42)
;;              (odd? (lambda (x) (not (even? x))))
;;              (even? (lambda (x) (if (= x 0) #t (not (odd? (- x 1)))))))
;;       (odd? input)))

(define program `(letrec ((abc '42))
                   abc))

;; (define program
;;   '(let ((abc '42)
;;          (def '101))
;;      '1337
;;      (add abc (times def '100))))

;; (pk 'scheme (eval program))

(define add (lambda (a b)
              (pk 'add a b)
              (+ a b)))

(define times (lambda (a b)
                (pk 'times a b)
                (* a b)))

(define program
  '(let ((square (lambda (value) (times value value))))
     (square '1337)))

(define program
  `(let ((XXX '10)
         (YYY '20))
     (add XXX (times YYY '3))))

(pk 'compiled ((eval (my-tiny-compile program)) pk))
