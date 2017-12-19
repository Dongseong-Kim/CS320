#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

;;-----------------------------------------------------------------------------

(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (params list?)
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-list list?)]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [try-catch (try KCFAE?)
             (catch KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (params list?)
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse : S-expr -> KCFAE
;; to convert s-expression to KCFAE expression
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (cond
                      [(symbol=? sexp '+) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp '-) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'fun) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'if0) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'withcc) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'try) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'throw) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [(symbol=? sexp 'catch) (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw")]
                      [else (id sexp)])]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (fun (map parse (second sexp)) (parse (third sexp)))]
       [(if0) (if0 (parse (second sexp))
                   (parse (third sexp))
                   (parse (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse (third sexp)))]
       [(try) (try-catch (parse (second sexp)) (parse (fourth sexp)))]
       [(throw) (if (= (length sexp) 1)
                    (throw)
                    (error 'parse "Do not use as a symbol: + - fun if0 withcc try catch throw"))]
       [else (app (parse (first sexp)) (map parse (rest sexp)))])]))

;; test: parse---------------------------------------------
(test (parse 3) (num 3))
(test (parse 'x) (id 'x))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{- 1 2}) (sub (num 1) (num 2)))
(test (parse '{fun {x} x}) (fun (list (id 'x)) (id 'x)))
(test (parse '{1 2}) (app (num 1) (list (num 2))))
(test (parse '{if0 0 1 2}) (if0 (num 0) (num 1) (num 2)))
(test (parse '{withcc x 2}) (withcc 'x (num 2)))
(test (parse '{try (+ 2 3) catch (- 2 3)}) (try-catch (add (num 2) (num 3)) (sub (num 2) (num 3))))
(test (parse '{try {{fun {x y} {+ x y}} 2 {throw}} catch z}) (try-catch (app (fun (list (id 'x) (id 'y)) (add (id 'x) (id 'y))) (list (num 2) (throw))) (id 'z)))
(test (parse '{{fun {x y} {try y catch x}} (try {+ 2 4} catch {throw}) {throw}}) (app (fun (list (id 'x) (id 'y)) (try-catch (id 'y) (id 'x))) (list (try-catch (add (num 2) (num 4)) (throw)) (throw))))
(test/exn (parse '{throw 1 2 3}) "Do not use as a symbol")
(test (parse '{throw}) (throw))
;; --------------------------------------------------------

;; parses a string to AST
(define (parse-string str)
  (parse (string->sexpr str)))

;; ----------------------------------------

;; dfrsub-for-function : list-of-id list-of-KCFAE-Value dfrSub (KCFAE-Value -> alpha) -> alpha
;; to make dfrSub for fucntion call
;; params is list of parameters of closureV which will be used for function call
;; args is list of arguments and newds is dfrSub for function call
;; k is continuation denoting what to do after making newds
(define (dfrsub-for-function params args newds k)
  (cond
    [(null? args) (k newds)]
    [else (dfrsub-for-function (rest params) (rest args) (aSub (id-name (first params)) (first args) newds) k)]))

;; interp-args : dfrSub dfrSub list-of-id list-of-KCFAE (KCFAE-Value -> alpha) (KCFAE-Value -> alpha) list-of-KCFAE-Value
;; to interpret arguments consequently and send resulting argument list to dfrsub-for-function function
;; ds is dfrSub of caller function which is used for evaluating each argument
;; fun-ds is dfrSub of closureV which will be used for function call and params is list of parameters of the closureV
;; k is continuation denoting what to do after interpreting all arguments and making new dfrSub for function call
;; arg-list is a list storing the result of evaluation of each argument
(define (interp-args ds fun-ds params args k exception-k arg-list)
  (if (null? args)
      (dfrsub-for-function params arg-list fun-ds k)
      (interp (first args) ds (lambda (arg) (interp-args ds fun-ds params (rest args) k exception-k (append arg-list (list arg)))) exception-k)))

; tests for above two functions are written below lookup function

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) (KCFAE-Value -> alpha) -> alpha
;; to evaluate the given KCFAE using continuation passing style
(define (interp a-fae ds k exception-k)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2)))
                                 exception-k))
                       exception-k)]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2)))
                                 exception-k))
                       exception-k)]
    [id (name) (k (lookup name ds))]
    [fun (params body-expr)
         (k (closureV params body-expr ds))]
    [app (fun-expr arg-list)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (type-case KCFAE-Value fun-val
                     [closureV (params body ds1)
                               (if (= (length params) (length arg-list))
                                   (interp-args ds ds1 params arg-list (lambda (newds) (interp body newds k exception-k)) exception-k empty)
                                   (error 'interp "wrong arity: ~a ~a in ~a" params arg-list a-fae))]
                     [contV (newk)
                            (if (= 1 (length arg-list))
                                (interp (first arg-list) ds (lambda (val) (newk val)) exception-k)
                                (error 'interp "continuation : only single argument"))]
                     [else (error 'interp "not a function")]))
                 exception-k)]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k exception-k)
                       (interp else-expr ds k exception-k)))
                 exception-k)]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k exception-k)]
    [try-catch (try-expr catch-expr) (interp try-expr ds k (lambda () (interp catch-expr ds k exception-k)))]
    [throw () (exception-k)]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; test: num-op------------------------------
(test (num+ (numV 10) (numV 20)) (numV 30))
(test (num- (numV 20) (numV 10)) (numV 10))
;; ------------------------------------------

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

;; lookup
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

;; test: numzero?--------------------------------------------------------------------------------
(test (numzero? (numV 0)) #t)
(test (numzero? (num- (numV 2) (numV 2))) #t)
(test (numzero? (interp (app (fun (list (id 'x)) (add (id 'x) (id 'x))) (list (num 2))) (mtSub) identity identity)) #f)
;; ----------------------------------------------------------------------------------------------
;; test: lookup----------------------------------------------------------------------------------
(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 42) (aSub 'x (numV 20) (mtSub))))) (numV 42))
(test/exn (lookup 'y (aSub 'x (numV 0) (mtSub))) "free variable")
;; ----------------------------------------------------------------------------------------------
;; test: dfrsub-for-function---------------------------------------------------------------------
(test (dfrsub-for-function (list (id 'x) (id 'y)) (list (numV 1) (numV 2)) (mtSub) (lambda (newds) (interp (add (id 'x) (id 'y)) newds identity identity))) (numV 3))
(test (dfrsub-for-function (list (id 'x) (id 'y)) (list (closureV (list (id 'x)) (add (id 'x) (id 'x)) (mtSub)) (numV 21)) (mtSub) (lambda (newds) (interp (app (id 'x) (list (id 'y))) newds identity identity))) (numV 42))
;; tests for dfrsub-for-function are also included in tests for interp-args, for interp-args function calls dfrsub-for-function
;; ----------------------------------------------------------------------------------------------
;; test: interp-args-----------------------------------------------------------------------------
(test (interp-args (aSub 'x (numV 3) (mtSub)) (mtSub) (list (id 'x)) (list (add (id 'x) (id 'x))) identity identity empty) (aSub 'x (numV 6) (mtSub)))
(test (interp-args (aSub 'x (closureV (list (id 'x) (id 'y)) (add (id 'x) (id 'y)) (mtSub)) (mtSub)) (mtSub) (list (id 'x)) (list (app (id 'x) (list (num 3) (num 4)))) identity identity empty) (aSub 'x (numV 7) (mtSub)))
(test (interp-args (aSub 'x (closureV (list (id 'x) (id 'y)) (try-catch (id 'x) (id 'y)) (mtSub)) (mtSub)) (mtSub) (list (id 'x)) (list (app (id 'x) (list (throw) (num 4)))) identity (lambda () (numV 42)) empty) (numV 42))
;; ----------------------------------------------------------------------------------------------

;; interp-expr : KCFAE-Value -> number-or-'function
(define (interp-expr a-fae)
  (type-case KCFAE-Value a-fae
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

;; run : string -> number || symbol
;; if evaluation results in a number (in fact, numV), return the number
;; otherwise, return 'function
(define (run str)
  (interp-expr (interp (parse-string str) (mtSub) identity (lambda () (error 'interp "no exception handling")))))

;; tests----------------------------------------------------------------

  (test (run "{try 7 catch 8}")
        7)
  (test (run "{try {throw} catch 8}")
        8)
  (test (run "{try {+ 1 {throw}} catch 8}")
        8)
  (test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
        8)
  (test (run "{try {try {throw} catch 8} catch 9}")
        8)
  (test (run "{try {try {throw} catch {throw}} catch 9}")
        9)
  (test (run "{try {try 7 catch {throw}} catch 9}")
        7)
  (test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
	8)

; multiple arguments (5)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

; exceptions (35)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; exit from recursive function using continuation
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110) ; exit from recursive function using try-catch
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54) ; equal? for multiple recursive try-catch
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464) ; recursive try-catch throwing (1)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}") 54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)

; multiple arguments (6)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 1099)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 11053)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}") 0)
(test (run "{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}") 64)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}") 'function)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}") 42)

; exceptions (4)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}") 4242)
(test (run "{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}") 33)
(test (run "{try {try {throw} catch {try {throw} catch {try {throw} catch {+ {withcc k {try {throw} catch {k 0}}} {throw}}}}} catch 0}") 0)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}") 4242)

;; additional tests-----------------------------------------------------------------------/---------------------------------------------
(test (run "{{fun {x y z} {+ x {+ y z}}} {{fun {x} {+ 1 x}} 1} {{fun {} 2}} 1}") 5)
(test (run "{{fun {x y} {+ x y}} {+ 1 {withcc second {+ 2 {second 3}}}} 2}") 6)
(test (run "3") 3)
(test/exn (run "x") "free variable")
(test (run "{+ 1 2}") 3)
(test (run "{- 2 1}") 1)
(test (run "{fun {x} x}") 'function)
(test (run "{if0 0 1 2}") 1)
(test (run "{withcc x 2}") 2)
(test (run "{try {+ 2 3} catch {- 2 3}}") 5)
(test (run "{try {{fun {x y} {+ x y}} 2 {throw}} catch 3}") 3)
(test (run "{+ {try {{fun {x y} {try x catch y}} 42 {throw}} catch {withcc foo {foo 2}}} 1}") 3)
(test (run "{try {withcc foo {try {withcc bar {try {+ 2 {throw}} catch {fun {x y} {fun {z} {+ x z}}}}} catch 42}} catch 43}") 'function)
(test (run "{try {withcc foo {try {withcc bar {try {+ {bar 2} {throw}} catch {fun {x y} {fun {z} {+ x z}}}}} catch 42}} catch 43}") 2)
(test (run "{try {- 100 {withcc foo {{fun {x} {try x catch {foo 10}}} {{fun {} {throw}}}}}} catch 0}") 0)
(test (run "{try {- 100 {withcc foo {{fun {x} {try x catch {foo 10}}} {{fun {} {{fun {} {throw}}}}}}}} catch 0}") 0)
(test (run "{try {{fun {x} {try {x} catch 0}} {{fun {} {{fun {} {{fun {x} {try {throw} catch {{fun {} {throw}}}}} 1}}}}}} catch 2}") 2)
(test (run "{{fun {x} {try {x 2} catch 42}} {fun {x} {throw}}}") 42)
(test (run "{{fun {x} {try {x 2} catch 42}} {withcc foo {{fun {x} {foo {fun {x} {throw}}}} 2}}}") 42)
(test (run "{+ 2 {withcc foo {{fun {x y} {+ x y}} {try {{fun {} {throw}}} catch {foo 3}} 0}}}") 5)
(test (run "{{fun {x y} {+ x y}} {withcc foo {+ 3 {foo 2}}} 2}") 4)