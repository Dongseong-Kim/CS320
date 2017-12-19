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

;; FWAE abstract syntax tree
(define-type FWAE
  [num  (n number?)]
  [add  (left FWAE?) (right FWAE?)]
  [sub  (left FWAE?) (right FWAE?)]
  [with (name id?) (init FWAE?) (body FWAE?)]
  [id   (name symbol?)]
  [app  (app-body FWAE?) (app-param list?)]
  [fun  (fun-arg list?) (fun-body FWAE?)]
  [record (records list?)]
  [getField (r FWAE?) (name id?)])

;; there are three kinds of return values
;; number, function and record
(define-type FWAE-Value
  [numV (n number?)]
  [functionV (fun-arg list?) (fun-body FWAE?) (ds dfrSub?)]
  [recordV (r list?)])

;; dfrSub for deferred substitution
(define-type dfrSub
  [mtSub]
  [aSub (name id?) (value FWAE-Value?) (rest dfrSub?)])

;; element of record list
;; only for the moment before evaluatian(interpret)
;; the return type of parsing is FWAE, thus entry-value is FWAE
(define-type recordEntry
  [entry (name id?) (value FWAE?)])

;; element of record list
;; during interpretation, entry-values of all recordEntrys are also evaluated
;; That is, recordEntrys are converted to recordEntryV, which has FWAE-Value for its entry value
(define-type recordEntryV
  [entryV (name id?) (value FWAE-Value?)])

;; check-duplicates : list-of-symbols -> boolean
;; to check whether there are two or more same symbols in the given list l.
;; if there is no same symbols, return #t. Otherwise, #f
(define (check-duplicates l)
  (cond
    [(not (list? l))                                     (error 'check-duplicates "not a list: ~a" l)]
    [(not (andmap symbol? l))                            (error 'check-duplicates "non-symbol element")]
    [(not (= (length l) (length (remove-duplicates l)))) #f]
    [else #t]))

(test (check-duplicates '(x y z)) #t)
(test (check-duplicates '()) #t)
(test/exn (check-duplicates 'b) "not a list")
(test/exn (check-duplicates '(a b 2 3)) "non-symbol element")
(test (check-duplicates '(x z x)) #f)

;; make-records : list-of-(symbol sexpr) list -> list-of-recordEntry
;; make a list of recordEntry with the given list that contains the information of record
;; if duplicate identifiers appear, report an error
(define (make-records l syms)
  (cond
    [(null? l) empty]
    [(not (= (length (first l)) 2)) (error 'make-records "bad syntax: invalid record: ~a" (first l))]
    [(not (symbol? (first (first l)))) (error 'make-records "bad syntax: ~a is not a symbol" (first (first l)))]
    [else (cond
            [(check-duplicates (append syms (list (first (first l)))))
             (append (list (entry (parse-sexpr (first (first l))) (parse-sexpr (second (first l)))))
                     (make-records (rest l) (append (list (first (first l))) syms)))]
            [else (error 'make-records "duplicate fields: ~a in ~a" (first (first l)) syms)])]))

; testcase for make-records function is written below parse-sexpr function

;; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAE
(define (parse-sexpr sexp)
  (match sexp
    [(? number?)               (num sexp)]
    [(list '+ l r)             (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r)             (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with (parse-sexpr x) (parse-sexpr i) (parse-sexpr b))]
    [(list 'fun l b)           (fun (map parse-sexpr (if (check-duplicates l) l (error 'parse-sexpr "bad syntax: ~a" sexp))) (parse-sexpr b))]
    [(list 'record l ...)      (record (make-records l empty))]
    [(list 'getField f i)      (getField (parse-sexpr f) (parse-sexpr i))]
    [(list f l ...)            (app (parse-sexpr f) (map parse-sexpr l))]
    [(? symbol?)               (cond
                                  [(symbol=? '+ sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [(symbol=? '- sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [(symbol=? 'with sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [(symbol=? 'fun sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [(symbol=? 'getField sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [(symbol=? 'record sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                                  [else (id sexp)])]
    [else (error 'parse-sexpr "bad syntax: ~a" sexp)]))

(test/exn (make-records (list '(a 10) '(b 10) '(b 20)) empty) "duplicate fields")
(test/exn (make-records '((a 20) (+ 2 3)) empty) "invalid record")
(test/exn (make-records '((a 10) (record (b 20))) empty) "cannot be an identifier")
(test/exn (make-records '((f 20) (2 3)) empty) "not a symbol")
(test (make-records (list '(a 10) '(b 20)) empty) (list (entry (id 'a) (num 10)) (entry (id 'b) (num 20))))
(test (make-records empty empty) empty)

(test/exn (parse-sexpr '{with {+ 10} {- + 1}}) "cannot be an identifier")
(test/exn (parse-sexpr '{record {a 10} {b 20} {fun 30}}) "cannot be an identifier")

;; parses a string to AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))


;; lookup-ds : symbol dfrSub -> FWAE-Value
;; to check whether the value of given identifier is contained in dfrSub
;; if exists, return the value
(define (lookup-ds name ds)
  (cond
    [(equal? ds (mtSub))          (error 'lookup-ds "unknown identifier: ~a" name)]
    [(equal? (id-name (aSub-name ds)) name) (aSub-value ds)]
    [else                         (lookup-ds name (aSub-rest ds))]))

(test (lookup-ds 'g (aSub (id 'a) (numV 10) (aSub (id 'g) (numV 20) (mtSub)))) (numV 20))
(test/exn (lookup-ds 'b (aSub (id 'a) (numV 20) (aSub (id 'c) (numV 20) (mtSub)))) "unknown identifier")
(test/exn (lookup-ds 'a (mtSub)) "unknown identifier")

;; lookup-record : id FWAE-Value -> FWAE-Value
;; find FWAE-Values corresponding the given identifier in record
(define (lookup-record name rv)
  (cond
    [(not (recordV? rv)) (error 'lookup-record "not recordV: ~a" rv)]
    [(null? (recordV-r rv)) (error 'lookup-record "no such field: ~a" name)]
    [(symbol=? (id-name name) (id-name (entryV-name (first (recordV-r rv))))) (entryV-value (first (recordV-r rv)))]
    [else (lookup-record name (recordV (rest (recordV-r rv))))]))

(test (lookup-record (id 'x)
                     (recordV (list (entryV (id 'y) (numV 10))
                                    (entryV (id 'x) (recordV (list (entryV (id 'x)
                                                                           (functionV (list (id 'a) (id 'b) (id 'c)) (add (add (id 'b) (id 'c)) (id 'a)) (mtSub))))))))) (recordV (list (entryV (id 'x) (functionV (list (id 'a) (id 'b) (id 'c)) (add (add (id 'b) (id 'c)) (id 'a)) (mtSub))))))
(test/exn (lookup-record (id 'x) (functionV (list (id 'x)) (id 'x) (aSub (id 'x) (numV 3) (mtSub)))) "not recordV")
(test/exn (lookup-record (id 'x) (recordV (list (entryV (id 'y) (recordV (list (entryV (id 'x) (numV 10)))))))) "no such field")


;; dfrsub-for-function : list-of-id list-of-FWAE-Value dfrSub -> dfrSub
;; to match arguments to corresponding parameters and store them in new dfrSub
(define (dfrsub-for-function arg param ds)
  (cond
    [(null? arg) ds]
    [else (aSub (first arg) (first param) (dfrsub-for-function (rest arg) (rest param) ds))]))

(test (dfrsub-for-function (list (id 'a) (id 'b) (id 'c)) (list (numV 10) (recordV (list (entryV (id 'x) (numV 20)))) (functionV (list (id 'z)) (add (num 1) (num 2)) (mtSub))) (mtSub)) (aSub (id 'a) (numV 10) (aSub (id 'b) (recordV (list (entryV (id 'x) (numV 20)))) (aSub (id 'c) (functionV (list (id 'z)) (add (num 1) (num 2)) (mtSub)) (mtSub)))))
(test (dfrsub-for-function empty empty (aSub (id 'x) (numV 10) (mtSub))) (aSub (id 'x) (numV 10) (mtSub)))

;; make-record-entry-v : list-of-recordEntry dfrSub -> list-of-recordEntryV
;; to convert the value of each entry from FWAE to FWAE-Value
(define (make-record-entry-v l ds)
  (cond
    [(null? l) empty]
    [else (append (list (entryV (entry-name (first l)) (eval (entry-value (first l)) ds))) (make-record-entry-v (rest l) ds))]))

; testcase for make-record-entry-v function is written below eval function

;; eval : FWAE dfrSub -> FWAE-Value
;; evaluates FWAE expressions by reducing them to FWAE-Value
(define (eval expr ds)
  (type-case FWAE expr
    [num (n) (numV n)]
    [add (l r) (local [(define l-eval (eval l ds)) (define r-eval (eval r ds))]
                          (cond
                            [(and (numV? l-eval) (numV? r-eval)) (numV (+ (numV-n (eval l ds)) (numV-n (eval r ds))))]
                            [else (error 'eval "at least one of them is not a numV: ~a ~a" l-eval r-eval)]))]
    [sub (l r) (local [(define l-eval (eval l ds)) (define r-eval (eval r ds))]
                          (cond
                            [(and (numV? l-eval) (numV? r-eval)) (numV (- (numV-n (eval l ds)) (numV-n (eval r ds))))]
                            [else (error 'eval "at least one of them is not a numV: ~a ~a" l-eval r-eval)]))]
    [with (bound-id named-expr bound-body) (eval bound-body (aSub bound-id (eval named-expr ds) ds))]
    [id (name) (lookup-ds name ds)]
    [app (b p) (local [(define ftn (eval b ds))]
                 (cond
                   [(not (functionV? ftn)) (error 'eval "not a function expression: ~a" b)]
                   [(not (list? p)) (error 'eval "parameter is not given as a list: ~a" p)]
                   [(not (= (length (functionV-fun-arg ftn)) (length p))) (error 'eval "wrong arity: ~a is given for ~a" p (functionV-fun-arg ftn))]
                   [else (eval (functionV-fun-body ftn) (dfrsub-for-function (functionV-fun-arg ftn) (map eval p (make-list (length p) ds)) ds))]))]
    [fun (a b) (functionV a b ds)]
    [record (l) (recordV (make-record-entry-v l ds))]
    [getField (r i) (lookup-record i (eval r ds))]))

(test (make-record-entry-v (list (entry (id 'x) (add (num 1) (num 2)))) (mtSub)) (list (entryV (id 'x) (numV 3))))
(test (make-record-entry-v (list (entry (id 'y) (sub (id 'z) (num 3)))) (aSub (id 'a) (numV 10) (aSub (id 'z) (numV 4) (mtSub)))) (list (entryV (id 'y) (numV 1))))

(test/exn (eval (parse "{+ 2 {record {x 10}}}") (mtSub)) "not a numV")
(test/exn (eval (parse "{- {fun {x y z} {+ x {+ y z}}} 2}") (mtSub)) "not a numV")

;; eval-result: FWAE-Value -> (if numV)number || (if functionV)'function || (if recordV)'record
;; if the result is numV, return its value in number
;; if the result is functionV, return 'function
;; if the result is recordV, return 'record
(define (eval-result value)
  (cond
    [(numV? value) (numV-n value)]
    [(functionV? value) 'function]
    [(recordV? value) 'record]
    [else (error 'eval-result "not a FWAE-Value: ~a" value)]))

(test (eval-result (eval (parse "2") (mtSub))) 2)
(test (eval-result (eval (parse "{fun {x y} {+ x {+ y z}}}") (aSub (id 'z) (numV 10) (mtSub)))) 'function)
(test (eval-result (eval (parse "{with {x {record {y 10}}} x}") (mtSub))) 'record)

;; run : string -> number || symbol
;; if evaluation results in a number (in fact, numV), return the number
;; otherwise, return symbol ('function or 'record)
(define (run str)
  (eval-result (eval (parse str) (mtSub))))

(test (run "{record {a 10} {b {+ 1 2}}}")
      'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}")
      3)
(test/exn (run "{getField {record {b 10} {b {+ 1 2}}} b}")
          "duplicate fields")
(test/exn (run "{getField {record {a 10}} b}")
          "no such field")
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}")
      12)
(test (run "{getField {record {r {record {z 0}}}} r}")
      'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}")
      0)
(test/exn (run "{record {z {getField {record {z 0}} y}}}")
          "no such field")
(test (run "{with {f {fun {a b} {+ a b}}}
                  {with {g {fun {x} {- x 5}}}
                        {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}}
                  {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}}
                  {with {g {fun {x} {+ x x}}}
                        {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {getField {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {getField a a} b}}}
                  {with {g {fun {x} {+ 5 x}}}
                        {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}}
                  {getField {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {getField {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}}
                  {f {getField {getField {record {a {record {a 10} {b {- 5 2}}}} {b {getField {record {x 50}} x}}} a} b}}}") 8)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") 'record)
(test (run "{record {a {- 2 1}}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {- 2 1}}} a}") 1)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)


(test (run "{fun {x y z} {+ z {- x y}}}") 'function)
(test (run "{fun {} 3}") 'function)
(test (run "{{fun {} 3}}") 3)
(test (run "{with {x {record {y 10} {z 20} {w 30}}} {getField x w}}") 30)
(test (run "{with {f {fun {} {record {x 10}}}} {getField {f} x}}") 10)