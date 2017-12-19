#lang plai

;; BFAE abstract syntax tree
(define-type BFAE
  [num (n number?)]
  [add (lhs BFAE?) (rhs BFAE?)]
  [sub (lhs BFAE?) (rhs BFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BFAE?)]
  [app (fun-expr BFAE?) (arg-expr BFAE?)]
  [newbox (val-expr BFAE?)]
  [setbox (box-expr BFAE?) (val-expr BFAE?)]
  [openbox (box-expr BFAE?)]
  [seqn (expr-one BFAE?) (other-expr list?)]
  [rec (records list?)]
  [get (record BFAE?) (target id?)]
  [setrecord (record BFAE?) (target id?) (val-expr BFAE?)])

;; there are three kinds of values
;; number, function, box and record
(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds dfrSub?)]
  [boxV (address integer?)]
  [recordV (record list?)])

;; dfrSub for deferred substitution
(define-type dfrSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds dfrSub?)])

;; Store for implementing simple memory architecture
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])

;; entry of record
;; entry-value is the address at which data is assigned in Store
(define-type recordEntry
  [entry (name id?) (value integer?)])

;; when evaluating BFAE, return value is a pair of value and store
;; for updating store which might be changed
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

;; make-entries : (symbol, sexpr) -> (<id>, <BFAE>)
;; to make entries of given record
(define (make-entries l)
  (cond
    [(= 2 (length l)) (list (parse-sexpr (first l)) (parse-sexpr (second l)))]
    [else (error 'make-entries "l should be a pair of two s-expression : ~a" l)]))

;; parse-sexpr : sexpr -> BFAE
;; to convert s-expressions into BFAE
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'fun (list p) b) (fun p (parse-sexpr b))]
    [(list 'newbox val) (newbox (parse-sexpr val))]
    [(list 'setbox box val) (setbox (parse-sexpr box) (parse-sexpr val))]
    [(list 'openbox box) (openbox (parse-sexpr box))]
    [(list 'seqn one other ...) (seqn (parse-sexpr one) (map parse-sexpr other))]
    [(list 'rec l ...) (rec (map make-entries l))]
    [(list 'get record name) (get (parse-sexpr record) (parse-sexpr name))]
    [(list 'set record name val) (setrecord (parse-sexpr record) (parse-sexpr name) (parse-sexpr val))]
    [(list f a) (app (parse-sexpr f) (parse-sexpr a))]
    [(? symbol?) (cond
                   [(symbol=? '+ sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? '- sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'fun sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'newbox sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'setbox sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'openbox sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'seqn sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'rec sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'set sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [(symbol=? 'get sexp) (error 'parse-sexpr "bad syntax: cannot be an identifier: ~a" sexp)]
                   [else (id sexp)])]
    [else (error 'parse-sexpr "bad syntax: ~a" sexp)]))

(test (make-entries '{y 2}) (list (id 'y) (num 2)))
(test (map make-entries '{{x 1} {y 2} {z 3}}) (list (list (id 'x) (num 1)) (list (id 'y) (num 2)) (list (id 'z) (num 3))))
(test/exn (parse-sexpr '{fun {openbox} {+ openbox 2}}) "cannot be an identifier")
(test/exn (parse-sexpr 'fun) "cannot be an identifier")
(test (parse-sexpr 'seqne) (id 'seqne))
(test/exn (parse-sexpr '{newbox}) "bad syntax")
(test (parse-sexpr '{newbox {+ 2 3}}) (newbox (add (num 2) (num 3))))
(test (parse-sexpr '{setbox {newbox 5} {{fun {x} {+ 2 x}} 5}}) (setbox (newbox (num 5)) (app (fun 'x (add (num 2) (id 'x))) (num 5))))
(test (parse-sexpr '{openbox {newbox {openbox {newbox {- 2 3}}}}}) (openbox (newbox (openbox (newbox (sub (num 2) (num 3)))))))
(test (parse-sexpr '{seqn {+ 2 3} x}) (seqn (add (num 2) (num 3)) (list (id 'x))))
(test (parse-sexpr '{rec {x 1} {y 2}}) (rec (list (list (id 'x) (num 1)) (list (id 'y) (num 2)))))
(test (parse-sexpr '{get {rec {x 1}} y}) (get (rec (list (list (id 'x) (num 1)))) (id 'y)))
(test (parse-sexpr '{set {rec {x 1}} x {{fun {y} {+ y 1}} 41}}) (setrecord (rec (list (list (id 'x) (num 1)))) (id 'x) (app (fun 'y (add (id 'y) (num 1))) (num 41))))
(test/exn (parse-sexpr '{+ 2 rec}) "cannot be an identifier")
(test/exn (parse-sexpr '{rec {set 2}}) "cannot be an identifier")

;; parses a string to AST
(define (parse str)
  (parse-sexpr str))

;; lookup-ds : symbol dfrSub -> BWAE-Value
;; to check whether the value of the given identifier is contained in dfrSub
;; if exists, return the value
(define (lookup-ds name ds)
  (type-case dfrSub ds
    [mtSub () (error 'lookup-ds "unknown identifier")]
    [aSub (sub-name val rest-ds) (if (symbol=? sub-name name)
                                     val
                                     (lookup-ds name rest-ds))]))

(test (lookup-ds 'x (aSub 'y (numV 10) (aSub 'x (recordV (list (list (id 'z) 10))) (mtSub)))) (recordV (list (list (id 'z) 10))))
(test/exn (lookup-ds 'y (aSub 'x (numV 10) (mtSub))) "unknown")

;; store-lookup : integer Store -> BWAE-Value
;; to check whether a value is assigned at the given address
;; if so, return the value
(define (store-lookup address st)
  (type-case Store st
    [mtSto () (error 'store-lookup "unallocated : address ~a" address)]
    [aSto (addr val rest-st) (if (= addr address) val (store-lookup address rest-st))]))

(test (store-lookup 14 (aSto 12 (numV 10) (aSto 14 (boxV 12) (mtSto)))) (boxV 12))
(test/exn (store-lookup 0 (aSto 1 (numV 1) (mtSto))) "unallocated")

;; replace-old-store : address Store -> Store
;; to find the store information of the given address
;; then, insert new aSto with newval there and set rest-st of old aSto as rest-st of new one
;; in other words, replace old aSto with new one
(define (replace-old-store address newval st)
  (type-case Store st
    [mtSto () (error 'replace-old-store "unallocated address: ~a" address)]
    [aSto (addr val rest-st) (if (= addr address) (aSto address newval rest-st) (aSto addr val (replace-old-store address newval rest-st)))]))

(test (replace-old-store 1 (numV 42) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))) (aSto 2 (numV 1) (aSto 1 (numV 42) (mtSto))))

;; malloc : Store -> integer
;; to find address which a value can be assigned
(define (malloc st)
  (+ 1 (max-address st)))

; testcases for malloc function are given below max-address function

;; max-address : Store -> integer
;; to find the maximun address which a value is already assigned
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (addr val rest-st) (max addr (max-address rest-st))]))

(test (max-address (mtSto)) 0)
(test (max-address (aSto 12 (numV 10) (aSto 1 (numV 1) (aSto 23 (numV 23) (aSto 13 (numV 10) (mtSto)))))) 23)
(test (malloc (mtSto)) 1)
(test (malloc (aSto 12 (numV 10) (aSto 1 (numV 1) (aSto 23 (numV 23) (aSto 13 (numV 10) (mtSto)))))) 24)

;; lookup-record : list-of-recordEntry id -> integer
;; to find the field whose name is same with the name of the given id
;; if exists, return field value which is integer address
(define (lookup-record record name)
  (cond
    [(empty? record) (error 'lookup-record "no such field : ~a" (id-name name))]
    [(symbol=? (id-name name) (id-name (entry-name (first record)))) (entry-value (first record))]
    [else (lookup-record (rest record) name)]))

(test (lookup-record (list (entry (id 'x) 11) (entry (id 'y) 42)) (id 'y)) 42)
(test/exn (lookup-record (list (entry (id 'z) 0) (entry (id 'x) 1)) (id 'y)) "no such field")
(test/exn (lookup-record empty (id 'x)) "no such field")

;; interp-two : BFAE BFAE dfrSub Store (BFAE-Value BFAE-Value Store -> Value*Store) -> Value*Store
;; if two BFAE expressions are evaluated, Store can be changed after interpreting the first expression
;; because Store plays a role of memory. Thus, the second expression must be evaluated with the new Store.
;; After evaluating two expressions following mentioned manner, evaluate handle, which is a lambda function where
;; two result values and Store after evaluating the second expression are used as arguments
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st1) (type-case Value*Store (interp expr2 ds st1)
                      [v*s (val2 st2) (handle val1 val2 st2)])]))

;; interp-seqn : BFAE list-of-BFAE dfrSub Store -> Value*Store
;; similar with interp-two, except that second parameter is a list of BFAE.
;; helping interpret function for seqn
(define (interp-seqn expr1 others ds st)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st1) (cond
                      [(empty? others) (v*s val1 st1)]
                      [(empty? (rest others)) (interp (first others) ds st1)]
                      [else (interp-seqn (first others) (rest others) ds st1)])]))

;; make-recordentry : list-of-(<id>, <BFAE>) dfrSub Store list-of-symbol -> list-of-recordEntry
;; when evaluating rec expression, all fields are stored in the form of recordEntry
;; also, value for a entry is the address at which data is assigned in Store
;; if record more than two entries whose names are same, error occurs
;; ids is a list containing symbols already used as a field name.
(define (make-recordentry l ds st ids)
  (cond
    [(empty? l) (list st)]   ; at the tail of returned list, final store after evaluating all entry is located
    [else (local [(define head (first l))]
            (cond
              [(= (length ids) (length (remove-duplicates (append (list (id-name (first head))) ids)))) (error 'make-recordentry "duplicate fields")]
              [else (type-case Value*Store (interp (second head) ds st)
                      [v*s (val1 st1) (local [(define p (malloc st1))]
                                        (append (list (entry (first head) p)) (make-recordentry (rest l) ds (aSto p val1 st1) (append (list (id-name (first head))) ids))))])]))]))

; testcases for interp-two, interp-seqn and make-recordentry are given below the interp function

;; interp : BFAE dfrSub Store -> Value*Store
;; to evaluate BFAE expressions and return a pair of resulting value and store
(define (interp bfae ds st)
  (type-case BFAE bfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st (lambda (val1 val2 st1) (v*s (numV (+ (numV-n val1) (numV-n val2))) st1)))]
    [sub (l r) (interp-two l r ds st (lambda (val1 val2 st1) (v*s (numV (- (numV-n val1) (numV-n val2))) st1)))]
    [id (s) (v*s (lookup-ds s ds) st)]
    [fun (p b) (v*s (closureV p b ds) st)]
    [app (f a) (interp-two f a ds st (lambda (val1 val2 st1) (type-case Value*Store (interp (closureV-body val1) (aSub (closureV-param val1) val2 (closureV-ds val1)) st1)
                                                               [v*s (fun-val st2) (v*s fun-val st2)])))]
    [newbox (v) (type-case Value*Store (interp v ds st)
                  [v*s (val1 st1) (local [(define p (malloc st1))]
                                    (v*s (boxV p) (aSto p val1 st1)))])]
    [setbox (b v) (interp-two b v ds st (lambda (val1 val2 st1) (v*s val2 (replace-old-store (boxV-address val1) val2 st1))))]
    [openbox (b) (type-case Value*Store (interp b ds st)
                   [v*s (val1 st1) (v*s (store-lookup (boxV-address val1) st1) st1)])]
    [seqn (l r) (interp-seqn l r ds st)]
    [rec (l) (cond
               [(empty? l) (v*s (recordV empty) st)]
               [else (local [(define entries (make-recordentry l ds st empty))]
                       (v*s (recordV (drop-right entries 1)) (first (take-right entries 1))))])]
    [get (r n) (type-case Value*Store (interp r ds st)
                 [v*s (val1 st1) (v*s (store-lookup (lookup-record (recordV-record val1) n) st1) st1)])]
    [setrecord (r n v) (type-case Value*Store (interp r ds st)
                         [v*s (val1 st1) (local [(define p (lookup-record (recordV-record val1) n))]
                                           (type-case Value*Store (interp v ds st1)
                                             [v*s (val2 st2) (v*s val2 (replace-old-store p val2 st2))]))])]))

(test (interp-two (num 2) (num 3) (mtSub) (mtSto) (lambda (val1 val2 st1) (v*s (numV (+ (numV-n val1) (numV-n val2))) st1))) (v*s (numV 5) (mtSto)))
(test (interp-seqn (num 2) (list (num 3) (num 4)) (mtSub) (mtSto)) (v*s (numV 4) (mtSto)))
(test (interp-seqn (num 1) empty (mtSub) (mtSto)) (v*s (numV 1) (mtSto)))
(test (make-recordentry (list (list (id 'x) (num 1)) (list (id 'y) (fun 'x (add (id 'x) (id 'x))))) (mtSub) (mtSto) empty) (list (entry (id 'x) 1) (entry (id 'y) 2) (aSto 2 (closureV 'x (add (id 'x) (id 'x)) (mtSub)) (aSto 1 (numV 1) (mtSto)))))
(test (make-recordentry empty (mtSub) (mtSto) empty) (list (mtSto)))
(test/exn (make-recordentry (list (list (id 'x) (num 1)) (list (id 'y) (num 2)) (list (id 'y) (boxV 1))) (mtSub) (mtSto) empty) "duplicate fields")
(test (interp (num 5) (mtSub) (mtSto)) (v*s (numV 5) (mtSto)))
(test (interp (add (num 5) (num 2)) (mtSub) (mtSto)) (v*s (numV 7) (mtSto)))
(test (interp (sub (num 5) (num 2)) (mtSub) (mtSto)) (v*s (numV 3) (mtSto)))
(test (interp (id 'x) (aSub 'x (closureV 'y (add (id 'y) (num 2)) (mtSub)) (mtSub)) (mtSto)) (v*s (closureV 'y (add (id 'y) (num 2)) (mtSub)) (mtSto)))
(test (interp (fun 'x (add (num 2) (id 'x))) (mtSub) (mtSto)) (v*s (closureV 'x (add (num 2) (id 'x)) (mtSub)) (mtSto)))
(test (interp (app (fun 'x (add (id 'x) (id 'x))) (num 2)) (aSub 'x (numV 3) (mtSub)) (mtSto)) (v*s (numV 4) (mtSto)))
(test (interp (newbox (fun 'x (add (id 'x) (id 'x)))) (aSub 'x (numV 3) (mtSub)) (mtSto)) (v*s (boxV 1) (aSto 1 (closureV 'x (add (id 'x) (id 'x)) (aSub 'x (numV 3) (mtSub))) (mtSto))))
(test (interp (setbox (newbox (num 5)) (num 4)) (mtSub) (mtSto)) (v*s (numV 4) (aSto 1 (numV 4) (mtSto))))
(test (interp (openbox (newbox (num 5))) (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (mtSto))))
(test (interp (seqn (add (id 'x) (num 3)) (list (add (id 'x) (id 'x)))) (aSub 'x (numV 5) (mtSub)) (mtSto)) (v*s (numV 10) (mtSto)))
(test (interp (app (fun 'b (seqn (setbox (id 'b) (num 2)) (list (openbox (id 'b))))) (newbox (num 1))) (mtSub) (mtSto)) (v*s (numV 2) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{seqn {+ 1 2}}) (mtSub) (mtSto)) (v*s (numV 3) (mtSto)))
(test (interp (parse '{seqn {+ 1 2} {- 1 1}}) (mtSub) (mtSto)) (v*s (numV 0) (mtSto)))

(define (interp-expr exp)
  (type-case Value*Store (interp exp (mtSub) (mtSto))
    [v*s (val st) (cond
                    [(numV? val) (numV-n val)]
                    [(closureV? val) 'func]
                    [(boxV? val) 'box]
                    [(recordV? val) 'record])]))

(test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b 2}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 2)
             (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b {+ 2 {openbox b}}}
                           {setbox b {+ 3 {openbox b}}}
                           {setbox b {+ 4 {openbox b}}}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)

(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)

 (test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)

(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)

(test/exn (interp (parse '{get {rec {a 10}} b}) (mtSub) (mtSto)) "")
(test/exn (interp (parse '{get {rec {b 10} {b {+ 1 2}}} b}) (mtSub) (mtSto)) "")
(test/exn (interp (parse '{{fun {x} {get {rec {a x} {x a}} a}} 7}) (mtSub) (mtSto)) "")
(test (interp-expr (parse '{{fun {x} {rec {a x}}} {newbox 1}})) 'record)
(test (interp-expr (parse '{{fun {x} {{fun {r} {get r a}} {rec {a x}}}} {newbox 1}})) 'box)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {openbox b}} {get r a}}} {rec {a x}}}} {newbox 1}})) 1)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 2)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b} {set r a 3} {get r a}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 3)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b} {set r a 3} {get r a} {openbox b}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 2)

