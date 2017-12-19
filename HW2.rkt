#lang plai
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)
       (rhs WAE?)]
  [sub (lhs WAE?)
       (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

; <<helper functions>>

; symbol<?: symbol symbol -> boolean

; to check whether two given symbols are ordered lexicographically.
(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

; first-if-not-null: list-of(-list-of)-sym -> list-of-sym

; if given list is null list, return it
; otherwise, given list always consists of two lists of sym. Return the first one.
(define (first-if-not-null lst)
  (cond
    [(null? lst) lst]
    [else (first lst)]))

; second-if-not-null: list-of(-list-of)-sym -> list-of-sym

; if given list is null list, return it
; otherwise, given list always consists of two lists of sym. Return the second one.
(define (second-if-not-null lst)
  (cond
    [(null? lst) lst]
    [else (second lst)]))

; bound-and-not-bound: wae -> list-of-sym

; to make a list with given wae.
; the list is '( <list of bound identifiers in wae> <list of non-bound identifiers in wae> ) or empty list
(define (bound-and-not-bound wae)
  (type-case WAE wae
    [num (n) (list empty empty)]
    [add (lhs rhs) (list (append (first-if-not-null (bound-and-not-bound lhs)) (first-if-not-null (bound-and-not-bound rhs)))
                         (append (second-if-not-null (bound-and-not-bound lhs)) (second-if-not-null (bound-and-not-bound rhs))))]
    [sub (lhs rhs) (list (append (first-if-not-null (bound-and-not-bound lhs)) (first-if-not-null (bound-and-not-bound rhs)))
                         (append (second-if-not-null (bound-and-not-bound lhs)) (second-if-not-null (bound-and-not-bound rhs))))]
    [with (name named-expr body) (cond
                                   [(member name (second-if-not-null (bound-and-not-bound body)))
                                    (list (append (first-if-not-null (bound-and-not-bound body)) (first-if-not-null (bound-and-not-bound named-expr)) (list name))
                                          (append (remq* (list name) (second-if-not-null (bound-and-not-bound body))) (second-if-not-null (bound-and-not-bound named-expr))))]
                                   [else (list (append (first-if-not-null (bound-and-not-bound body)) (first-if-not-null (bound-and-not-bound named-expr)))
                                               (append (second-if-not-null (bound-and-not-bound body)) (second-if-not-null (bound-and-not-bound named-expr))))])]
    [id (name) (list empty (list name))]))


; <<main function>>

; free-ids: WAE -> list-of-sym

; to produce a list of symbols for free identifiers in the given WAE
; the symbols should be ordered lexicographically and appear at most once.

(define (free-ids wae)
  (remove-duplicates (sort (type-case WAE wae
    [num (n) empty]
    [add (lhs rhs) (append (free-ids lhs) (free-ids rhs))]
    [sub (lhs rhs) (append (free-ids lhs) (free-ids rhs))]
    [with (name named-expr body) (append (remq* (list name) (free-ids body)) (free-ids named-expr))]
    [id (name) (list name)]) symbol<?)))

(test (free-ids (add (num 2) (id 'x))) '(x))
(test (free-ids (num 3)) '())
(test (free-ids (id 'x)) '(x))
(test (free-ids (with 'x (num 3) (with 'y (num 3) (add (id 'x) (id 'z))))) '(z))
(test (free-ids (with 'x (add (id 'x) (num 3)) (add (with 'z (id 'x) (sub (id 'x) (id 'y))) (sub (num 3) (id 'z))))) '(x y z))
(test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
(test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
(test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
(test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))
(test (free-ids (add (num 3) (sub (id 'x) (id 'y)))) '(x y))
(test (free-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x))
(test (free-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(x))
(test (free-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x))
(test (free-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(x y))
(test (free-ids (with 'x (num 3) (add (id 'y) (num 3)))) '(y))
(test (free-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(y))
(test (free-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '())
(test (free-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '())
(test (free-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(y))
(test (free-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x y))
(test (free-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(x y))
(test (free-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(a b c d))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))


; binding-ids: WAE -> list-of-sym

; to produce a list of symbols for binding identifier in the given WAE
; the symbols should be ordered lexicographically and appear at most once.

(define (binding-ids wae)
  (remove-duplicates (sort (type-case WAE wae
    [num (n) empty]
    [add (lhs rhs) (append (binding-ids lhs) (binding-ids rhs))]
    [sub (lhs rhs) (append (binding-ids lhs) (binding-ids rhs))]
    [with (name named-expr body) (append (list name) (binding-ids named-expr) (binding-ids body))]
    [id (name) empty]) symbol<?)))

(test (binding-ids (add (num 2) (id 'x))) '())
(test (binding-ids (num 3)) '())
(test (binding-ids (id 'x)) '())
(test (binding-ids (with 'x (num 3) (with 'y (num 3) (add (id 'x) (id 'z))))) '(x y))
(test (binding-ids (with 'x (add (id 'x) (num 3)) (add (with 'z (id 'x) (sub (id 'x) (id 'y))) (sub (num 3) (id 'z))))) '(x z))
(test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
(test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))
(test (binding-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '(x))
(test (binding-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(x))
(test (binding-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(x))
(test (binding-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(x))
(test (binding-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(x y))
(test (binding-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(x y))
(test (binding-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (binding-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a x y))
(test (binding-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x y))
(test (binding-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(a x y))
(test (binding-ids (with 'x (num 3) (add (id 'y) (num 3)))) '(x))
(test (binding-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (binding-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (binding-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (binding-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x y))
(test (binding-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x y z))
(test (binding-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(x y))
(test (binding-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (binding-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x y))
(test (binding-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(a x y))

; bound-ids: WAE -> list-of-sym

; to produce a list of symbols for bound identifier in the given WAE
; the symbols should be ordered lexicographically and appear at most once.


(define (bound-ids wae)
  (remove-duplicates(sort (first-if-not-null (bound-and-not-bound wae)) symbol<?)))

(test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
(test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))
(test (bound-ids (add (num 2) (id 'x))) '())
(test (bound-ids (num 3)) '())
(test (bound-ids (id 'x)) '())
(test (bound-ids (with 'x (num 3) (with 'y (num 3) (add (id 'x) (id 'z))))) '(x))
(test (bound-ids (with 'x (add (id 'x) (num 3)) (add (with 'z (id 'x) (sub (id 'x) (id 'y))) (sub (num 3) (id 'z))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '(x))
(test (bound-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(x))
(test (bound-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(x))
(test (bound-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(x))
(test (bound-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(x))
(test (bound-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(x))
(test (bound-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))
(test (bound-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (bound-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(y))
(test (bound-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (bound-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (bound-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w))


 