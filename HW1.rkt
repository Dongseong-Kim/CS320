#lang plai
; area-square: number number -> number

; to compute the area of a square whose length of
; two sides is (integer) x.
(define (area-square x)
  (* x x))
;(test (area-square 4) 16)
;(test (area-square 10) 100)
;(test (area-square 5) 25)
;(test (area-square 1) 1)
;(test (area-square 200) 40000)
;(test (area-square 12) 144)
;(test (area-square 100) 10000)
;(test (area-square 14) 196)
;(test (area-square 712) 506944)
;(test (area-square 123) 15129)


; volume-cuboid: number number number -> number

; to compute the volume of a cuboid whose length of
; each side is (integer) x, (integer) y, and (integer) z respectively.
(define (volume-cuboid x y z)
  (* x (* y z)))
;(test (volume-cuboid 1 2 3) 6)
;(test (volume-cuboid 2 5 10) 100)
;(test (volume-cuboid 1 2 6) 12)
;(test (volume-cuboid 1 1 1) 1)
;(test (volume-cuboid 12 4 8) 384)
;(test (volume-cuboid 100 100 100) 1000000)
;(test (volume-cuboid 120 33 7) 27720)
;(test (volume-cuboid 334 12 4) 16032)
;(test (volume-cuboid 97 46 54) 240948)
;(test (volume-cuboid 58 14 3224) 2617888)



; is-multiple-of?: number number -> boolean

; to check whether the first (integer) number, named "first", is
; a multiple of the second one, named "second".
(define (is-multiple-of? first second)
  (cond
    [(> first 0) (is-multiple-of? (- first second) second)] ; fix these three line!!
    [(= first 0) true]
    [(< first 0) false]))
;(test (is-multiple-of? 15 4) false)
;(test (is-multiple-of? 21 3) true)
;(test (is-multiple-of? 124 32) false)
;(test (is-multiple-of? 125132 12) false)
;(test (is-multiple-of? 1674426 21) false)
;(test (is-multiple-of? 155124 124) true)
;(test (is-multiple-of? 0 3) true)
;(test (is-multiple-of? 1 3) false)
;(test (is-multiple-of? 506920 152) true)
;(test (is-multiple-of? 126153 13) false)

; factorial: number -> number

; to compute the result of the factorial operation
; on input (integer) number, named "num".
(define (factorial num)
  (cond
    [(> num 1) (* num (factorial (- num 1)))]
    [else 1]))
;(test (factorial 5) 120)
;(test (factorial 7) 5040)
;(test (factorial 9) 362880)
;(test (factorial 1) 1)
;(test (factorial 2) 2)
;(test (factorial 11) 39916800)

; fibonacci: number -> number

; to find n-th fibonacci number when input (integer) number is "n".
(define (fibonacci n)
  (cond
    [(or (= n 1) (= n 2)) 1]
    [(> n 2) (+ (fibonacci (- n 2)) (fibonacci (- n 1)))]))
;(test (fibonacci 5) 5)
;(test (fibonacci 9) 34)
;(test (fibonacci 1) 1)
;(test (fibonacci 2) 1)
;(test (fibonacci 3) 2)
;(test (fibonacci 4) 3)

; definition of type COURSE
(define-type COURSE
  [CS320 (quiz number?)
         (homework number?)]
  [CS311 (homework number?)]
  [CS330 (projects number?)
         (homework number?)])

; total-assignments: COURSE -> number

; to compute the total number of quzzes, homework
; and projects for the given course.
(define (total-assignments course)
  (type-case COURSE course
    [CS320 (q h) (+ q h)]
    [CS311 (h) h]
    [CS330 (p h) (+ p h)]))
;(test (total-assignments (CS320 3 2)) 5)
;(test (total-assignments (CS311 4)) 4)
;(test (total-assignments (CS330 1 6)) 7)
;(test (total-assignments (CS330 12 5)) 17)
;(test (total-assignments (CS311 6)) 6)
;(test (total-assignments (CS320 125 3)) 128)

; total-homework: list-of-course -> number

; to notify the total number of homework of the
; courses in the given list
(define (total-homework list-of-course)
  (cond
    [(null? list-of-course) 0]
    [else
     (type-case COURSE (first list-of-course)
       [CS320 (q h) (+ h (total-homework (rest list-of-course)))]
       [CS311 (h) (+ h (total-homework (rest list-of-course)))]
       [CS330 (p h) (+ h (total-homework (rest list-of-course)))])]))
;(test (total-homework (list (CS320 1 2) (CS311 6) (CS330 1 5))) 13)
;(test (total-homework (list (CS320 3 3) (CS311 2) (CS330 8 9))) 14)
;(test (total-homework empty) 0)
;(test (total-homework (list (CS320 65 1) (CS311 1) (CS330 15124 1))) 3)

; my-map: function list-of-number -> list-of-number

; to generate the result of function f with input list l
(define (my-map f l)
  (cond
    [(null? l) null]
    [else (cons (f (first l)) (my-map f (rest l)))]))
;(test (my-map (lambda (x) (* x 2)) (cons 1 (cons 2 (cons 3 empty)))) '(2 4 6))
;(test (my-map (lambda (x) (+ (* 3 x) 2)) (cons 1 (cons 2 (cons 3 empty)))) '(5 8 11))
;(test (my-map (lambda (x) (* (+ x 2) (* 3 (- x 1)))) (cons 1 (cons 2 (cons 3 empty)))) '(0 12 30))
;(test (my-map (lambda (x) (- x 2)) (cons 1 (cons 2 (cons 3 empty)))) '(-1 0 1))
;(test (my-map (lambda (x) (* x 2)) empty) '())
;(test (my-map (lambda (x) (* x 2)) (cons 1 empty)) '(2))

; my-filter: predicate list-of-number -> list of number

; to generate a list consisting of the elements of l that satisfy the predicate f
(define (my-filter f l)
  (cond
    [(null? l) null]
    [else
     (cond
       [(f (first l)) (append (list (first l)) (my-filter f (rest l)))]
       [else (append null (my-filter f (rest l)))])]))
;(test (my-filter (lambda (x) (< x 5)) (cons 4 (cons 5 (cons 6 (cons 7 empty))))) '(4))
;(test (my-filter (lambda (x) (and (< x 7) (> x 3))) (cons 3 (cons 6 (cons 5 (cons 8 empty))))) '(6 5))
;(test (my-filter (lambda (x) (or (< x 1) (> x 10))) (cons 12 (cons 1 (cons 13 (cons -12 (cons 5 (cons 7 empty))))))) '(12 13 -12))
;(test (my-filter (lambda (x) (< x 10)) empty) '())
;(test (my-filter (lambda (x) (> x 1)) (cons 3 (cons 1 (cons 2 empty)))) '(3 2))


;;; --------------------------------------------------------------------
;;; Question 1 (10)

(test (area-square 1) 1)
(test (area-square 2) 4)
(test (area-square 3) 9)
(test (area-square 4) 16)
(test (area-square 5) 25)
(test (area-square 11) 121)
(test (area-square 35) 1225)
(test (area-square 2483) 6165289)
(test (area-square 10000) 100000000)
(test (area-square 99999) 9999800001)

;;; --------------------------------------------------------------------
;;; Question 2 (10)

(test (volume-cuboid 1 5 1) 5)
(test (volume-cuboid 2 4 3) 24)
(test (volume-cuboid 3 4 4) 48)
(test (volume-cuboid 4 3 5) 60)
(test (volume-cuboid 5 8 2) 80)
(test (volume-cuboid 3 3 3) 27)
(test (volume-cuboid 11 12 13) 1716)
(test (volume-cuboid 23 24 25) 13800)
(test (volume-cuboid 45 12 85) 45900)
(test (volume-cuboid 50 50 50) 125000)


;;; --------------------------------------------------------------------
;;; Question 3 (10)

(test (is-multiple-of? 44 3) #f)
(test (is-multiple-of? 33 3) #t)
(test (is-multiple-of? 1 7) #f)
(test (is-multiple-of? 0 10) #t)
(test (is-multiple-of? -121 11) #t)
(test (is-multiple-of? 33 12) #f)
(test (is-multiple-of? 60 -12) #t)
(test (is-multiple-of? -78 78) #t)
(test (is-multiple-of? 1001 11) #t)
(test (is-multiple-of? 999 9) #t)


;;; --------------------------------------------------------------------
;;; Question 4 (10)

(test (factorial 1) 1)
(test (factorial 2) 2)
(test (factorial 3) 6)
(test (factorial 4) 24)
(test (factorial 5) 120)
(test (factorial 6) 720)
(test (factorial 7) 5040)
(test (factorial 8) 40320)
(test (factorial 9) 362880)
(test (factorial 11) 39916800)

;;; --------------------------------------------------------------------
;;; Question 5 (10)

(test (fibonacci 1) 1)
(test (fibonacci 2) 1)
(test (fibonacci 3) 2)
(test (fibonacci 4) 3)
(test (fibonacci 5) 5)
(test (fibonacci 10) 55)
(test (fibonacci 15) 610)
(test (fibonacci 20) 6765)
(test (fibonacci 21) 10946)
(test (fibonacci 22) 17711)


;;; Question 6 (10)
(test (COURSE? (CS320 1 1)) #t)
(test (CS320-quiz (CS320 2 2)) 2)
(test (CS320-homework (CS320 4 4)) 4)
(test (COURSE? (CS311 4)) #t)
(test (CS311-homework (CS311 7)) 7)
(test (COURSE? (CS330 7 4)) #t)
(test (CS330-projects (CS330 2 2)) 2)
(test (CS330-homework (CS330 6 6)) 6)
(test (COURSE? (CS320 1 3)) #t)
(test (COURSE? (CS330 7 0)) #t)

;;; Question 7 (10)
(test (total-assignments (CS320 3 8)) 11)
(test (total-assignments (CS311 9)) 9)
(test (total-assignments (CS330 1 8)) 9)
(test (total-assignments (CS320 1 9)) 10)
(test (total-assignments (CS311 20)) 20)
(test (total-assignments (CS330 3 11)) 14)
(test (total-assignments (CS320 0 3)) 3)
(test (total-assignments (CS311 12)) 12)
(test (total-assignments (CS330 3 2)) 5)
(test (total-assignments (CS330 7 2)) 9)


;;; Question 8 (10)
(test (total-homework (list)) 0)
(test (total-homework (list (CS320 2 8))) 8)
(test (total-homework (list (CS311 1))) 1)
(test (total-homework (list (CS330 3 3))) 3)
(test (total-homework (list (CS320 3 3) (CS311 1))) 4)
(test (total-homework (list (CS320 2 2) (CS311 6) (CS330 3 3))) 11)
(test (total-homework (list (CS320 3 3) (CS320 3 3) (CS320 1 1) (CS320 1 1) (CS320 1 1))) 9)
(test (total-homework (list (CS320 5 5) (CS320 2 2) (CS320 2 2) (CS320 2 2) (CS320 2 2))) 13)
(test (total-homework (list (CS330 0 0) (CS330 1 1) (CS311 6) (CS320 1 1) (CS320 1 1))) 9)
(test (total-homework (list (CS330 0 0) (CS330 0 0) (CS330 0 0) (CS330 0 0) (CS330 0 0))) 0)

;;; Question 9 (10)
(test (my-map (lambda (number) (+ 1 number)) '()) '())
(test (my-map (lambda (number) (* 1 number)) '(1 2 3 4)) '(1 2 3 4))
(test (my-map (lambda (number) (+ 3 number)) '(4)) '(7))
(test (my-map (lambda (number) (- 4 number)) '()) '())
(test (my-map (lambda (number) (- 8 number)) '(1 2 3 4)) '(7 6 5 4))
(test (my-map (lambda (number) (* number number)) '()) '())
(test (my-map (lambda (number) (* number number)) '(9)) '(81))
(test (my-map (lambda (number) (* number number)) '(2 1 0 -1)) '(4 1 0 1))
(test (my-map (lambda (number) (* 0 number)) '(3 1 2)) '(0 0 0))
(test (my-map (lambda (number) number) '(1 2 3)) '(1 2 3))

;;; Question 10 (10)
(test (my-filter (lambda (x) (> x 1)) '()) '())
(test (my-filter (lambda (x) (> x 2)) '(3 2 1)) '(3))
(test (my-filter (lambda (x) (> x 1)) '(2 3 1 3 2)) '(2 3 3 2))
(test (my-filter (lambda (x) (and (> x 1) (< x 4))) '(4 3 2 1 2 3 4)) '(3 2 2 3))
(test (my-filter (lambda (x) true) '(3 2 1 2 3)) '(3 2 1 2 3))
(test (my-filter (lambda (x) true) '()) '())
(test (my-filter (lambda (x) false) '(3 2 1 2 3)) '())
(test (my-filter (lambda (x) false) '()) '())
(test (my-filter (lambda (x) (< x 10)) '(10 5 1 5 10 15 20)) '(5 1 5))
(test (my-filter (lambda (x) (> x 6)) '(11 1 2 3 4 5 6 7 8 9 10)) '(11 7 8 9 10))
