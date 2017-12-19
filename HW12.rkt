#lang plai-typed

(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : EXPR-Value) (rest : DefrdSub)]
  [aRecSub (name : symbol) (value-box : (boxof EXPR-Value)) (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [idT (name : symbol)]
  [tvT (name : symbol)])

(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])
  
(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)])

(define-type TypeList
  [mtList]
  [aList (type : Type) (rest : TypeList)])

(define-type TvLabel
  [mtLabel]
  [aLabel (name : symbol) (type : Type) (rest : TvLabel)])

(define-type Label
  [none]
  [some (type : Type)])

;; functions

;; get-type : symbol TypeEnv -> Type
;; to find non-user-defined type with the given name
(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest) (if (symbol=? name-to-find name)
                              ty
                              (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]))

(test (get-type 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (aBind 'a (polyT 'alpha (numT)) (mtEnv))))) (polyT 'alpha (numT)))
(test/exn (get-type 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (aBind 'b (polyT 'alpha (numT)) (mtEnv))))) "free")
(test/exn (get-type 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (tBind 'a 'foo (numT) 'bar (numT) (mtEnv))))) "free")

;; find-type-id : symbol TypeEnv -> TypeEnv
;; to find user-defined type with the given name
(define (find-type-id name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free type name, so no type")]
    [aBind (name ty rest) (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]))

(test (find-type-id 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (tBind 'a 'foo (numT) 'bar (numT) (mtEnv))))) (tBind 'a 'foo (numT) 'bar (numT) (mtEnv)))
(test/exn (find-type-id 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (aBind 'b (polyT 'alpha (numT)) (mtEnv))))) "free")
(test/exn (find-type-id 'a (aBind 'x (numT) (aBind 'y (arrowT (numT) (boolT)) (aBind 'a (polyT 'alpha (numT)) (mtEnv))))) "free")

;; parse-type : TE -> Type
;; convert given TE to corresponding Type
(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (p r) (arrowT (parse-type p) (parse-type r))]
    [polyTE (f b) (polyT f (parse-type b))]
    [idTE (n) (idT n)]
    [tvTE (n) (tvT n)]))

(test (parse-type (numTE)) (numT))
(test (parse-type (arrowTE (numTE) (arrowTE (boolTE) (tvTE 'n)))) (arrowT (numT) (arrowT (boolT) (tvT 'n))))
(test (parse-type (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))


;; validtype Type TypeEnv -> TypeEnv
;; to check the given type is valid
(define (validtype ty env)
  (type-case Type ty
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a b) (begin (validtype a env)
                         (validtype b env))]
    [polyT (f b) (validtype b (aBind f (tvT f) env))]
    [idT (id) (find-type-id id env)]
    [tvT (id) (local [(define tv-type (get-type id env))]
                (type-case Type tv-type
                  [tvT (n) (mtEnv)]
                  [else (error 'validtype "no type")]))]))

(test (validtype (numT) (aBind 'x (boolT) (mtEnv))) (mtEnv))
(test (validtype (arrowT (numT) (arrowT (boolT) (polyT 'alpha (tvT 'alpha)))) (mtEnv)) (mtEnv))
(test/exn (validtype (tvT 'beta) (aBind 'alpha (tvT 'alpha) (aBind 'x (numT) (tBind 'alpha 'foo (numT) 'bar (numT) (mtEnv))))) "free")
(test (validtype (idT 't) (aBind 'x (arrowT (numT) (numT)) (tBind 't 'foo (numT) 'bar (numT) (mtEnv)))) (tBind 't 'foo (numT) 'bar (numT) (mtEnv)))

;; find-all-type : Type TypeEnv TypeList -> TypeList
;; to collect all types of the given type and sort them in the specific order
(define (find-all-type ty env tl)
  (type-case Type ty
    [numT () (aList (numT) tl)]
    [boolT () (aList (numT) tl)]
    [arrowT (p b) (local [(define p-list (find-all-type p env tl))]
                    (find-all-type b env p-list))]
    [polyT (f b) (aList (tvT f) (find-all-type b env tl))]
    [idT (id) (aList (idT id) tl)]
    [tvT (id) (aList (tvT id) tl)]))

(test (find-all-type (arrowT (numT) (numT)) (mtEnv) (mtList)) (aList (numT) (aList (numT) (mtList))))
(test (find-all-type (polyT 'alpha (tvT 'alpha)) (mtEnv) (mtList)) (aList (tvT 'alpha) (aList (tvT 'alpha) (mtList))))

;; lookup-tvlabel : symbol TvLabel -> Label
;; to check whether there is a label whose name is same with given one
;; the given name is a name of a tvT. And if there is such label the tvT has equivalent type. So return it
;; if it does not exist, return none label
(define (lookup-tvlabel name tvl)
  (type-case TvLabel tvl
    [mtLabel () (none)]
    [aLabel (n t r) (if (symbol=? n name)
                        (some t)
                        (lookup-tvlabel name r))]))

(test (lookup-tvlabel 'alpha (mtLabel)) (none))
(test (lookup-tvlabel 'alpha (aLabel 'alpha (numT) (mtLabel))) (some (numT)))
(test (lookup-tvlabel 'alpha (aLabel 'ppap (boolT) (mtLabel))) (none))

;; compare-all-type : TypeList TypeList TvLabel TvLabel -> bool
(define (compare-all-type tl1 tl2 tvl1 tvl2 env)
  (type-case TypeList tl1
    [mtList () (type-case TypeList tl2
                 [mtList () #t]
                 [else #f])]
    [aList (ty1 rest1) (type-case TypeList tl2
                          [mtList () #f]
                          [aList (ty2 rest2) (type-case Type ty1
                                                [numT () (type-case Type ty2
                                                           [numT () (compare-all-type rest1 rest2 tvl1 tvl2 env)]
                                                           [boolT () #f]
                                                           [idT (id) #f]
                                                           [tvT (id) (local [(define label (lookup-tvlabel id tvl2))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (aLabel id (numT) tvl2) env)]
                                                                         [some (t) (if (numT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [boolT () (type-case Type ty2
                                                           [numT () #f]
                                                           [boolT () (compare-all-type rest1 rest2 tvl1 tvl2 env)]
                                                           [idT (id) #f]
                                                           [tvT (id) (local [(define label (lookup-tvlabel id tvl2))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (aLabel id (boolT) tvl2) env)]
                                                                         [some (t) (if (boolT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [idT (id1) (type-case Type ty2
                                                           [numT () #f]
                                                           [boolT () #f]
                                                           [idT (id2) (if (symbol=? id1 id2) #t #f)]
                                                           [tvT (id) (local [(define label (lookup-tvlabel id tvl2))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (aLabel id (idT id1) tvl2) env)]
                                                                         [some (t) (if (and (idT? t) (symbol=? id1 (idT-name t)))
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [tvT (id1) (type-case Type ty2
                                                           [numT () (local [(define label (lookup-tvlabel id1 tvl1))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 (aLabel id1 (numT) tvl1) tvl2 env)]
                                                                         [some (t) (if (numT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [boolT () (local [(define label (lookup-tvlabel id1 tvl1))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 (aLabel id1 (boolT) tvl1) tvl2 env)]
                                                                         [some (t) (if (boolT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [idT (id) (local [(define label (lookup-tvlabel id1 tvl1))]
                                                                       (type-case Label label
                                                                         [none () (compare-all-type rest1 rest2 (aLabel id1 (idT id) tvl1) tvl2 env)]
                                                                         [some (t) (if (and (idT? t) (symbol=? id (idT-name t)))
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2 env)
                                                                                       #f)]))]
                                                           [tvT (id2) (local [(define id1-label (lookup-tvlabel id1 tvl1))
                                                                              (define id2-label (lookup-tvlabel id2 tvl2))]
                                                                        (type-case Label id1-label
                                                                          [none () (type-case Label id2-label
                                                                                     [none () (compare-all-type rest1 rest2 tvl1 tvl2 env)]
                                                                                     [some (t) (compare-all-type rest1 rest2 (aLabel id1 t tvl1) tvl2 env)])]
                                                                          [some (t1) (type-case Label id2-label
                                                                                      [none () (compare-all-type rest1 rest2 tvl1 (aLabel id2 t1 tvl2) env)]
                                                                                      [some (t2) (if (equaltype t1 t2 env) (compare-all-type rest1 rest2 tvl1 tvl2 env) #f)])]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [else (error 'compare-all-type "impossible case!")])])]))

(test (compare-all-type (aList (numT) (mtList)) (aList (boolT) (mtList)) (mtLabel) (mtLabel) (mtEnv)) #f)
(test (compare-all-type (aList (numT) (aList (numT) (mtList))) (aList (numT) (aList (numT) (mtList))) (mtLabel) (mtLabel) (mtEnv)) #t)

;; equaltype : Type Type TypeEnv -> bool
;; to check whether given two types are equal or not
(define (equaltype ty1 ty2 env)
  (local [(define ty1-list (find-all-type ty1 env (mtList)))
          (define ty2-list (find-all-type ty2 env (mtList)))]
    (compare-all-type ty1-list ty2-list (mtLabel) (mtLabel) env)))

(test (equaltype (numT) (numT) (mtEnv)) #t)
(test (equaltype (polyT 'alpha (tvT 'alpha)) (polyT 'beta (tvT 'beta)) (mtEnv)) #t)


;; replace-tvT : Type symbol Type -> Type
;; to replace every tvT with the given symbol with specific type
(define (replace-tvT from name with)
  (type-case Type from
    [arrowT (p r) (arrowT (replace-tvT p name with) (replace-tvT r name with))]
    [polyT (f b) (if (symbol=? name f)
                     from
                     (polyT f (replace-tvT b name with)))]
    [tvT (id) (if (symbol=? id name)
                  with
                  from)]
    [else from]))

(test (replace-tvT (numT) 'alpha (boolT)) (numT))
(test (replace-tvT (arrowT (tvT 'alpha) (tvT 'alpha)) 'alpha (numT)) (arrowT (numT) (numT)))
(test (replace-tvT (arrowT (tvT 'alpha) (tvT 'beta)) 'alpha (arrowT (numT) (numT))) (arrowT (arrowT (numT) (numT)) (tvT 'beta)))

;; typecheck : EXPR TypeEnv -> Type
;; to check the given expression has valid type. If does, return the type
(define (typecheck expr env)
  (type-case EXPR expr
    [num (n) (numT)]
    [bool (b) (boolT)]
    [add (l r) (local [(define l-type (typecheck l env))]
                 (type-case Type l-type
                   [numT () (if (equaltype l-type (typecheck r env) env)
                                l-type
                                (error 'typecheck "no type"))]
                   [else (error 'typecheck "no type")]))]
    [sub (l r) (local [(define l-type (typecheck l env))]
                 (type-case Type l-type
                   [numT () (if (equaltype l-type (typecheck r env) env)
                                l-type
                                (error 'typecheck "no type"))]
                   [else (error 'typecheck "no type")]))]
    [equ (l r) (local [(define l-type (typecheck l env))]
                 (type-case Type l-type
                   [numT () (if (equaltype l-type (typecheck r env) env)
                                (boolT)
                                (error 'typecheck "no type"))]
                   [else (error 'typecheck "no type")]))]
    [id (name) (get-type name env)]
    [fun (name te body)
         (local [(define param-type (parse-type te))]
           (begin
             (validtype param-type env)
             (arrowT param-type
                     (typecheck body
                                (aBind name param-type env)))))]
    [app (fn arg)
         (type-case Type (typecheck fn env)
           [arrowT (param-type result-type)
                   (if (equaltype param-type
                               (typecheck arg env) env)
                       result-type
                       (error 'typecheck "no type"))]
           [else (error 'typecheck "no type")])]
    [ifthenelse (t l r)
                (type-case Type (typecheck t env)
                  [boolT () (local [(define l-type (typecheck l env))]
                              (if (equaltype l-type (typecheck r env) env)
                                  l-type
                                  (error 'typecheck "no type")))]
                  [else (error 'typecheck "no type")])]
    [rec (name te rhs-expr body-expr) (local [(define ty (parse-type te))
                                              (define new-env (aBind name ty env))]
                                        (if (equaltype ty (typecheck rhs-expr new-env) env)
                                            (typecheck body-expr new-env)
                                            (error 'typecheck "no type")))]
    [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
      (local [(define var1-ty (parse-type var1-te))
              (define var2-ty (parse-type var2-te))
              (define new-env (tBind type-name
                                     var1-name var1-ty
                                     var2-name var2-ty
                                     env))]
        (begin
          (validtype var1-ty new-env)
          (validtype var2-ty new-env)
          (typecheck body-expr (aBind var1-name
                                      (arrowT var1-ty (idT type-name))
                                      (aBind var2-name
                                             (arrowT var2-ty (idT type-name))
                                             new-env)))))]
    [cases (type-name dispatch-expr var1-name var1-id var1-rhs var2-name var2-id var2-rhs)
      (local [(define bind (find-type-id type-name env))]
        (if (and (equal? var1-name (tBind-var1-name bind))
                 (equal? var2-name (tBind-var2-name bind)))
            (type-case Type (typecheck dispatch-expr env)
              [idT (name) (if (equal? name type-name)
                              (local [(define rhs1-ty (typecheck var1-rhs (aBind var1-id (tBind-var1-type bind) env)))
                                      (define rhs2-ty (typecheck var2-rhs (aBind var2-id (tBind-var2-type bind) env)))]
                                (if (equaltype rhs1-ty rhs2-ty env)
                                    rhs1-ty
                                    (error 'typecheck "no type")))
                              (error 'typecheck "no type"))]
              [else (error 'typecheck "no type")])
            (error 'typecheck "no type")))]
    [tfun (n e) (polyT n (typecheck e (aBind n (tvT n) env)))]
    [tapp (b te) (local [(define ty (parse-type te))
                         (define b-type (typecheck b env))]
                   (begin
                     (validtype ty env)
                     (type-case Type b-type
                       [polyT (f body) (replace-tvT body f ty)]
                       [else (error 'typecheck "no type")])))]))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'beta (tvT 'alpha))) (mtEnv))) (polyT 'beta (numT)))

;; lookup : symbol DefrdSub -> EXPR-Value
;; to check what the value corresponding to the given symbol is
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds) (if (symbol=? sub-name name) val (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))

(test (lookup 'foo (aSub 'bar (numV 20) (aSub 'foo (boolV #t) (mtSub)))) (boolV #t))
(test (lookup 'foo (aSub 'bar (numV 20) (aSub 'foo (constructorV #f) (mtSub)))) (constructorV #f))
(test/exn (lookup 'foo (aSub 'bar (numV 42) (mtSub))) "free")


;; interp : EXPR DefrdSub -> EXPR-Value
;; to evaluate given expression
(define (interp expr ds)
  (type-case EXPR expr
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (numV (+ (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [sub (l r) (numV (- (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [equ (l r) (boolV (= (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [id (name) (lookup name ds)]
    [fun (param te body-expr) (closureV param body-expr ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (type-case EXPR-Value fun-val
             [closureV (param body ds) (interp body (aSub param arg-val ds))]
             [constructorV (right?) (variantV right? arg-val)]
             [else (error 'interp "not applicable")]))]
    [ifthenelse (t l r) (if (boolV-b (interp t ds))
                            (interp l ds)
                            (interp r ds))]
    [rec (bound-id type named-expr body-expr)
      (local [(define value-holder (box (numV 42)))
              (define new-ds (aRecSub bound-id value-holder ds))]
        (begin
          (set-box! value-holder (interp named-expr new-ds))
          (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
      (interp body-expr (aSub var1-name (constructorV false) (aSub var2-name (constructorV true) ds)))]
    [cases (ty dispatch-expr var1-name var1-id var1-rhs var2-name var2-id var2-rhs)
      (type-case EXPR-Value (interp dispatch-expr ds)
        [variantV (right? val) (if (not right?) (interp var1-rhs (aSub var1-id val ds)) (interp var2-rhs (aSub var2-id val ds)))]
        [else (error 'interp "not a variant result")])]
    [tfun (n e) (interp e ds)]
    [tapp (b te) (interp b ds)]))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'y))) (boolTE)) (mtSub)) (closureV 'x (id 'y) (mtSub)))

;; sample tests : typecheck -----------------------------------------------------------------------------------
(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (typecheck (tfun 'alpha (num 3)) (mtEnv)) (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))

(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (arrowTE (numTE) (numTE)))
          (mtEnv)) (arrowT (arrowT (numT) (numT)) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (num 42)) (id 'f)) (aBind 'f (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))) (mtEnv))) (numT))

;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))

;; sample tests : interp -----------------------------------------------------------------------------------
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10))