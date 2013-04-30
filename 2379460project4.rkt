; Jeff Cailteux
; KUID: 2379460
; Project 4
; EECS 662
; CFWAE/S

#lang plai


; Environment type
(define-type Env
  (mtSub)
  (aSub (name symbol?) (location number?) (env Env?)))

; Environment lookup
(define (env-lookup name env)
  (type-case Env env
    (mtSub () (error 'env-lookup "variable not found"))
    (aSub (n l e)
          (if (symbol=? n name)
              l
              (env-lookup name e)))))


; Store type
(define-type Store
  (mtSto)
  (aSto (location number?)
        (value CFWAE/S-Value?)
        (store Store?)))

; Store lookup
(define (store-lookup loc-index sto)
  (type-case Store sto
    (mtSto () (error 'store-lookup "no value found at location"))
    (aSto (l v s)
          (if (= l loc-index)
              v
              (store-lookup loc-index s)))))


; CFWAE/S Value type
(define-type CFWAE/S-Value
  (numV (n number?))
  (closureV (param symbol?)
            (body CFWAE/S?)
            (env Env?)))

; CFWAE/S type
(define-type CFWAE/S
  (num (n number?))
  (id (name symbol?))
  (add (lhs CFWAE/S?) (rhs CFWAE/S?))
  (sub (lhs CFWAE/S?) (rhs CFWAE/S?))
  (mul (lhs CFWAE/S?) (rhs CFWAE/S?))
  (div (lhs CFWAE/S?) (rhs CFWAE/S?))
  (with (bound-id symbol?) (named-expr CFWAE/S?) (bound-body CFWAE/S?))
  (fun (fun-name symbol?) (body CFWAE/S?))
  (app (fun-expr CFWAE/S?) (arg CFWAE/S?))
  (if0 (c CFWAE/S?) (t CFWAE/S?) (e CFWAE/S?))
  (seqq (first CFWAE/S?) (second CFWAE/S?))
  (assignq (id-name symbol?) (value CFWAE/S?)))


; Value Pairs
(define-type Value*Store
  (v*s (value CFWAE/S-Value?) (store Store?)))


; Parsing functoin
(define parse-cfwaes
  (lambda (expr)
    (cond ((symbol? expr) (id expr))
          ((number? expr) (num expr))
          ((list? expr)
           (case (car expr)
             ((-) (sub (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
             ((+) (add (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
             ((*) (mul (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
             ((/) (div (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
             ((if0) (if0 (parse-cfwaes (cadr expr)) (parse-cfwaes(caddr expr))
                         (parse-cfwaes (cadddr expr))))
             ((fun) (fun (cadr expr) 
                             (parse-cfwaes (caddr expr))))
             ((with) (with (car (cadr expr))
                           (parse-cfwaes (cadr (cadr expr)))
                           (parse-cfwaes (caddr expr))))
             ((seq) (seqq (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
             ((assign) (assignq (cadr expr) (parse-cfwaes (caddr expr))))
             ;app has been removed from syntax, hence the use of "else"
             (else (app (parse-cfwaes (car expr)) (parse-cfwaes (cadr expr))))))
          (else 'parse-cfwaes "Unexpected token"))))


; Next location
(define (next-location sto)
  (type-case Store sto
    (mtSto () 1)
    (aSto (location value stor)
          (+ 1 location))))


; Arithmetic helpers
(define (num+ n1 n2)
  (numV (+ (numV-n n1) (numV-n n2))))
(define (num- n1 n2)
  (numV (- (numV-n n1) (numV-n n2))))
(define (num* n1 n2)
  (numV (* (numV-n n1) (numV-n n2))))
(define (num/ n1 n2)
  (numV (/ (numV-n n1) (numV-n n2))))


; Interpreter
(define interp-cfwaes
  (lambda (expr env sto)
    (type-case CFWAE/S expr
      (num (n) (v*s (numV n) sto))
      (id (v) (v*s (store-lookup (env-lookup v env) sto) sto))
      (sub (lhs rhs)
           (type-case Value*Store (interp-cfwaes lhs env sto)
             (v*s (lhs-value lhs-store)
                  (type-case Value*Store (interp-cfwaes rhs env lhs-store)
                    (v*s (rhs-value rhs-store)
                         (v*s (num- lhs-value rhs-value) rhs-store))))))
      (add (lhs rhs)
           (type-case Value*Store (interp-cfwaes lhs env sto)
             (v*s (lhs-value lhs-store)
                  (type-case Value*Store (interp-cfwaes rhs env lhs-store)
                    (v*s (rhs-value rhs-store)
                         (v*s (num+ lhs-value rhs-value) rhs-store))))))
      (mul (lhs rhs)
           (type-case Value*Store (interp-cfwaes lhs env sto)
             (v*s (lhs-value lhs-store)
                  (type-case Value*Store (interp-cfwaes rhs env lhs-store)
                    (v*s (rhs-value rhs-store)
                         (v*s (num* lhs-value rhs-value) rhs-store))))))
      (div (lhs rhs)
           (type-case Value*Store (interp-cfwaes lhs env sto)
             (v*s (lhs-value lhs-store)
                  (type-case Value*Store (interp-cfwaes rhs env lhs-store)
                    (v*s (rhs-value rhs-store)
                         (v*s (num/ lhs-value rhs-value) rhs-store))))))
      (fun (a b) (v*s (closureV a b env) sto))
      (with (name named-expr body) 
            (type-case Value*Store (interp-cfwaes named-expr env sto)
              (v*s (ne-value ne-store)
                   (local ([define new-loc (next-location ne-store)])
                     (interp-cfwaes body (aSub name new-loc env) 
                                    (aSto new-loc ne-value ne-store))))))
      (if0 (c t e)
           (type-case Value*Store (interp-cfwaes c env sto)
             (v*s (c-value c-store)
                  (if (zero? (numV-n c-value))
                      (interp-cfwaes t env c-store)
                      (interp-cfwaes e env c-store)))))
      (app (fun-expr arg-expr)
           (type-case Value*Store (interp-cfwaes fun-expr env sto)
             (v*s (fe-value fe-store)
                  (type-case Value*Store (interp-cfwaes arg-expr env fe-store)
                    (v*s (ae-value ae-store)
                         (local ((define new-loc (next-location ae-store)))
                           (interp-cfwaes (closureV-body fe-value)
                                          (aSub (closureV-param fe-value)
                                                new-loc
                                                (closureV-env fe-value))
                                          (aSto new-loc
                                                ae-value
                                                ae-store))))))))
      (seqq (f s)
            (type-case Value*Store (interp-cfwaes f env sto)
              (v*s (f-value f-store)
                   (interp-cfwaes s env f-store))))
      (assignq (variable value)
            (type-case Value*Store (interp-cfwaes value env sto)
              (v*s (value-value value-store)
                   (local ((define l (env-lookup variable env)))
                     (v*s value-value
                          (aSto l value-value value-store)))))))))


; eval
(define eval-cfwae/s
  (lambda (expr)
    (type-case Value*Store (interp-cfwaes (parse-cfwaes expr) (mtSub) (mtSto))
      (v*s (v s)
           v))))


; Test Cases
(test (eval-cfwae/s '{+ 1 2}) (numV 3))
(test (eval-cfwae/s '{+ 2 {* 2 3}}) (numV 8))
(test (eval-cfwae/s '{{fun x x} 3}) (numV 3))
(test (eval-cfwae/s '{{fun x {+ x 1}} 1}) (numV 2))
(test (eval-cfwae/s '{if0 0 1 2}) (numV 1))
(test (eval-cfwae/s '{if0 {{fun x {- x 2}} 3} {{fun x {* 2 x}} 10} {{fun x {/ x 2}} 8}}) (numV 4))
(test (eval-cfwae/s '{{if0 0 {fun x {+ x 1}} {fun x {+ x 2}}} 0}) (numV 1))
(test (eval-cfwae/s '{with {x 10} {+ x 5}}) (numV 15))
(test (eval-cfwae/s '{with {f {fun x {+ x 1}}} {f 2}}) (numV 3))
(test (eval-cfwae/s '{with {x 2} {with {inc {fun x {+ x 2}}} {inc x}}}) (numV 4))
(test (eval-cfwae/s '{{{fun x {fun y {+ x y}}} 3} 1}) (numV 4))
(test (eval-cfwae/s '{with {f {fun x {fun y {+ x y}}}} {{f 3} 1}}) (numV 4))
(test (eval-cfwae/s '{with {y 1}
                           {with {inc {fun x {+ x y}}}
                                 {inc 3}}}) (numV 4))
(test (eval-cfwae/s '{with {y 1}
                           {with {inc {fun x {+ x y}}}
                                 {seq {assign y 2} {inc 3}}}}) (numV 5))
(test (eval-cfwae/s '{with {y 1}
                           {with {inc {seq {assign y 2} {fun x {+ x y}}}}
                                 {inc 3}}}) (numV 5))
(test (eval-cfwae/s '{with {x 3}
                           {seq x {assign x {+ x 1}}}}) (numV 4))
(test (eval-cfwae/s '{with {x 3}
                           {seq
                            {assign x {+ x 1}} {assign x {+ x 1}}}}) (numV 5))
(test (eval-cfwae/s '{with {x 3}
                           {seq
                            {seq
                             {assign x {+ x 1}} {assign x {+ x 1}}}
                            {assign x {+ x 1}}}}) (numV 6))