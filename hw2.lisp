#|

Copyright © 2026 by Pete Manolios 
CS 4820 Spring 2026

Homework 2.
Due: 1/26 (Midnight)

For this assignment, work in groups of 1-2.

Send me a link to your repo and cc the grader and your group members.
Send only 1 email per group and make sure to follow the submission
instructions on the course Web page. In particular, make sure that
the subject of your email submission is "CS 4820 HWK 2". Also, your
repo should have this file in it with solutions/answers included.

The group members are:
Zheng wangyuan 

|#





(in-package "ACL2S")

(modeling-validate-defs)
;; (modeling-admit-defs)
;; (modeling-admit-all)
;; (modeling-start)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1) SYNTAX: operators + SAEL expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unary operators in SAEL: (- e) and (/ e)
(defdata uoper (enum '(- /)))

;; Binary operators in SAEL:  + , * , ^ ,
(defdata boper (enum '(+ - * / ^)))

(check= (boperp '*) t)
(check= (boperp '^) t)
(check= (boperp '!) nil)

;; Mutually recursive def for SAEL expressions.
;; - usaexpr is a unary: (uoper saexpr)
;; - bsaexpr is a binary:(saexpr boper saexpr)
(defdata
  (saexpr (or rational
              var
              usaexpr
              bsaexpr))
  (usaexpr (list uoper saexpr))
  (bsaexpr (list saexpr boper saexpr)))

(check= (saexprp '((x + y) - (/ z))) t)
(check= (saexprp '(x + y + z)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2) ENVIRONMENTS: assignments + lookup
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assignment: vars to rationals
(defdata assignment (alistof var rational))

(check= (assignmentp '((x . 1) (y . 1/2))) t)
(check= (assignmentp '((x 1) (y 1/2))) nil)

;; lookup: return bound value if present, otherwise default to 1
(definec lookup (v :var a :assignment) :rational
  (if (endp a)
      1
      (let ((p (first a)))
        (if (eq v (first p))
            (rest p)
            (lookup v (rest a))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3) ERRORS + RESULTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata er 'error)
(defconst *er* (nth-er-builtin 0))

(defdata rat-err (or rational er))

;; Convenience predicate: true iff value is not error
(definec no-errorp (x :rat-err) :boolean
  (not (equal x *er*)))

;; added for (modeling-admit-all )
(defthm no-errorp->rational
    (implies (and (rat-errp v)
                  (no-errorp v))
             (rationalp v)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4) SEMANTICS: evaluator saeval
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: combine two rat-err values with a rational->rational->rational op
(definec binop-eval (op :boper x :rat-err y :rat-err) :rat-err
  (if (or (equal x *er*) (equal y *er*))
      *er*
      (case op
        (+ (+ x y))
        (- (- x y))
        (* (* x y))
        (/ (if (equal y 0) *er* (/ x y)))
        (^ (if (not (integerp y)) *er*
               (if (and (equal x 0) (< y 0)) *er*
                   (expt x y))))
        (otherwise *er*))))
;; The main evaluator
(definec saeval (e :saexpr a :assignment) :rat-err
  (match e
         (:rational e)
         (:var (lookup e a))
         (:usaexpr
          (('- x)
           (let ((vx (saeval x a)))
             (if (equal vx *er*) *er* (- vx))))
          (('/ x)
           (let ((vx (saeval x a)))
             (if (equal vx *er*) *er*
                 (if (equal vx 0) *er* (/ 1 vx))))))
         (:bsaexpr
          ((x '+ y) (binop-eval '+ (saeval x a) (saeval y a)))
          ((x '- y) (binop-eval '- (saeval x a) (saeval y a)))
          ((x '* y) (binop-eval '* (saeval x a) (saeval y a)))
          ((x '/ y) (binop-eval '/ (saeval x a) (saeval y a)))
          ((x '^ y) (binop-eval '^ (saeval x a) (saeval y a))))))

(check= (saeval '((x + y) - (- z))
                '((y . 3/2) (z . 1/2)))
        3)

(check= (saeval '(/ 0) nil) *er*)
(check= (saeval '(1 / 0) nil) *er*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5) PROPERTIES 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(property (a :assignment)
  (== (saeval 'x a)
      (saeval 'x a)))

;; 1) -x = -(-(-x)), for var x
(property (x :var a :assignment)
          (== (saeval (list '- x) a)
              (saeval (list '- (list '- (list '- x))) a)))

;; 2) (x - y) = (x + (- y)), for vars x, y
(property (x y :var a :assignment)
          (== (saeval (list x '- y) a)
              (saeval (list x '+ (list '- y)) a)))


;; 3) (x * (y + z)) = ((x * y) + (x * z)) distributivity for saexpr x y z
(property (x y z :saexpr a :assignment)
          (== (saeval (list x '* (list y '+ z)) a)
              (saeval (list (list x '* y) '+ (list x '* z)) a)))


;; 4) (1 / (x / y)) = (y / x) for saexpr x y
(property (x y :saexpr a :assignment)
          (let ((valueX (saeval x a))
                (valueY (saeval y a)))
            (=> (and (no-errorp valueX)
                     (no-errorp valueY)
                     (not (equal 0 valueX))
                     (not (equal 0 valueY)))
                (== (saeval (list 1 '/ (list x '/ y)) a)
                    (saeval (list y '/ x) a)))))

;; 5) (0 ^ x) = 0 for saexpr x
(property (x :saexpr a :assignment)
          (let ((n (saeval x a)))
            (=> (and (integerp n)
                     (> n 0))
                (== (saeval (list 0 '^ x) a)
                    0))))


;; 6) (x ^ ((2 * y) / y)) = (x ^ 2) for saexpr x y
(property (x y :saexpr a :assignment )
          (let ( (valueX (saeval x a))
                 (valueY (saeval y a)))
            (=> (and (no-errorp valueX)
                     (no-errorp valueY)
                     (rationalp valueY)
                     (not (zerop valueY)))
                (== (saeval (list x '^
                                  (list (list 2 '* y)
                                        '/
                                        y)) a)
                    (saeval (list x '^ 2) a)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6) AAEXPR / TRANSLATIONS / AAEVAL (placeholders)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; AAEL ::  rational | var | (- e) | (/ e) | (+ e e) | (- e e) | (* e e)
;;          | (/ e e) | (expt e e)

(defdata aaexpr
    (or rational
        var
        (list '- aaexpr)
        (list '/ aaexpr)
        (list '+ aaexpr aaexpr)
        (list '- aaexpr aaexpr)
        (list '* aaexpr aaexpr)
        (list '/ aaexpr aaexpr)
        (list 'expt aaexpr aaexpr)))

;; Converts a saexpr to an aaexpr
(definec sael->aa (e :saexpr) :aaexpr
  (match e
         (:rational e)
         (:var e)
         (:usaexpr
          (('- x) (list '- (sael->aa x)))
          (('/ x) (list '/ (sael->aa x))))
         (:bsaexpr
          ((x '+ y) (list '+    (sael->aa x) (sael->aa y)))
          ((x '- y) (list '-    (sael->aa x) (sael->aa y)))
          ((x '* y) (list '*    (sael->aa x) (sael->aa y)))
          ((x '/ y) (list '/    (sael->aa x) (sael->aa y)))
          ((x '^ y) (list 'expt (sael->aa x) (sael->aa y))))))

;; Converts an aaexpr to an saexpr
;; kept getting unused variable conflicts here because of the match macro, so instead of turning it off I did
;; a cond with an exhasutive search, using eq for object equality for the symbols
(definec aa->sael (e :aaexpr) :saexpr
  (cond
    ((rationalp e) e)
    ((varp e) e)
    ;; unary
    ((and (consp e) (equal (len e) 2) (eq (first e) '-))
     (list '- (aa->sael (first (rest e)))))
    ((and (consp e) (equal (len e) 2) (eq (first e) '/))
     (list '/ (aa->sael (first (rest e)))))
    ;; binary: (+ x y), (- x y), (* x y), (/ x y)
    ((and (consp e) (equal (len e) 3) (eq (first e) '+))
     (list (aa->sael (first (rest e))) '+ (aa->sael (first (rest (rest e))))))
    ((and (consp e) (equal (len e) 3) (eq (first e) '-))
     (list (aa->sael (first (rest e))) '- (aa->sael (first (rest (rest e))))))
    ((and (consp e) (equal (len e) 3) (eq (first e) '*))
     (list (aa->sael (first (rest e))) '* (aa->sael (first (rest (rest e))))))
    ((and (consp e) (equal (len e) 3) (eq (first e) '/))
     (list (aa->sael (first (rest e))) '/ (aa->sael (first (rest (rest e))))))
    ;; exponent: (expt x y)
    ((and (consp e) (equal (len e) 3) (eq (first e) 'expt))
     (list (aa->sael (first (rest e))) '^ (aa->sael (first (rest (rest e))))))
    (t
     ;; should be unreachable if e :aaexpr
     'x)))

;; aa->sael is the inverse of sael->aa
(property (x :saexpr)
          (== (aa->sael (sael->aa x))
              x ))

;; sael->aa is the inverse of aa->sael
(property (x  :aaexpr)
          (== (sael->aa (aa->sael x))
              x))

;; evaluates an aaexpr to a rational
;; had the same issue as aa->sael because the match had unused variables. I decided to try to use the case-match instead
;; to work with it.
(definec aaeval (e :aaexpr a :assignment) :rational
  (cond
    ((rationalp e) e)
    ((varp e) (lookup e a))

    (t
     (case-match e

       ;; unary minus: (- x)
       (('- x)
        (- (aaeval x a)))

       ;; unary reciprocal: (/ x)  div-by-0 => 0
       (('/ x)
        (let ((valueX (aaeval x a)))
          (if (equal valueX 0) 0 (/ 1 valueX))))

       ;; binary +
       (('+ x y)
        (+ (aaeval x a) (aaeval y a)))

       ;; binary -
       (('- x y)
        (- (aaeval x a) (aaeval y a)))

       ;; binary *
       (('* x y)
        (* (aaeval x a) (aaeval y a)))

       ;; binary /  div-by-0 => 0
       (('/ x y)
        (let ((valueY (aaeval y a)))
          (if (equal valueY 0)
              0
            (/ (aaeval x a) valueY))))

       ;; (expt x y) special cases:
       ;; if y=0 or y not integer => 1
       ;; else if x=0 => 0
       ;; else (expt x y)
       (('expt x y)
        (let ((valueX (aaeval x a))
              (valueY (aaeval y a)))
          (if (or (equal valueY 0) (not (integerp valueY)))
              1
            (if (equal valueX 0)
                0
              (expt valueX valueY)))))

       ;; should be unreachable if e :aaexpr, but totality fallback
       (& 0)))))


;; Test some properties here
;; Only time saexpr should deviate is when there is an error (aaexpr always returns a rational)

;; sael -> aael
(property (e :saexpr a :assignment)
          (=> (no-errorp (saeval e a))
              (== (aaeval (sael->aa e) a)
                  (saeval e a))))

;; aael -> sael
(property (e :aaexpr a :assignment)
          (=> (no-errorp (saeval (aa->sael e) a))
              (== (aaeval e a)
                  (saeval (aa->sael e) a))))


