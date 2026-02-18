#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
 Christopher Wright-Williams

|#



(in-package "ACL2S")
(set-gag-mode nil) 

(modeling-admit-all)
;; 70 percent usage of Codex to help with theorem proving
#|
[1,2,3] [4,5] []
-> bad-app [1,2,3] nil [4,5]
-> bad-app nil [1,2,3] [4,5]
-> bad-app nil [2,3] [1,4,5]
...
-> bad-app nil [] [3,2,1,4,5]
-> [3,2,1,4,5]

|#
(definec bad-app (x y acc :tl) :tl
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

; Q1a. We are using the definition on page 125
#|
(definec m-bad-app (x y :tl) :nat
  (+ (len x) (len y)))
|#
(definec m-bad-app (x y acc :tl) :lex
  (declare (ignorable acc))
  (match (list x y)
         ((nil nil) 0)
         ((nil &)   (len y))
         ((& nil)   '(1))
         (&         '(2))))

; in case 2, swap happens
(property case1-terminate (x acc :tl)
  :hyps (and (consp x))
  :body (l< (m-bad-app nil x acc)
	   (m-bad-app x nil acc)))

; in case 3, keep recursing and pushing into acc
(property case2-terminate (f :all acc r :tl)
  :body (l< (m-bad-app nil r (cons f acc))
	   (m-bad-app nil (cons f r) acc)))

; in case 4, inner recursive call decrements
(property case3-terminate (x y acc :tl)
  :hyps (and (consp x) (consp y))
  :body (l< (m-bad-app acc nil y)
	   (m-bad-app x y acc)))

; in case 4, outer recursive call decreases
(property case4-terminate (x y acc res :tl)
  :hyps (and (consp x) (consp y))
  :body (l< (m-bad-app x nil res)
	   (m-bad-app x y acc)))


(property rev-cdr+car (x :cons)
  (== (append (rev (cdr x)) (list (car x)))
      (rev x)))

(property bad-app-nil-is-revappend (y acc :tl)
  (== (bad-app nil y acc)
      (revappend y acc))
  :hints (("Goal"
           :in-theory (e/d (bad-app revappend)
                           (acl2::revappend-removal))
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (revappend y acc))))


(property (x y :tl)
    (== (bad-app x y nil)
     (if (endp x)
         (rev y)
         (if (endp y)
             (rev x)
             (app (rev x) y)))))

; lets use the measure function in the function:

(definec bad-app (x y acc :tl) :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
         ((nil nil) acc)
         ((& nil) (bad-app y x acc))
         ((nil (f . r)) (bad-app x r (cons f acc)))
         (& (bad-app x nil (bad-app acc nil y)))))




(ubt! 1)

; Q2

(definec ack (n m :nat) :pos
  :skip-tests t ; ack is slow, so skip testing
  (match (list n m)
         ((0 &) (1+ m))
         ((& 0) (ack (1- n) 1))
         (& (ack (1- n) (ack n (1- m))))))
; Q2a.  We are using the definition on page 129.
; Q2b. Further-generalized measure for ack (returns a lex)
; Using lex = (oneof nat (cons nat (listof nat))) and ordering l<
; (see “Further Generalized Measure Function Definition”) :contentReference[oaicite:1]{index=1}

(definec m-ack (n :nat m :all) :lex
  (list n (nfix m)))

(property (n m :nat)
          (implies (and (not (zp n))
                        (zp m))
                   (l< (m-ack (1- n) 1)
                       (m-ack n m))))

(property (n m :nat)
          (implies (and (not (zp n))
                        (not (zp m)))
                   (l< (m-ack n (1- m))
                       (m-ack n m))))

(property (n m :nat)
          (implies (and (not (zp n))
                        (not (zp m)))
                   (l< (m-ack (1- n) (ack n (1- m)))
                       (m-ack n m))))

; Lets use the measure function we made in ack
(definec ack (n m :nat) :pos
  :skip-tests t
  (declare (xargs :measure (m-ack n m)))
  (match (list n m)
         ((0 &) (1+ m))
         ((& 0) (ack (1- n) 1))
         (& (ack (1- n) (ack n (1- m))))))


(ubt! 1)

; Q3a. We are using the definition on page 129.

;; for if-expr, conditional can appear in condition position
;; for normative, conditional cannot appear in condition position
(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)


(definec if-flat-measure (x :if-expr) :nat
  (match x
    (:if-atom 0)
    (('if a b c)
     (+ 1 
        (* 2 (if-flat-measure a))
        (max (if-flat-measure b) (if-flat-measure c))))))

(defthm if-flat-measure-atomic-recurse-b
    (implies (and (if-atomp a)
		  (if-exprp b)
		  (if-exprp c))
     (< (if-flat-measure b)
	(if-flat-measure (list 'if a b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

(defthm if-flat-measure-atomic-recurse-c
  (implies (and (if-atomp a)
                (if-exprp b)
                (if-exprp c))
           (< (if-flat-measure c)
              (if-flat-measure (list 'if a b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

;; Case 2: Pullout transformation decreases measure
(defthm if-flat-measure-pullout-decreases
  (implies (and (if-atomp d)
                (if-atomp e)
                (if-atomp f)
                (if-exprp b)
                (if-exprp c))
           (< (if-flat-measure (list 'if d
                                     (list 'if e b c)
                                     (list 'if f b c)))
              (if-flat-measure (list 'if (list 'if d e f) b c))))
  :hints (("Goal" :in-theory (enable if-flat-measure))))

; check the first element of non-atom, if it is an atom, then recurse
; down to the end to check their conditional position
; if conditional is not atom, then we reconstruct it by first
; putting d at the first conditonal position, which decides
; if we go into e or f, and we put e and f on two branches
; if d is true, then we go into e, whose result should decide
; whether we go into b or c. similarly for f b c statement too
(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :consider-only-ccms ((if-flat-measure x))))
  ;:skip-admissibilityp t
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

;; match will check each element one by one then use let
;; to record its value

(defdata if-assign (alistof var bool))

(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

(defthm impossible-if-condition-shape
  (implies (and (not (consp e3))
                (not (booleanp e3))
                (not (varp e3))
                (consp e4)
                (consp (cdr e4))
                (not (cddr e4)))
           (not (if-exprp (list* 'if e3 e4)))))


(property if-flat-equal-if (e :if-expr a :if-assign)
  (== (if-eval e a)
      (if-eval (if-flat e) a)))

(in-theory (disable if-flat-equal-if))

; returns nil when not a bool and can't be found in assignment
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))


(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a) ; check either branch's validity
             (validp y a)
           (validp z a)) 
       ; check if then branch suppose x is true

       (and (validp y (acons x t a)) 
       ; check if else branch suppose x is nil
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

;; Main soundness theorem
(definec extend-assign (req :if-assign a :if-assign) :if-assign
  (match req
    (nil a)
    (((k . v) . rst)
     (acons k v (extend-assign rst a)))))

;; if your assignment has an assignment for a variable,
;; adding it does not matter, so collapse to simpler form
(defthm if-eval-acons-same-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (booleanp v)
                (equal (lookup-var x a) v))
           (equal (if-eval e (acons x v a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable if-eval lookup-atom)
           :induct (if-eval e a))))

;; a more specific form than before
(defthm if-eval-acons-true-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (lookup-var x a))
           (equal (if-eval e (acons x t a))
                  (if-eval e a)))
  :hints (("Goal"
           :use ((:instance if-eval-acons-same-when-lookup
                            (e e)
                            (a a)
                            (x x)
                            (v t))))))

;; a specific form like previous
(defthm if-eval-acons-false-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (not (lookup-var x a)))
           (equal (if-eval e (acons x nil a))
                  (if-eval e a)))
  :hints (("Goal"
           :use ((:instance if-eval-acons-same-when-lookup
                            (e e)
                            (a a)
                            (x x)
                            (v nil))))))

;; similar to before but in a different form 
(defthm if-eval-cons-cons-true-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (lookup-var x a))
           (equal (if-eval e (cons (cons x t) a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable acons)
           :use ((:instance if-eval-acons-true-when-lookup
                            (e e)
                            (a a)
                            (x x))))))

;; similar to before
(defthm if-eval-cons-list-false-when-lookup
  (implies (and (if-exprp e)
                (if-assignp a)
                (varp x)
                (not (lookup-var x a)))
           (equal (if-eval e (cons (list x) a))
                  (if-eval e a)))
  :hints (("Goal"
           :in-theory (enable acons)
           :use ((:instance if-eval-acons-false-when-lookup
                            (e e)
                            (a a)
                            (x x))))))

;; similar to before but now adding to assignments
(defthm lookup-var-extend-assign-when-assigned
  (implies (and (varp x)
                (if-assignp req)
                (if-assignp a)
                (consp (assoc-equal x req)))
           (equal (lookup-var x (extend-assign req a))
                  (lookup-var x req)))
  :hints (("Goal"
           :in-theory (enable extend-assign lookup-var)
           :induct (lookup-var x req))))

;; similar 
(defthm lookup-atom-extend-assign-when-assigned
  (implies (and (if-atomp x)
                (if-assignp req)
                (if-assignp a)
                (assignedp x req))
           (equal (lookup-atom x (extend-assign req a))
                  (lookup-atom x req)))
  :hints (("Goal"
           :in-theory (enable assignedp lookup-atom))))

;; similar
(defthm lookup-var-true-preserved-by-extend-assign
  (implies (and (if-assignp req)
                (if-assignp a)
                (varp x)
                (lookup-var x req))
           (lookup-var x (extend-assign req a)))
  :hints (("Goal"
           :in-theory (enable extend-assign lookup-var)
           :induct (extend-assign req a))))

;; if validp says the normalized if-expr is true under req,
;; then adding extensions to it does not change its truth
(defthm validp-sound-on-extend-assign
  (implies (and (norm-if-exprp n)
                (if-assignp req)
                (if-assignp a)
                (validp n req))
           (if-eval n (extend-assign req a)))
  :hints (("Goal"
           :in-theory (enable validp if-eval assignedp lookup-atom extend-assign
                              if-eval-acons-true-when-lookup
                              if-eval-acons-false-when-lookup
                              if-eval-cons-cons-true-when-lookup
                              if-eval-cons-list-false-when-lookup)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (validp n req))))

;; if normalized n is valid with no assumptions
;; then it evals to true under any assumption
(property validp-nil-sound (n :norm-if-expr a :if-assign)
  (implies (validp n nil)
           (if-eval n a))
  :hints (("Goal"
           :in-theory (enable extend-assign)
           :use ((:instance validp-sound-on-extend-assign
                            (n n)
                            (req nil)
                            (a a))))))

;; if the original expr e is valid, then
;; its flattened norm form is valid with no assumption
(defthm check-validp-is-sound-flat
  (implies (and (if-exprp e)
                (if-assignp a)
                (check-validp e))
           (if-eval (if-flat e) a))
  :hints (("Goal"
           :in-theory (enable check-validp)
           :use ((:instance validp-nil-sound
                            (n (if-flat e))
                            (a a))))))

(property check-validp-is-sound (e :if-expr a :if-assign)
  (implies (check-validp e)
           (if-eval e a))
  :hints (("Goal"
           :use ((:instance check-validp-is-sound-flat
                            (e e)
                            (a a))
                 (:instance if-flat-equal-if
                            (e e)
                            (a a))))))

;; Q3f completeness witness
(definec counterexample-assign (n :norm-if-expr req :if-assign) :if-assign
  (declare (xargs :consider-only-ccms ((if-flat-measure n))))
  (match n
    (:if-atom req)
    (('if x y z)
     (if (assignedp x req)
         (if (lookup-atom x req)
             (counterexample-assign y req)
           (counterexample-assign z req))
       (if (not (validp y (acons x t req)))
           (counterexample-assign y (acons x t req))
         (counterexample-assign z (acons x nil req)))))))

(defthm lookup-var-acons-diff
  (implies (and (varp x)
                (varp y)
                (booleanp v)
                (if-assignp a)
                (not (equal x y)))
           (equal (lookup-var x (acons y v a))
                  (lookup-var x a)))
  :hints (("Goal"
           :in-theory (enable lookup-var))))

(defthm lookup-atom-counterexample-assign-when-assigned
  (implies (and (if-atomp x)
                (norm-if-exprp n)
                (if-assignp req)
                (assignedp x req))
           (equal (lookup-atom x (counterexample-assign n req))
                  (lookup-atom x req)))
  :hints (("Goal"
           :in-theory (enable counterexample-assign assignedp lookup-atom)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (counterexample-assign n req))))

(defthm counterexample-assign-falsifies-validp
  (implies (and (norm-if-exprp n)
                (if-assignp req)
                (not (validp n req)))
           (not (if-eval n (counterexample-assign n req))))
  :hints (("Goal"
           :in-theory (enable counterexample-assign validp if-eval assignedp lookup-atom)
           :do-not '(generalize eliminate-destructors fertilize)
           :induct (counterexample-assign n req))))

(defthm check-validp-is-complete-flat
  (implies (and (if-exprp e)
                (not (check-validp e)))
           (not (if-eval (if-flat e)
                         (counterexample-assign (if-flat e) nil))))
  :hints (("Goal"
           :in-theory (enable check-validp)
           :use ((:instance counterexample-assign-falsifies-validp
                            (n (if-flat e))
                            (req nil))))))

;; a failure => a counterexample
(property check-validp-is-complete (e :if-expr)
  (let ((a (counterexample-assign (if-flat e) nil)))
    (implies (not (check-validp e))
             (and (if-assignp a)
                  (not (if-eval e a)))))
  :hints (("Goal"
           :use ((:instance check-validp-is-complete-flat
                            (e e))
                 (:instance if-flat-equal-if
                            (e e)
                            (a (counterexample-assign (if-flat e) nil)))))))

(ubt! 1)

#|
 Q4. We will now reason about sorting algorithms. Consider the
 following definitions for insert sort and quicksort.
|#

;; See the documentation for <<, which is a total order on the ACL2s
;; universe, so we can compare anything, no matter the types. This
;; allows us to define sorting algorithms that work on integers,
;; rationals, strings, whatever (but using the << ordering.

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

;; we need to describe that elements in an isorted list are ordered
(definec orderedp (x :tl) :boolean
  (or (endp x)
      (endp (cdr x))
      (^ (<<= (first x) (second x))
         (orderedp (cdr x)))))

; We need the lemma that insert preserves order to avoid nested
; induction in later lemmas
(property insert-preserves-order (l :tl a :all)
          :h (orderedp l)
          :b (orderedp (insert a l)))

(property isort-ordered (l :tl)
          (orderedp (isort l)))

; Helper lemma from checkpoint
(property less-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (less a (insert b l))
                 (less a l)))

; We need the invariant that l is ordered
(property less-insert-<< (l :tl a :all b :all)
          :h (^ (<< b a)
                (orderedp l))
          :b (== (less a (insert b l))
                 (insert b (less a l))))

; Lemma 1
(property isort-less (l :tl a :all)
          (== (isort (less a l))
              (less a (isort l))))

; Helper lemmas for Lemma 2 (symmetric from Lemma 1)
(property notless-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (insert b (notless a l))
                 (notless a (insert b l))))

; Helper lemma
(property notless-insert-<< (l :tl a :all b :all)
          :h (<< b a)
          :b (== (notless a (insert b l))
                 (notless a l)))

; Lemma 2
(property isort-notless (l :tl a :all)
          (== (isort (notless a l))
              (notless a (isort l))))

; Helper lemma
(property orderedp-<=-less (l :tl a :all)
          :h (^ (orderedp l) (<<= a (first l)))
          :b (== (less a l) nil))

; Lemma 3
(property app-less-not-less (l :tl a :all)
          :h (orderedp l)
          :b (== (append (less a l)
                         (cons a (notless a l)))
                 (insert a l)))

; Bridge lemma in the same app-shape used by qsort checkpoints
(property app-less-not-less-app (l :tl a :all)
          :h (orderedp l)
          :b (== (app (less a l)
                      (cons a (notless a l)))
                 (insert a l)))

#|
 Q4. Prove the following property.
 This is not easy, so I strongly recommend that you come up with a
 plan and use the professional method to sketch out a proof.
|#

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))
