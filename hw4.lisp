==#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
 ... (put the names of the group members here)

|#

#|

 In this homework, you will use ACL2s to prove theorems.  Think of
 ACL2s as a proof checker. You give it a proof outline and it checks
 it for you.  The high-level idea is that you provide ACL2s with
 theorems (named properties) that can be proved with, ideally, one
 level of induction. ACL2s will take care of the details, so that you
 do not have to, but you are still responsible for coming up with a
 proof outline.

 To use ACL2s effectively, you need to understand how ACL2s works,
 which we covered in class. For example, recall that theorems can be
 of different types; see rule-classes. Most of your theorems will be
 rewrite rules, so make sure you orient them appropriately and follow
 the other guidelines mentioned in class.  Also, you can specify which
 induction to use or any other hints, using the same options as defthm
 takes (see the documentation).

 The main challenge is figuring out which supporting theorems (lemmas)
 you need to prove the top-level theorems. The use of the professional
 method can be very helpful here. 

 When ACL2s gets stuck or some theorem is not going through, use the
 "method" to figure out what ACL2s does not know that will allow it to
 make progress. 

 For all your proofs in this homework, ACL2s should never do nested
 inductions. If it does, specify an appropriate lemma so that nested
 inductions are not needed.

 This homework has some hard problems, so start early and ask
 questions. 

|#

(in-package "ACL2S")
(set-gag-mode nil) ; ACL2s shows what it is doing.

#|

 Start with the configuration below and once you are done with the
 homework, go to the next configuration, cranking up the rigor all the
 way up to (modeling-admit-all). That is, when you submit your
 homework the form below must be (modeling-admit-all), if you want to
 get full credit.

 After (modeling-start), try (modeling-validate-defs), then 
 (modeling-admit-defs) and finally (modeling-admit-all).

 Tip: once you get one configuration working, you can test that there
 were no errors by going to the shell buffer and typing the following.

 (ubt! 1)
 (ld "hwk4.lisp")

 The first form undoes everything and the second loads hwk4.lisp. For
 the ld to work, you must have started acl2s in the directory where
 hwk4 resides, otherwise you have to specify a path. If the ld
 encounters an error, you will see it and you can see where that error
 occurred by typing

 (pbt 0)

 which will show you what events were accepted.

 Once that is working, change the configuration to the next one and do
 it again, fixing problems until done.

 Each problem has its own configuration, which gives you the
 flexibility work on problems in any order and to have different
 levels of rigor per problem, at a given point in time. All
 configurations should be set to (modeling-admit-all) to get full
 credit.

|#

(modeling-start)

#|

Q1. Consider the following definition

|#

(definec bad-app (x y acc :tl) :tl
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. See the RAP lecture notes on measures; you can use
 generalized measure functions.

|#

; Define, m-bad-app, a measure function for bad-app.
; Q1a. We are using the definition on page 125

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q1b. Fill in the definition
(definec m-bad-app (x y :tl acc :all) :nat
  (cond
    ; if both are empty, then no recursion -> no measure decrease
    ((and (endp x) (endp y)) 0)
    ; because of the swap when y is nil, we need x not nil and y nil state to be bigger
    ; than x nil, y not nil
    ((endp x) (len y))
    ((endp y) (+ 1 (len x)))
    (t (+ 2 (len x) (len acc)))))

; The proof obligations for the termination proof of bad-app, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed. 

; Q1c
; this is for the swap case (& nil)
(property (x y :tl acc :all)

          (=> (and (consp x) (endp y))
              (< (m-bad-app y x acc)
                 (m-bad-app x y acc))))
; this is for case where x is nil, and y is cons (after swap)
(property (x y :tl acc :all)
          (=> (and (endp x) (consp y))
              (< (m-bad-app x (rest y) (cons (first y) acc))
                 (m-bad-app x y acc))))
(property (x y :tl acc :all)
          (=> (and (consp x) (consp y) (tlp acc))
              (and
               ; inner call decreases
               (< (m-bad-app acc nil y)
                  (m-bad-app x y acc))
               ; outer call decreases
               (< (m-bad-app x nil (bad-app acc nil y))
                  (m-bad-app x y acc)))))

; Relate bad-app to app.
; Fill in the ... part below. You can only use functions app, rev, if
; and endp. Make sure that ACL2s can prove the property.

; Q1d
(property (x y :tl)
  (== (bad-app x y nil)
      ...))

; Configuration: update as per instructions
(modeling-start)

#|

Q2. Consider the following definition.

|#

(definec ack (n m :nat) :pos
  :skip-tests t ; ack is slow, so skip testing
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. 

|#

; Define, m-ack, a measure function for ack.
; Q2a. We are using the definition on page ...

; Note: fill in the ...'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q2b. Fill in the definition
(definec m-ack (...) ...
  ...)

; The proof obligations for the termination proof of ack, using
; properties.  Make sure that ACL2s can prove all of these
; properties. 

; Q2c
(property ...)
(property ...)
(property ...)
  
; Configuration: update as per instructions
(modeling-start)

#|

Q3. Consider the following definitions.

|#

(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)

; The :skip-admissibilityp command below tells ACL2s to skip the
; termination proof, as ACL2s cannot prove termination without help.

(definec if-flat (x :if-expr) :norm-if-expr
  :skip-admissibilityp t
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

#|

 Since match is a macro, it may help to know exactly what it expands
 into. If you aren't familiar with the backquote/comma duo, look it up
 and it may be useful to see what this expands into also. You can
 check using the ":trans1" form, which expands the top-level form one
 time and expands backquote/commas. To fully expand a form you can use
 ":trans" but that expands lets and conds and so on and may not be
 that readable. Try the following

 :trans1 (match x
           (:if-atom x)
           (('if a b c)
            (match a
              (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
              (('if d e f)
               (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))))))

 Notice that the nested match was not expanded, but you can copy that
 form and run trans1 on it to expand it.

|#

; Define, m-if-flat, a measure function for if-flat.
; Q3a. We are using the definition on page ...


; Q3b. Fill in the definition. This definition must be accepted by
; ACL2s. 
(definec m-if-flat (...) ...
  ...)

; The proof obligations for the termination proof of if-flat, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed. 

; Q3c
(property ...)
(property ...)
(property ...)

#|
 
 We will now prove that if-flat does not change the semantics of if
 expressions using ideas similar to those from HWK2. We will define
 assignments and an evaluator for if expressions.

|#

(defdata if-assign (alistof var bool))

; Notice that if var is not in the if-assign, we return nil.
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

; Q3d
; State and prove that for all if-assign's, an if-expr e evaluates to
; the same thing as (if-flat e). This should go though automatically,
; but, remember, you have to provide enough lemmas so that there are
; no nested inductions! Also, remember theorems are rewrite rules, so
; orient appropriately.

(property if-flat-equal-if (...)
  ...)

#|

 Check-validp is a simple validity checker for if-expr's.  The idea is
 to use if-flat to normalize the if-expr. Then, we start with an empty
 if-assign and check validity by traversing the expression. When we
 get to a variable that is not assigned, we check that the expression
 is a validity when the variable is t and when it is nil.

|# 

; Lookup assoc-equal in the documentation.
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))

(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (validp y a)
           (validp z a))
       (and (validp y (acons x t a))
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

; Q3e
; 
; Formalize and prove the soundness of check-validp.  That is, if
; (check-validp e) = t, then evaluating e under a, an arbitrary
; if-assign, results in t.

(property check-validp-is-sound ...
  ...)

; Configuration: update as per instructions
(modeling-start)


; Q3f
; 
; Prove that check-validp is complete by showing that when
; check-validp returns nil, there is some if-assign under which the
; if-expr evaluates to nil. With this proof, we now know that
; check-validp is a decision procedure for PL validity.

...

#|

 Q4. We will now reason about sorting algorithms. Consider the
 following definitions for insert sort and quicksort.

|#

;; See the documentation for <<, which is a total order on the ACL2s
;; universe, so we can compare anything, no matter the types. This
;; allows us to define sorting algorithms that work on integers,
;; rationals, strings, whatever (but using the << ordering).

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

#|

 Q4. Prove the following property.

 This is not easy, so I strongly recommend that you come up with a
 plan and use the professional method to sketch out a proof.

|#

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))

#|

 Extra Credit 1. (25 points each, all or nothing)


 1. First, prove (in ACL2s) that if x and y are ordered true lists,
 under <<=, and permutations of each other, they are equal. Second,
 prove that qsort and isort return ordered permutations of their
 input.

 2. Do the homework in another theorem prover of your choice. Try to
 make it as equivalent as possible. Provide a summary of your
 findings.  This is only recommended for those of you that already
 have experience with other theorem provers. ACL2 is not allowed this
 time.

|#
