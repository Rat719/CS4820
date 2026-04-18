#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Spring 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

 The group members are:

 ... (put the names of the group members here)
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t.

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. 

|#

;; -------------------------------------------------------------------------
;; Helpers
;; -------------------------------------------------------------------------
 
(defun negate-lit (x)
  ;; Flip polarity of a literal; used for complementary-pair detection.
  (if (and (consp x) (== (car x) 'not))
      (cadr x)
      (list 'not x)))
 
(defun flatten-op-args (op args)
  ;; For AC ops (and, or, iff), splice (op ...) children into parent.
  (if (in op '(and or iff))
      (mapcan (lambda (a)
                (if (and (consp a) (== (car a) op))
                    (copy-list (cdr a))
                    (list a)))
              args)
      args))
 
(defun make-nary (op args)
  ;; Arity collapse: () -> identity, (x) -> x, else (op . args).
  (cond
    ((and (== op 'and) (null args)) t)
    ((and (== op 'or)  (null args)) nil)
    ((and (== op 'iff) (null args)) t)
    ((and (in op '(and or iff))
          (== (len args) 1))
     (first args))
    (t (cons op args))))
 
;; Free variables, for Rule F.
(defun q-vars (vars)
  (if (consp vars) vars (list vars)))
 
(defun free-vars (f)
  (cond
    ((variable-symbolp f) (list f))
    ((or (constant-symbolp f)
         (constant-objectp f)
         (quotep f))
     nil)
    ((atom f) nil)
    ((and (consp f) (in (car f) *fo-quantifiers*))
     (set-difference (free-vars (caddr f)) (q-vars (cadr f)) :test #'equal))
    (t
     (reduce (lambda (a b) (union a b :test #'equal))
             (mapcar #'free-vars (cdr f))
             :initial-value nil))))
 
;; -------------------------------------------------------------------------
;; Constant folding (Rule G)
;; -------------------------------------------------------------------------
 
(defun ground-termp (tm)
  (cond ((constant-objectp tm) t)
        ((quotep tm) t)
        ((constant-symbolp tm) nil)
        ((variable-symbolp tm) nil)
        ((consp tm)
         (and (function-symbolp (car tm))
              (every #'ground-termp (cdr tm))))
        (t nil)))
 
(defun try-constant-fold (tm)
  ;; Evaluate tm via ACL2s. acl2s-compute returns a single list (erp val):
  ;; erp is nil on success, non-nil on guard/type violation.
  ;; On success return the folded value (constant-object as-is, else quoted);
  ;; on any failure (guard violation, error) return tm unchanged.
  (handler-case
      (let ((r (acl2s-compute (to-acl2s tm))))
        (cond
          ((and (consp r) (null (car r)))
           (let ((v (cadr r)))
             (if (constant-objectp v) v (list 'quote v))))
          (t tm)))
    (error () tm)))
 
(defun fo-simplify-term (tm)
  (cond
    ((variable-symbolp tm) tm)
    ((constant-symbolp tm) tm)
    ((constant-objectp tm) tm)
    ((quotep tm) tm)
    ((atom tm) tm)
    ((consp tm)
     (let* ((args (mapcar #'fo-simplify-term (cdr tm)))
            (new-tm (cons (car tm) args)))
       (if (every #'ground-termp args)
           (try-constant-fold new-tm)
           new-tm)))
    (t tm)))
 
;; -------------------------------------------------------------------------
;; Main simplifier
;; -------------------------------------------------------------------------
 
(defun fo-simplify (f)
  (cond
    ;; leaves
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((constant-objectp f) f)
    ((quotep f) f)
    ((atom f) f)
    ;; quantifier
    ((in (car f) *fo-quantifiers*)
     (simplify-quant (car f) (cadr f) (fo-simplify (caddr f))))
    ;; propositional operator
    ((p-funp (car f))
     (simplify-p-op (car f) (mapcar #'fo-simplify (cdr f))))
    ;; equality atom
    ((== (car f) '=)
     (let ((t1 (fo-simplify-term (cadr f)))
           (t2 (fo-simplify-term (caddr f))))
       (if (equal t1 t2) t (list '= t1 t2))))
    ;; relation application
    (t (cons (car f) (mapcar #'fo-simplify-term (cdr f))))))
 
(defun simplify-quant (q vars body)
  (let* ((fv (free-vars body))
         (kept (remove-if-not (lambda (v) (in v fv)) (q-vars vars))))
    (cond
      ((endp kept) body)
      ((and (not (consp vars)) (endp (cdr kept)))
       (list q (car kept) body))
      (t (list q kept body)))))
 
(defun simplify-p-op (op sargs)
  (let ((sargs (flatten-op-args op sargs)))
    (case op
      (not
       (let ((a (first sargs)))
         (cond
           ((and (consp a) (== (car a) 'not)) (cadr a))
           ((booleanp a) (not a))
           (t (list 'not a)))))
      (and
       (cond
         ((member nil sargs :test #'equal) nil)
         (t (let ((sargs (remove t sargs :test #'equal)))
              (cond
                ((some (lambda (x) (member (negate-lit x) sargs :test #'equal))
                       sargs)
                 nil)
                (t (make-nary 'and (remove-dups sargs))))))))
      (or
       (cond
         ((member t sargs :test #'equal) t)
         (t (let ((sargs (remove nil sargs :test #'equal)))
              (cond
                ((some (lambda (x) (member (negate-lit x) sargs :test #'equal))
                       sargs)
                 t)
                (t (make-nary 'or (remove-dups sargs))))))))
      (iff (simplify-iff sargs))
      (implies
       (destructuring-bind (p q) sargs
         (cond ((== p nil) t)
               ((== p t)   q)
               ((== q t)   t)
               ((== q nil) (fo-simplify `(not ,p)))
               ((equal p q) t)
               (t `(implies ,p ,q)))))
      (if
       (destructuring-bind (c tb fb) sargs
         (cond ((== c t)    tb)
               ((== c nil)  fb)
               ((equal tb fb) tb)
               (t `(if ,c ,tb ,fb)))))
      (otherwise (cons op sargs)))))
 
(defun iff-odd-occurrences (args)
  ;; Keep only elements appearing an odd number of times (equal pairs cancel).
  (let ((result '()))
    (dolist (a args)
      (if (find a result :test #'equal)
          (setf result (remove a result :test #'equal :count 1))
          (push a result)))
    (nreverse result)))
 
(defun simplify-iff (sargs)
  (let* ((sargs     (remove t sargs :test #'equal))
         (nil-count (count nil sargs :test #'equal))
         (sargs     (remove nil sargs :test #'equal))
         (has-comp  (some (lambda (x) (member (negate-lit x) sargs :test #'equal))
                          sargs))
         (sargs     (iff-odd-occurrences sargs))
         (base      (if has-comp nil (make-nary 'iff sargs))))
    (if (oddp nil-count)
        (fo-simplify `(not ,base))
        base)))
;; Tests for Q1
;; =========================================================================
 
(defparameter *test-fails* 0)
(defparameter *test-passes* 0)
 
(defun test-simplify (name input expected)
  (let ((actual (fo-simplify input)))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a~%" name))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name input expected actual)))))
 
(defun run-tests ()
  (setf *test-passes* 0)
  (setf *test-fails* 0)
 
  ;; Rule A: identity removal
  (test-simplify "A.1 drop t from and" '(and (p x) t (q y)) '(and (p x) (q y)))
  (test-simplify "A.2 drop nil from or" '(or nil (p x) nil (q y)) '(or (p x) (q y)))
  (test-simplify "A.3 constants in term positions preserved"
                 '(and (p x) t (q t y) (q y z))
                 '(and (p x) (q t y) (q y z)))
 
  ;; Rule B: flattening
  (test-simplify "B.1 flatten nested and"
                 '(and (p x) (and (q y) (r z)))
                 '(and (p x) (q y) (r z)))
  (test-simplify "B.2 0-ary and -> t" '(and) t)
  (test-simplify "B.3 1-ary or -> its arg" '(or (p x)) '(p x))
  (test-simplify "B.4 deeply nested collapses"
                 '(and (or (and (p x))) (and (q y)))
                 '(and (p x) (q y)))
 
  ;; Rule C: sink short-circuit
  (test-simplify "C.1 and with nil -> nil" '(and (p x) nil (q y)) nil)
  (test-simplify "C.2 or with t -> t" '(or (p x) t (q y)) t)
  (test-simplify "C.3 sink after flatten"
                 '(and (p x) (and (q y) nil)) nil)
 
  ;; Rule D: double negation
  (test-simplify "D.1 not not p -> p" '(not (not (p x))) '(p x))
  (test-simplify "D.2 triple negation" '(not (not (not (p x)))) '(not (p x)))
  (test-simplify "D.3 not t -> nil" '(not t) nil)
 
  ;; Rule E: complement/idempotency
  (test-simplify "E.1 and p (not p) -> nil"
                 '(and (p a) (not (p a))) nil)
  (test-simplify "E.2 or with complements -> t"
                 '(or (f) (f1) (p a b) (not (p a b)) (= w z)) t)
  (test-simplify "E.3 dedup under and"
                 '(and (p x) (p x) (q y)) '(and (p x) (q y)))
 
  ;; Rule F: vacuous quantifiers
  (test-simplify "F.1 fully vacuous forall drops"
                 '(forall (x w) (p y z)) '(p y z))
  (test-simplify "F.2 partially vacuous forall"
                 '(forall (x w) (p x y z)) '(forall (x) (p x y z)))
  (test-simplify "F.3 single-var vacuous"
                 '(exists w (p y z)) '(p y z))
  (test-simplify "F.4 non-vacuous preserved"
                 '(forall (x) (p x y)) '(forall (x) (p x y)))
 
  ;; iff
  (test-simplify "iff.1 (iff p p) -> t" '(iff (p x) (p x)) t)
  (test-simplify "iff.2 (iff p (not p)) -> nil"
                 '(iff (p x) (not (p x))) nil)
  (test-simplify "iff.3 empty iff -> t" '(iff) t)
  (test-simplify "iff.4 single-arg iff" '(iff (p x)) '(p x))
 
  ;; implies / if
  (test-simplify "impl.1 (implies t q) -> q" '(implies t (q x)) '(q x))
  (test-simplify "impl.2 (implies p nil) -> (not p)"
                 '(implies (p x) nil) '(not (p x)))
  (test-simplify "if.1 (if t a b) -> a" '(if t (p x) (q y)) '(p x))
  (test-simplify "if.2 (if c a a) -> a"
                 '(if (r z) (p x) (p x)) '(p x))
 
  ;; Integration
  (test-simplify "int.1 nested identities + flatten"
                 '(and t (or nil (p x)) t (and (q y) t))
                 '(and (p x) (q y)))
  (test-simplify "int.2 complement exposed after identity drop"
                 '(or nil (p x) (not (p x))) t)
  (test-simplify "int.3 quantifier becomes vacuous after body collapses"
                 '(forall (x) (and t t)) t)
  (test-simplify "int.4 quantifier body collapses to t"
                 '(forall (x y) (or t (p x))) t)
 
  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))
 
;; Rule G tests - require live ACL2s. Run separately with (run-rule-g-tests).
;; Each call to acl2s-compute spawns a subprocess, so these are slow
;; (5-15s each). Don't run them in tight dev loops.
(defun run-rule-g-tests ()
  (setf *test-passes* 0)
  (setf *test-fails* 0)
  (test-simplify "G.1 fold ground arithmetic"
                 '(p (binary-+ 4 2) 3)
                 '(p 6 3))
  (test-simplify "G.2 non-ground arg left alone"
                 '(p (binary-+ x 2) 3)
                 '(p (binary-+ x 2) 3))
  (test-simplify "G.3 guard violation returns term unchanged"
                 '(p (binary-+ 'a 2) 3)
                 '(p (binary-+ 'a 2) 3))
  (test-simplify "G.4 nested fold"
                 '(p (binary-+ (binary-+ 1 1) 2))
                 '(p 4))
  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))
#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun nnf (f)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((constant-objectp f) f)
    ((quotep f) f)
    ((atom f) f)
    (t
     (case (car f)
       (not (nnf-not (cadr f)))
       (and (cons 'and (mapcar #'nnf (cdr f))))
       (or  (cons 'or  (mapcar #'nnf (cdr f))))
       (implies
        (list 'or (nnf-not (cadr f)) (nnf (caddr f))))
       (iff (nnf-iff (cdr f)))
       (if
        (let ((c (cadr f)) (a (caddr f)) (b (cadddr f)))
          (list 'or
                (list 'and (nnf c) (nnf a))
                (list 'and (nnf-not c) (nnf b)))))
       (otherwise
        (cond
          ((in (car f) *fo-quantifiers*)
           (list (car f) (cadr f) (nnf (caddr f))))
          (t f)))))))
 
(defun nnf-not (f)
  ;; Returns the NNF of (not f).
  (cond
    ((booleanp f) (not f))
    ((variable-symbolp f) (list 'not f))
    ((constant-symbolp f) (list 'not f))
    ((constant-objectp f) (list 'not f))
    ((quotep f) (list 'not f))
    ((atom f) (list 'not f))
    (t
     (case (car f)
       (not (nnf (cadr f)))
       (and (cons 'or  (mapcar #'nnf-not (cdr f))))
       (or  (cons 'and (mapcar #'nnf-not (cdr f))))
       (implies
        (list 'and (nnf (cadr f)) (nnf-not (caddr f))))
       (iff (nnf-not-iff (cdr f)))
       (if
        (let ((c (cadr f)) (a (caddr f)) (b (cadddr f)))
          (list 'and
                (list 'or (nnf-not c) (nnf-not a))
                (list 'or (nnf c) (nnf-not b)))))
       (otherwise
        (cond
          ((== (car f) 'forall)
           (list 'exists (cadr f) (nnf-not (caddr f))))
          ((== (car f) 'exists)
           (list 'forall (cadr f) (nnf-not (caddr f))))
          (t (list 'not f))))))))
 
(defun nnf-iff (args)
  (cond
    ((endp args) t)
    ((endp (cdr args)) (nnf (car args)))
    ((endp (cddr args))
     (let ((p (car args)) (q (cadr args)))
       (list 'and
             (list 'or (nnf-not p) (nnf q))
             (list 'or (nnf p) (nnf-not q)))))
    (t
     (nnf (list 'iff (car args) (cons 'iff (cdr args)))))))
 
(defun nnf-not-iff (args)
  (cond
    ((endp args) nil)
    ((endp (cdr args)) (nnf-not (car args)))
    ((endp (cddr args))
     (let ((p (car args)) (q (cadr args)))
       (list 'or
             (list 'and (nnf p) (nnf-not q))
             (list 'and (nnf-not p) (nnf q)))))
    (t
     (nnf-not (list 'iff (car args) (cons 'iff (cdr args)))))))
 
(defun test-nnf (name input expected)
  (let ((actual (nnf input)))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a~%" name))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name input expected actual)))))
 
(defun run-nnf-tests ()
  (setf *test-passes* 0)
  (setf *test-fails* 0)
 
  (test-nnf "atom passes through" '(p x) '(p x))
  (test-nnf "equality passes through" '(= x y) '(= x y))
  (test-nnf "boolean passes through" t t)
  (test-nnf "not of atom" '(not (p x)) '(not (p x)))
  (test-nnf "not of not" '(not (not (p x))) '(p x))
  (test-nnf "de morgan and" '(not (and (p) (q)))
            '(or (not (p)) (not (q))))
  (test-nnf "de morgan or" '(not (or (p) (q)))
            '(and (not (p)) (not (q))))
  (test-nnf "implies" '(implies (p) (q))
            '(or (not (p)) (q)))
  (test-nnf "not implies" '(not (implies (p) (q)))
            '(and (p) (not (q))))
  (test-nnf "iff 2-ary"
            '(iff (p) (q))
            '(and (or (not (p)) (q)) (or (p) (not (q)))))
  (test-nnf "not iff"
            '(not (iff (p) (q)))
            '(or (and (p) (not (q))) (and (not (p)) (q))))
  (test-nnf "if"
            '(if (c) (a) (b))
            '(or (and (c) (a)) (and (not (c)) (b))))
  (test-nnf "not forall"
            '(not (forall x (p x)))
            '(exists x (not (p x))))
  (test-nnf "not exists"
            '(not (exists x (p x)))
            '(forall x (not (p x))))
  (test-nnf "nested: not (implies p (and q r))"
            '(not (implies (p) (and (q) (r))))
            '(and (p) (or (not (q)) (not (r)))))
  (test-nnf "deep nesting"
            '(not (and (implies (p) (q)) (or (r) (not (s)))))
            '(or (and (p) (not (q))) (and (not (r)) (s))))
  (test-nnf "relation with args"
            '(and (p x y) (not (q z)))
            '(and (p x y) (not (q z))))
 
  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))
#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

;; Fresh name generation
;; -------------------------------------------------------------------------

(defparameter *fresh-counter* 0)

(defun reset-fresh-counter ()
  (setf *fresh-counter* 0))

(defun fresh-var ()
  (intern (format nil "V~a" (incf *fresh-counter*)) :tp))

(defun fresh-skolem ()
  (intern (format nil "SK~a" (incf *fresh-counter*)) :tp))

;; Scan input for any pre-existing V<n> or SK<n> and bump the counter past them,
;; so our fresh names never clash with user-provided symbols.
(defun all-symbols (f)
  (cond ((symbolp f) (list f))
        ((atom f) nil)
        (t (append (all-symbols (car f)) (all-symbols (cdr f))))))

(defun parse-trailing-nat (name start)
  (let ((n (parse-integer name :start start :junk-allowed t)))
    (and (integerp n) n)))

(defun bump-fresh-counter-for (f)
  (dolist (s (remove-duplicates (all-symbols f)))
    (let ((name (symbol-name s)))
      (cond
        ((and (>= (length name) 2) (char= (char name 0) #\V))
         (let ((n (parse-trailing-nat name 1)))
           (when (and n (>= n *fresh-counter*))
             (setf *fresh-counter* (1+ n)))))
        ((and (>= (length name) 3)
              (char= (char name 0) #\S) (char= (char name 1) #\K))
         (let ((n (parse-trailing-nat name 2)))
           (when (and n (>= n *fresh-counter*))
             (setf *fresh-counter* (1+ n)))))))))

;; Substitution of variables by terms.  Respects quantifier shadowing
;; -------------------------------------------------------------------------

(defun fo-subst (f subst)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f)
     (let ((p (assoc f subst :test #'equal)))
       (if p (cdr p) f)))
    ((constant-symbolp f) f)
    ((constant-objectp f) f)
    ((quotep f) f)
    ((atom f) f)
    ((in (car f) *fo-quantifiers*)
     (let* ((vars (q-vars (cadr f)))
            (sub2 (remove-if (lambda (p) (in (car p) vars)) subst)))
       (list (car f) (cadr f) (fo-subst (caddr f) sub2))))
    (t (cons (car f) (mapcar (lambda (x) (fo-subst x subst)) (cdr f))))))

;; Standardize bound variables apart
;; -------------------------------------------------------------------------

(defun standardize-vars (f subst)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f)
     (let ((p (assoc f subst :test #'equal)))
       (if p (cdr p) f)))
    ((constant-symbolp f) f)
    ((constant-objectp f) f)
    ((quotep f) f)
    ((atom f) f)
    ((in (car f) *fo-quantifiers*)
     (let* ((q (car f))
            (var-list (q-vars (cadr f)))
            (new-vars (mapcar (lambda (v) (declare (ignore v)) (fresh-var))
                              var-list))
            (sub2 (append (mapcar #'cons var-list new-vars) subst)))
       (list q new-vars (standardize-vars (caddr f) sub2))))
    (t (cons (car f) (mapcar (lambda (x) (standardize-vars x subst)) (cdr f))))))

;;Skolemize.  u-scope is the list of universals currently in scope.
;; Assumes all bound variables are already unique (standardized).
;; -------------------------------------------------------------------------

(defun skolemize (f u-scope)
  (cond
    ((booleanp f) f)
    ((variable-symbolp f) f)
    ((constant-symbolp f) f)
    ((constant-objectp f) f)
    ((quotep f) f)
    ((atom f) f)
    ((== (car f) 'forall)
     (let* ((vars (q-vars (cadr f)))
            (body (skolemize (caddr f) (append u-scope vars))))
       (list 'forall vars body)))
    ((== (car f) 'exists)
     (let* ((evars (q-vars (cadr f)))
            (body  (caddr f))
            (sk-body (skolem-evars evars body u-scope)))
       (skolemize sk-body u-scope)))
    (t (cons (car f) (mapcar (lambda (x) (skolemize x u-scope)) (cdr f))))))

(defun skolem-evars (evars body u-scope)
  ;; Process each existential variable; Skolem args = u-scope ∩ free(body).
  (if (endp evars)
      body
      (let* ((v    (car evars))
             (fv   (free-vars body))
             (args (remove-if-not (lambda (u) (in u fv)) u-scope))
             (sk   (fresh-skolem))
             (skt  (cons sk args))
             (body2 (fo-subst body (list (cons v skt)))))
        (skolem-evars (cdr evars) body2 u-scope))))

;; Prenex - pull universals to the front.
;; Returns (cons universal-var-list quantifier-free-matrix).
;; -------------------------------------------------------------------------

(defun prenex (f)
  (cond
    ((booleanp f) (cons nil f))
    ((variable-symbolp f) (cons nil f))
    ((constant-symbolp f) (cons nil f))
    ((constant-objectp f) (cons nil f))
    ((quotep f) (cons nil f))
    ((atom f) (cons nil f))
    ((== (car f) 'forall)
     (let* ((vars (q-vars (cadr f)))
            (rec  (prenex (caddr f))))
       (cons (append vars (car rec)) (cdr rec))))
    ((in (car f) '(and or))
     (let* ((parts (mapcar #'prenex (cdr f)))
            (vs    (reduce #'append (mapcar #'car parts) :initial-value nil))
            (ms    (mapcar #'cdr parts)))
       (cons vs (cons (car f) ms))))
    (t (cons nil f))))  ; literal

;; CNF conversion and simplification
;; -------------------------------------------------------------------------

(defun to-cnf-clauses (f)
  (cond
    ((== f t)   nil)            ; empty CNF
    ((== f nil) (list nil))     ; CNF with empty clause = false
    ((and (consp f) (== (car f) 'and))
     (reduce #'append (mapcar #'to-cnf-clauses (cdr f)) :initial-value nil))
    ((and (consp f) (== (car f) 'or))
     (distribute-or-cnf (mapcar #'to-cnf-clauses (cdr f))))
    (t (list (list f)))))       ; literal

(defun distribute-pair (a b)
  ;; a, b are CNFs.  Cross-product of clauses, unioned and deduped.
  (reduce #'append
          (mapcar (lambda (c1)
                    (mapcar (lambda (c2) (remove-dups (append c1 c2))) b))
                  a)
          :initial-value nil))

(defun distribute-or-cnf (cnfs)
  (cond ((endp cnfs) (list nil))
        ((endp (cdr cnfs)) (car cnfs))
        (t (distribute-pair (car cnfs) (distribute-or-cnf (cdr cnfs))))))

(defun tautology-clause-p (lits)
  (some (lambda (l) (member (negate-lit l) lits :test #'equal)) lits))

(defun clause-set-equal (c1 c2)
  (and (subsetp c1 c2 :test #'equal)
       (subsetp c2 c1 :test #'equal)))

(defun strictly-subsumed-p (c all)
  ;; Strict: some OTHER clause c2 with c2 ⊂ c (proper subset).
  (some (lambda (c2)
          (and (not (clause-set-equal c c2))
               (subsetp c2 c :test #'equal)))
        all))

(defun simplify-cnf (clauses)
  (let* ((cs (mapcar #'remove-dups clauses))
         (cs (remove-if #'tautology-clause-p cs))
         (cs (remove-duplicates cs :test #'clause-set-equal :from-end t))
         (cs (remove-if (lambda (c) (strictly-subsumed-p c cs)) cs)))
    cs))

(defun clause-to-formula (lits)
  (cond ((endp lits) nil)
        ((endp (cdr lits)) (car lits))
        (t (cons 'or lits))))

(defun cnf-to-formula (clauses)
  (cond ((endp clauses) t)
        ((some #'endp clauses) nil)
        ((endp (cdr clauses)) (clause-to-formula (car clauses)))
        (t (cons 'and (mapcar #'clause-to-formula clauses)))))

;; Main entry point
;; -------------------------------------------------------------------------

(defun simp-skolem-pnf-cnf (f)
  (reset-fresh-counter)
  (bump-fresh-counter-for f)
  (let* ((f1    (fo-simplify f))
         (f2    (nnf f1))
         (f3    (standardize-vars f2 nil))
         (f4    (skolemize f3 nil))
         (pn    (prenex f4))
         (uvs   (car pn))
         (mtx   (cdr pn))
         (cls   (simplify-cnf (to-cnf-clauses mtx)))
         (mf    (cnf-to-formula cls))
         (used  (free-vars mf))
         (kept  (remove-if-not (lambda (v) (in v used)) uvs)))
    (if (null kept) mf (list 'forall kept mf))))


(defun test-sspc (name input expected)
  (let ((actual (simp-skolem-pnf-cnf input)))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a~%" name))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name input expected actual)))))

(defun run-sspc-tests ()
  (setf *test-passes* 0)
  (setf *test-fails*  0)

  ;; 1. Pure propositional passes through
  (test-sspc "1 atom" '(p x y) '(p x y))
  (test-sspc "2 boolean t" t t)
  (test-sspc "3 already CNF"
             '(and (or (p) (q)) (or (r) (s)))
             '(and (or (p) (q)) (or (r) (s))))

  ;; 4-6. Basic quantifier handling
  (test-sspc "4 simple forall"
             '(forall x (p x))
             '(forall (v1) (p v1)))
  (test-sspc "5 simple exists -> 0-ary skolem"
             '(exists x (p x))
             '(p (sk2)))
  (test-sspc "6 forall-exists -> skolem fn of one arg"
             '(forall x (exists y (p x y)))
             '(forall (v1) (p v1 (sk3 v1))))

  ;; 7. exists-forall: exists doesn't need arg since u-scope is empty
  (test-sspc "7 exists-forall"
             '(exists x (forall y (p x y)))
             '(forall (v2) (p (sk3) v2)))

  ;; 8. implies elimination via NNF
  (test-sspc "8 implies" 
             '(implies (p x) (q x))
             '(or (not (p x)) (q x)))

  ;; 9. iff produces 2-clause CNF
  (test-sspc "9 iff"
             '(iff (p) (q))
             '(and (or (not (p)) (q)) (or (p) (not (q)))))

  ;; 10. Negated universal -> existential -> skolem
  (test-sspc "10 not forall"
             '(not (forall x (p x)))
             '(not (p (sk2))))

  ;; 11. forall (implies P exists Q) - classic homework shape
  (test-sspc "11 forall(implies P (exists Q))"
             '(forall x (implies (p x) (exists y (q x y))))
             '(forall (v1) (or (not (p v1)) (q v1 (sk3 v1)))))

  ;; 12. Two independent foralls get standardized apart then merged
  (test-sspc "12 merge parallel universals"
             '(and (forall x (p x)) (forall x (q x)))
             '(forall (v1 v2) (and (p v1) (q v2))))

  ;; 13. Skolem arity minimization: y doesn't appear free in (p x),
  ;;     so the skolem for z only needs x and doesn't pick up y.
  (test-sspc "13 skolem arity minimization"
             '(forall x (forall y (exists z (q x z))))
             '(forall (v1) (q v1 (sk3 v1))))


  ;; 14. Disjunction of mixed quantifiers
  (test-sspc "14 disjunction of quantifiers"
             '(or (forall x (p x)) (exists y (q y)))
             '(forall (v1) (or (p v1) (q (sk3)))))

  ;; 15. Nested CNF distribution
  (test-sspc "15 distributivity"
             '(or (and (p) (q)) (r))
             '(and (or (p) (r)) (or (q) (r))))

  ;; 16. Barb-like: exists x forall y. iff
  (test-sspc "16 barb-shape"
             '(exists x (forall y (iff (p x y) (not (p y y)))))
             '(forall (v2)
                (and (or (not (p (sk3) v2)) (not (p v2 v2)))
                     (or (p (sk3) v2) (p v2 v2)))))

  ;; 17. if-then-else NNF-expanded and CNF-flattened
  (test-sspc "17 if expansion"
             '(if (c) (a) (b))
             '(and (or (c) (b)) (or (a) (not (c))) (or (a) (b))))

  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))

#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#
(defun apply-subst-term (tm subst)
  (cond
    ((variable-symbolp tm)
     (let ((p (assoc tm subst :test #'equal)))
       (if p (cdr p) tm)))
    ((constant-symbolp tm) tm)
    ((constant-objectp tm) tm)
    ((quotep tm) tm)
    ((atom tm) tm)
    ((consp tm)
     (cons (car tm)
           (mapcar (lambda (x) (apply-subst-term x subst)) (cdr tm))))
    (t tm)))

(defun occurs-in (v tm)
  (cond
    ((equal v tm) t)
    ((variable-symbolp tm) nil)
    ((constant-symbolp tm) nil)
    ((constant-objectp tm) nil)
    ((quotep tm) nil)           ; do NOT descend into quoted data
    ((atom tm) nil)
    ((consp tm) (some (lambda (x) (occurs-in v x)) (cdr tm)))
    (t nil)))

(defun extend-subst (v tm subst)
  ;; Add (v . tm), then push v->tm through every existing rhs to
  ;; maintain idempotence (no var in dom(subst) appears in any rhs).
  (let ((one (list (cons v tm))))
    (cons (cons v tm)
          (mapcar (lambda (p)
                    (cons (car p) (apply-subst-term (cdr p) one)))
                  subst))))

(defun unify-aux (eqs subst)
  (cond
    ((endp eqs) subst)
    (t
     (let* ((eq   (car eqs))
            (s    (apply-subst-term (car eq) subst))
            (tm   (apply-subst-term (cdr eq) subst))
            (rest (cdr eqs)))
       (cond
         ((equal s tm) (unify-aux rest subst))
         ((variable-symbolp s)
          (if (occurs-in s tm)
              'fail
              (unify-aux rest (extend-subst s tm subst))))
         ((variable-symbolp tm)
          (if (occurs-in tm s)
              'fail
              (unify-aux rest (extend-subst tm s subst))))
         ;; Two compound terms: both must be function apps (not quoted),
         ;; with matching head and matching arity.
         ((and (consp s) (not (quotep s))
               (consp tm) (not (quotep tm))
               (equal (car s) (car tm))
               (== (len (cdr s)) (len (cdr tm))))
          (unify-aux (append (mapcar #'cons (cdr s) (cdr tm)) rest)
                     subst))
         (t 'fail))))))

(defun unify (l)
  ;; Input: non-empty list of cons-pairs (s . t).
  ;; Output: an MGU (list of (var . term) with unique cars) or 'fail.
  (unify-aux l nil))


(defun test-unify (name input expected)
  (let ((actual (unify input)))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a~%" name))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name input expected actual)))))

(defun run-unify-tests ()
  (setf *test-passes* 0)
  (setf *test-fails*  0)

  ;; Trivial / orientation
  (test-unify "1 x = x"         '((x . x))     nil)
  (test-unify "2 var = const"   '((x . c1))    '((x . c1)))
  (test-unify "3 const = var"   '((c1 . x))    '((x . c1)))
  (test-unify "4 var = var"     '((x . y))     '((x . y)))
  (test-unify "5 const != const"'((c1 . c2))   'fail)

  ;; Function applications
  (test-unify "6 f(x) = f(c1)"     '(((f x) . (f c1)))   '((x . c1)))
  (test-unify "7 diff heads"       '(((f x) . (g x)))    'fail)
  (test-unify "8 arity mismatch"   '(((f x) . (f x y)))  'fail)

  ;; Occurs check
  (test-unify "9 x = f(x)"         '((x . (f x)))        'fail)
  (test-unify "10 x = f(g(x))"     '((x . (f (g x))))    'fail)

  ;; Composition / cascade
  (test-unify "11 chain x=y, y=c1"
              '((x . y) (y . c1))
              '((y . c1) (x . c1)))
  (test-unify "12 cascade into existing rhs"
              '((x . (f y z)) (y . c1) (z . c2))
              '((z . c2) (y . c1) (x . (f c1 c2))))
  (test-unify "13 aliasing then const"
              '((x . y) (x . c1))
              '((y . c1) (x . c1)))

  ;; Shared/repeated variables
  (test-unify "14 p(x,x) = p(y,c1)"
              '(((p x x) . (p y c1)))
              '((y . c1) (x . c1)))
  (test-unify "15 f(x,y) = f(y,x) via aliasing"
              '(((f x y) . (f y x)))
              '((x . y)))

  ;; Nested structure
  (test-unify "16 deep nested"
              '(((f (g x) y) . (f (g c1) (h c2))))
              '((y . (h c2)) (x . c1)))
  (test-unify "17 constant leaf inside fn app"
              '(((f c1 x) . (f c1 c2)))
              '((x . c2)))

  ;; Multiple independent equations
  (test-unify "18 two independent bindings"
              '((x . c1) (y . c2))
              '((y . c2) (x . c1)))

  ;; Quoted data is not a function app
  (test-unify "19 var = quoted"
              '((x . '1))
              '((x . '1)))
  (test-unify "20 quoted != quoted"
              '(('1 . '2))
              'fail)

  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))
#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#
;; Clause data structure: (:pos <atoms> :neg <atoms>)
;; -------------------------------------------------------------------------

(defun make-clause (pos neg)
  (list :pos pos :neg neg))

(defun clause-pos (c) (getf c :pos))
(defun clause-neg (c) (getf c :neg))

(defun clause-empty-p (c)
  (and (endp (clause-pos c)) (endp (clause-neg c))))

(defun clause-positive-p (c)
  (endp (clause-neg c)))

(defun clause-tautology-p (c)
  (some (lambda (a) (member a (clause-neg c) :test #'equal))
        (clause-pos c)))

(defun clause-literal-count (c)
  (+ (len (clause-pos c)) (len (clause-neg c))))

;; Clausification: full formula -> list of clauses
;; -------------------------------------------------------------------------

(defun split-literal (lit)
  ;; Returns (values atom sign) where sign is :pos or :neg.
  (if (and (consp lit) (== (car lit) 'not))
      (values (cadr lit) :neg)
      (values lit :pos)))

(defun literals-to-clause (lits)
  (let ((pos nil) (neg nil))
    (dolist (l lits)
      (multiple-value-bind (atom sign) (split-literal l)
        (if (eq sign :pos) (push atom pos) (push atom neg))))
    (make-clause (nreverse pos) (nreverse neg))))

(defun clausify-matrix (mtx)
  ;; mtx is quantifier-free CNF: literal | (or lit ...) | (and c1 c2 ...).
  (cond
    ((== mtx t) nil)                                  ; tautological CNF
    ((== mtx nil) (list (make-clause nil nil)))       ; empty clause
    ((and (consp mtx) (== (car mtx) 'and))
     (reduce #'append (mapcar #'clausify-matrix (cdr mtx))
             :initial-value nil))
    ((and (consp mtx) (== (car mtx) 'or))
     (list (literals-to-clause (cdr mtx))))
    (t (list (literals-to-clause (list mtx))))))      ; single literal

(defun formula-to-clauses (f)
  ;; Full pipeline: simp+skolem+pnf+cnf, then extract clause list.
  (let* ((skn (simp-skolem-pnf-cnf f))
         (mtx (if (and (consp skn) (== (car skn) 'forall))
                  (caddr skn)
                  skn)))
    (remove-if #'clause-tautology-p (clausify-matrix mtx))))

;; Variable renaming for fresh clause copies
;; -------------------------------------------------------------------------

(defun collect-vars (tm acc)
  (cond
    ((variable-symbolp tm)
     (if (member tm acc :test #'equal) acc (cons tm acc)))
    ((atom tm) acc)
    ((quotep tm) acc)
    ((consp tm)
     (let ((a acc))
       (dolist (x (cdr tm))
         (setf a (collect-vars x a)))
       a))
    (t acc)))

(defun clause-vars (c)
  (let ((acc nil))
    (dolist (a (clause-pos c)) (setf acc (collect-vars a acc)))
    (dolist (a (clause-neg c)) (setf acc (collect-vars a acc)))
    acc))

(defun rename-clause (c)
  ;; Every variable in c -> fresh V<n>.
  (let* ((vs    (clause-vars c))
         (subst (mapcar (lambda (v) (cons v (fresh-var))) vs)))
    (make-clause
     (mapcar (lambda (a) (apply-subst-term a subst)) (clause-pos c))
     (mapcar (lambda (a) (apply-subst-term a subst)) (clause-neg c)))))

;; Applying a substitution to a clause
;; -------------------------------------------------------------------------

(defun apply-subst-clause (c subst)
  (make-clause
   (mapcar (lambda (a) (apply-subst-term a subst)) (clause-pos c))
   (mapcar (lambda (a) (apply-subst-term a subst)) (clause-neg c))))

(defun dedup-atoms (atoms)
  (remove-duplicates atoms :test #'equal :from-end t))

(defun normalize-clause (c)
  (make-clause (dedup-atoms (clause-pos c))
               (dedup-atoms (clause-neg c))))

;; Positive resolution
;; -------------------------------------------------------------------------

(defun resolve-on (pos-parent mix-parent l1 l2)
  ;; Try unifying l1 (pos lit of pos-parent) with l2 (neg lit of mix-parent).
  (let ((mgu (unify (list (cons l1 l2)))))
    (cond ((equal mgu 'fail) nil)
          (t
           (let* ((new-pos (append (remove l1 (clause-pos pos-parent)
                                           :test #'equal :count 1)
                                   (clause-pos mix-parent)))
                  (new-neg (remove l2 (clause-neg mix-parent)
                                   :test #'equal :count 1))
                  (resolvent (make-clause new-pos new-neg))
                  (applied   (apply-subst-clause resolvent mgu))
                  (norm      (normalize-clause applied)))
             (if (clause-tautology-p norm) nil (list norm)))))))

(defun positive-resolvents-oriented (pos-parent mix-parent)
  ;; pos-parent assumed positive.  Resolve each L1 in pos against each L2
  ;; in mix's neg.  Renaming of both clauses is the caller's responsibility.
  (let ((out nil))
    (dolist (l1 (clause-pos pos-parent))
      (dolist (l2 (clause-neg mix-parent))
        (dolist (r (resolve-on pos-parent mix-parent l1 l2))
          (push r out))))
    out))

(defun positive-resolvents (c1 c2)
  ;; Rename both, then orient: whichever side is all-positive is pos-parent.
  ;; If both are positive, no resolution possible (no neg lits on either side).
  ;; If neither is positive, positive resolution does not apply.
  (let ((r1 (rename-clause c1))
        (r2 (rename-clause c2)))
    (cond
      ((and (clause-positive-p r1) (not (clause-positive-p r2)))
       (positive-resolvents-oriented r1 r2))
      ((and (clause-positive-p r2) (not (clause-positive-p r1)))
       (positive-resolvents-oriented r2 r1))
      (t nil))))

;; Factoring
;; -------------------------------------------------------------------------

(defun factor-same-sign (atoms sign-accessor other-accessor c)
  (let ((out nil)
        (atoms (funcall sign-accessor c))
        (other (funcall other-accessor c)))
    (declare (ignore atoms))
    (let ((lits (funcall sign-accessor c)))
      (loop for tail on lits do
        (loop for l2 in (cdr tail) do
          (let* ((l1 (car tail))
                 (mgu (unify (list (cons l1 l2)))))
            (unless (equal mgu 'fail)
              (let* ((new-this (remove l2 lits :test #'equal :count 1))
                     (cl (if (eq sign-accessor #'clause-pos)
                             (make-clause new-this other)
                             (make-clause other new-this)))
                     (applied (apply-subst-clause cl mgu))
                     (norm    (normalize-clause applied)))
                (unless (clause-tautology-p norm)
                  (push norm out))))))))
    out))

(defun factors (c)
  ;; All single-step factors of c (positive or negative side).
  (let ((rc (rename-clause c)))
    (append
     (factor-same-sign nil #'clause-pos #'clause-neg rc)
     (factor-same-sign nil #'clause-neg #'clause-pos rc))))

;; Matching: one-way substitution
;; -------------------------------------------------------------------------

(defun match-term (pat tm subst)
  (cond
    ((variable-symbolp pat)
     (let ((p (assoc pat subst :test #'equal)))
       (cond (p (if (equal (cdr p) tm) subst 'fail))
             (t (cons (cons pat tm) subst)))))
    ((variable-symbolp tm) 'fail)     ; pattern is not a var, but tm is
    ((or (constant-symbolp pat) (constant-objectp pat) (quotep pat))
     (if (equal pat tm) subst 'fail))
    ((or (constant-symbolp tm) (constant-objectp tm) (quotep tm))
     'fail)
    ((atom pat) (if (equal pat tm) subst 'fail))
    ((atom tm) 'fail)
    ((and (consp pat) (consp tm)
          (equal (car pat) (car tm))
          (== (len (cdr pat)) (len (cdr tm))))
     (match-terms (cdr pat) (cdr tm) subst))
    (t 'fail)))

(defun match-terms (ps ts subst)
  (cond
    ((endp ps) subst)
    (t (let ((s (match-term (car ps) (car ts) subst)))
         (if (equal s 'fail) 'fail
             (match-terms (cdr ps) (cdr ts) s))))))

;; Clause subsumption
;; -------------------------------------------------------------------------

(defun match-literals-backtrack (c1-lits c2-lits subst)
  ;; c1-lits: list of atoms from one sign side of C1.
  ;; c2-lits: list of atoms from same sign side of C2.
  ;; Returns extended subst or 'fail.
  (cond
    ((endp c1-lits) subst)
    (t
     (let ((l1 (car c1-lits))
           (rest (cdr c1-lits))
           (result 'fail))
       (dolist (l2 c2-lits)
         (when (equal result 'fail)
           (let ((s2 (match-term l1 l2 subst)))
             (unless (equal s2 'fail)
               (let ((r (match-literals-backtrack rest c2-lits s2)))
                 (unless (equal r 'fail)
                   (setf result r)))))))
       result))))

(defun subsumes-p (c1 c2)
  ;; Does C1 subsume C2?  Match each pos of C1 against some pos of C2,
  ;; then each neg of C1 against some neg of C2, under one shared sigma.
  (let ((s1 (match-literals-backtrack (clause-pos c1) (clause-pos c2) nil)))
    (cond ((equal s1 'fail) nil)
          (t (let ((s2 (match-literals-backtrack (clause-neg c1)
                                                 (clause-neg c2) s1)))
               (not (equal s2 'fail)))))))

;; Replacement
;; -------------------------------------------------------------------------

(defun any-subsumes (c clauses)
  (some (lambda (c2) (subsumes-p c2 c)) clauses))

(defun remove-subsumed-by (c clauses)
  (remove-if (lambda (c2) (subsumes-p c c2)) clauses))

(defun add-clause-with-replacement (c clauses)
  ;; Return updated clause list, or the symbol :redundant if c is
  ;; subsumed by something already present.
  (cond
    ((clause-tautology-p c) :redundant)
    ((any-subsumes c clauses) :redundant)
    (t (cons c (remove-subsumed-by c clauses)))))

;; Saturation loop
;; -------------------------------------------------------------------------

(defparameter *fo-val-iter-cap* 2000
  "Max given-clause iterations before giving up.")

(defun saturate (initial-clauses)
  ;; Returns 'valid if empty clause derived (i.e., input UNSAT),
  ;; 'unknown if iteration cap hit, 'saturated if closed off cleanly.
  (let ((processed nil)
        (unprocessed nil))
    ;; Seed unprocessed with initial clauses, applying replacement.
    (dolist (c initial-clauses)
      (let ((r (add-clause-with-replacement c unprocessed)))
        (unless (eq r :redundant) (setf unprocessed r))))
    ;; Early empty-clause check
    (when (some #'clause-empty-p unprocessed)
      (return-from saturate 'valid))
    (loop for iter from 0 below *fo-val-iter-cap* do
      (when (endp unprocessed)
        (return-from saturate 'saturated))
      (let* ((given (car unprocessed))
             (rest  (cdr unprocessed)))
        (setf unprocessed rest)
        ;; Check given against processed via forward subsumption.
        (cond
          ((any-subsumes given processed)
           nil)  ; discard; iterate
          (t
           ;; Remove any processed clauses subsumed by given.
           (setf processed (remove-subsumed-by given processed))
           ;; Generate new clauses: resolvents and factors.
           (let ((new-clauses nil))
             ;; Factors of given
             (dolist (f (factors given))
               (push f new-clauses))
             ;; Resolvents of given against each processed clause
             (dolist (p processed)
               (dolist (r (positive-resolvents given p))
                 (push r new-clauses)))
             ;; Insert given into processed
             (push given processed)
             ;; Integrate new clauses
             (dolist (nc new-clauses)
               (when (clause-empty-p nc)
                 (return-from saturate 'valid))
               (let ((r1 (add-clause-with-replacement nc processed)))
                 (unless (eq r1 :redundant)
                   (setf processed r1)
                   (let ((r2 (add-clause-with-replacement nc unprocessed)))
                     (unless (eq r2 :redundant)
                       (setf unprocessed r2)))))))))))
    'unknown))

;; Main entry point
;; -------------------------------------------------------------------------

(defun fo-no=-val (f)
  ;; A formula F is valid iff (not F) is unsat.
  ;; Clausify (not F), saturate, return 'valid on empty clause.
  (reset-fresh-counter)
  (let* ((neg     (list 'not f))
         (clauses (formula-to-clauses neg))
         (result  (saturate clauses)))
    (if (eq result 'valid) 'valid result)))


(defun clause-equiv-p (c1 c2)
  ;; Syntactic equivalence up to literal ordering.
  (and (null (set-difference (clause-pos c1) (clause-pos c2) :test #'equal))
       (null (set-difference (clause-pos c2) (clause-pos c1) :test #'equal))
       (null (set-difference (clause-neg c1) (clause-neg c2) :test #'equal))
       (null (set-difference (clause-neg c2) (clause-neg c1) :test #'equal))))

(defun clause-set-has-p (c cs)
  (some (lambda (c2) (clause-equiv-p c c2)) cs))

(defun test-q5p1 (name actual-bool)
  (cond (actual-bool
         (incf *test-passes*)
         (format t "PASS ~a~%" name))
        (t
         (incf *test-fails*)
         (format t "FAIL ~a~%" name))))

(defun run-q5p1-tests ()
  (setf *test-passes* 0)
  (setf *test-fails*  0)

  ;; Clausification
  (let ((cs (formula-to-clauses '(or (p x) (not (q x))))))
    (test-q5p1 "clausify: single disjunction"
               (and (== (len cs) 1)
                    (clause-equiv-p (first cs)
                                    (make-clause '((p x)) '((q x)))))))

  (let ((cs (formula-to-clauses '(and (or (p) (q)) (or (r) (not (s)))))))
    (test-q5p1 "clausify: conjunction of disjunctions"
               (and (== (len cs) 2)
                    (clause-set-has-p (make-clause '((p) (q)) nil) cs)
                    (clause-set-has-p (make-clause '((r)) '((s))) cs))))

  ;; Tautology pruning at clausification time
  (let ((cs (formula-to-clauses '(or (p x) (not (p x)) (q)))))
    (test-q5p1 "clausify: tautology dropped"
               (endp cs)))

  ;; Rename uses fresh vars
  (reset-fresh-counter)
  (let* ((c  (make-clause '((p x) (q x y)) '((r y))))
         (r1 (rename-clause c))
         (r2 (rename-clause c)))
    (test-q5p1 "rename: distinct vars across calls"
               (null (intersection (clause-vars r1) (clause-vars r2)
                                   :test #'equal))))

  ;; Propositional resolution
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p)) nil))              ; p
         (c2 (make-clause '((q)) '((p))))           ; p -> q
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: modus ponens"
               (and (== (len rs) 1)
                    (clause-equiv-p (first rs) (make-clause '((q)) nil)))))

  ;; First-order resolution with substitution
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p x)) nil))            ; forall x. p(x)
         (c2 (make-clause '((q y)) '((p y))))       ; forall y. p(y) -> q(y)
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: FO with unification"
               (and (== (len rs) 1)
                    ;; resolvent should be q(<some var>)
                    (endp (clause-neg (first rs)))
                    (== (len (clause-pos (first rs))) 1)
                    (equal (car (car (clause-pos (first rs)))) 'q))))

  ;; Unit resolution to empty clause
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p (a))) nil))          ; p(a)
         (c2 (make-clause nil '((p x))))            ; not p(x)
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: derives empty clause"
               (and (== (len rs) 1)
                    (clause-empty-p (first rs)))))

  ;; No positive parent -> no resolvent under positive resolution
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p)) '((q))))
         (c2 (make-clause '((r)) '((p))))
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: neither parent positive -> none"
               (endp rs)))

  ;; Positive resolution requires unifiability
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p (a))) nil))
         (c2 (make-clause '((q)) '((p (b)))))
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: unify failure -> none"
               (endp rs)))

  ;; Multiple resolvents from multiple unifying pairs
  (reset-fresh-counter)
  (let* ((c1 (make-clause '((p x) (q y)) nil))
         (c2 (make-clause '((r)) '((p (a)) (q (b)))))
         (rs (positive-resolvents c1 c2)))
    (test-q5p1 "resolve: multiple resolvents"
               (== (len rs) 2)))

  ;; Factoring
  (reset-fresh-counter)
  (let* ((c  (make-clause '((p x) (p (a))) nil))
         (fs (factors c)))
    (test-q5p1 "factor: p(x) v p(a) -> p(a)"
               (and (>= (len fs) 1)
                    (some (lambda (f)
                            (and (endp (clause-neg f))
                                 (== (len (clause-pos f)) 1)))
                          fs))))

  ;; No factor when no same-sign unifying pair
  (reset-fresh-counter)
  (let* ((c  (make-clause '((p (a)) (p (b))) nil))
         (fs (factors c)))
    (test-q5p1 "factor: distinct ground atoms -> none"
               (endp fs)))

  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))

;; Q5 Part 2 tests:
;; =========================================================================

(defun test-val (name input expected)
  (let ((actual (fo-no=-val input)))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a   [~a]~%" name actual))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name input expected actual)))))

(defun test-val-timed (name input expected)
  ;; Like test-val but reports wall-clock time for the run.
  (let* ((t0 (get-internal-real-time))
         (actual (fo-no=-val input))
         (t1 (get-internal-real-time))
         (ms (round (* 1000 (/ (- t1 t0)
                               internal-time-units-per-second)))))
    (cond ((equal actual expected)
           (incf *test-passes*)
           (format t "PASS ~a   [~a, ~a ms]~%" name actual ms))
          (t
           (incf *test-fails*)
           (format t "FAIL ~a   [~a ms]~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                   name ms input expected actual)))))

;; textbook formulas (from p.178-198 of the Handbook)
;; -------------------------------------------------------------------------

(defparameter *p34*
  '(iff
    (iff (exists x (forall y (iff (p x) (p y))))
         (iff (exists x (q x)) (forall y (q y))))
    (iff (exists x (forall y (iff (q x) (q y))))
         (iff (exists x (p x)) (forall y (p y))))))

(defparameter *p38*
  '(iff
    (forall x
     (implies
      (and (p (a))
           (implies (p x) (exists y (and (p y) (r x y)))))
      (exists (z w) (and (p z) (r x w) (r w z)))))
    (forall x
     (and
      (or (not (p (a))) (p x)
          (exists (z w) (and (p z) (r x w) (r w z))))
      (or (not (p (a)))
          (not (exists y (and (p y) (r x y))))
          (exists (z w) (and (p z) (r x w) (r w z))))))))

(defparameter *ewd1062*
  '(implies
    (and (forall x (le x x))
         (forall (x y z) (implies (and (le x y) (le y z)) (le x z)))
         (forall (x y) (iff (le (f x) y) (le x (g y)))))
    (and (forall (x y) (implies (le x y) (le (f x) (f y))))
         (forall (x y) (implies (le x y) (le (g x) (g y)))))))

(defparameter *los*
  '(implies
    (and (forall (x y z) (implies (and (p x y) (p y z)) (p x z)))
         (forall (x y z) (implies (and (q x y) (q y z)) (q x z)))
         (forall (x y) (implies (q x y) (q y x)))
         (forall (x y) (or (p x y) (q x y))))
    (or (forall (x y) (p x y))
        (forall (x y) (q x y)))))

;; tests: propositional and simple FO validities/non-validities.
;; -------------------------------------------------------------------------

(defun run-val-tests ()
  (setf *test-passes* 0)
  (setf *test-fails*  0)

  ;; Propositional validities
  (test-val "1 p or not p"
            '(or (p) (not (p))) 'valid)
  (test-val "2 contrapositive"
            '(implies (implies (p) (q))
                      (implies (not (q)) (not (p))))
            'valid)
  (test-val "3 hypothetical syllogism"
            '(implies (and (implies (p) (q)) (implies (q) (r)))
                      (implies (p) (r)))
            'valid)

  (test-val "4 p does not imply q"
            '(implies (p) (q)) 'saturated)

  ;; First-order validities
  (test-val "5 forall instantiation"
            '(implies (forall x (p x)) (p (a)))
            'valid)
  (test-val "6 exists introduction"
            '(implies (p (a)) (exists x (p x)))
            'valid)
  (test-val "7 forall chain (modus ponens under forall)"
            '(implies (and (forall x (implies (p x) (q x)))
                           (forall x (p x)))
                      (forall x (q x)))
            'valid)
  (test-val "8 quantifier swap (valid direction)"
            '(implies (exists x (forall y (p x y)))
                      (forall y (exists x (p x y))))
            'valid)

  ;; Drinker's paradox
  (test-val "9 drinker's paradox"
            '(exists x (implies (p x) (forall y (p y))))
            'valid)

  ;; Barber of Seville (L19 slide barb formula).
  (test-val "10 barber - no such barber"
            '(not (exists v (forall x (iff (shaves v x)
                                           (not (shaves x x))))))
            'valid)

  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))

;; Textbook tests: Harrison p34/p38/ewd1062/Los.
;; -------------------------------------------------------------------------

(defun run-textbook-tests ()
  (setf *test-passes* 0)
  (setf *test-fails*  0)
  (let ((*fo-val-iter-cap* 20000))
    (test-val-timed "Los (presolution in Harrison)" *los*     'valid)
    (test-val-timed "ewd1062"                       *ewd1062* 'valid)
    (test-val-timed "p38"                           *p38*     'valid)
    (test-val-timed "p34 (Andrews' Challenge)"      *p34*     'valid))
  (format t "~%-----~%~a passed, ~a failed~%" *test-passes* *test-fails*))


(defun run-all-val-tests ()
  (format t "~%=== Core tests ===~%")
  (run-val-tests)
  (format t "~%=== Textbook tests ===~%")
  (run-textbook-tests))


#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

(defun fo-val (f) ...)
