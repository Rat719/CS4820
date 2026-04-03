;;;; CS 4820 — HW5 Grading Rubric
;;;; Load after student's file (in package :tp)
;;;;
;;;; POINTS: Q1=25  Q2=20  Q3=30  Q4 Part1=25  Q4 Part2=30  EC1=20  EC2=20
;;;; DEDUCTIONS: <10 tests/section −3 | no assert-acl2s-equal −3 | no verify-sat −2

(in-package :tp)

(defmacro check (label form)
  `(handler-case (progn ,form (format t "~&[PASS] ~a~%" ,label))
     (error (e) (format t "~&[FAIL] ~a — ~a~%" ,label e))))

(defmacro check-sat (label f)
  `(check ,label
     (multiple-value-bind (r a) (dp ,f)
       (assert (== r 'sat))
       (assert (verify-sat ,f a)))))

(defmacro check-unsat (label f)
  `(check ,label (assert (== (dp ,f) 'unsat))))

(defmacro check-dpll-sat (label f)
  `(check ,label
     (multiple-value-bind (r a) (dpll ,f)
       (assert (== r 'sat))
       (assert (verify-sat ,f a)))))

(defmacro check-dpll-unsat (label f)
  `(check ,label (assert (== (dpll ,f) 'unsat))))

;;;; ── Q1: p-simplify (25 pts) ────────────────────────────────────────────

(format t "~%=== Q1 p-simplify ===~%")

(check "A1" (assert-acl2s-equal (p-simplify '(and p t q))     '(and p q)))
(check "A2" (assert-acl2s-equal (p-simplify '(or  p nil q))   '(or  p q)))
(check "A3" (assert-acl2s-equal (p-simplify '(and))           t))
(check "A4" (assert-acl2s-equal (p-simplify '(and p))         'p))
(check "A5" (assert-acl2s-equal (p-simplify '(and p t (foo t nil) q)) '(and p (foo t nil) q)))

(check "B1" (assert-acl2s-equal (p-simplify '(and p (and q r)))         '(and p q r)))
(check "B2" (assert-acl2s-equal (p-simplify '(or  p (or  q r)))         '(or  p q r)))
(check "B3" (assert-acl2s-equal (p-simplify '(and p (and q (and r s)))) '(and p q r s)))

(check "C1" (assert-acl2s-equal (p-simplify '(and p nil q)) nil))
(check "C2" (assert-acl2s-equal (p-simplify '(or  p t   q)) t))

(check "D1" (assert-acl2s-equal (p-simplify '(not (not p)))   'p))
(check "D2" (assert-acl2s-equal (p-simplify '(not (iff p q))) '(xor p q)))
(check "D3" (assert-acl2s-equal (p-simplify '(not (xor p q))) '(iff p q)))
(check "D4" (assert-acl2s-equal (p-simplify '(not (iff p t))) '(not p)))

(check "E1" (assert-acl2s-equal (p-simplify '(and (or p q) (or r q p) p)) 'p))
(check "E2" (assert-acl2s-equal (p-simplify '(and p (implies p q)))       '(and p q)))

(check "F1" (assert-acl2s-equal (p-simplify '(or  x (not x))) t))
(check "F2" (assert-acl2s-equal (p-simplify '(and x (not x))) nil))
(check "F3" (assert-acl2s-equal (p-simplify '(or (foo a b) z (not (foo a b)))) t))

;;;; ── Q2: tseitin (20 pts) ────────────────────────────────────────────────

(format t "~%=== Q2 tseitin ===~%")

(check "T1" (assert (cnfp (tseitin '(and p q)))))
(check "T2" (assert (cnfp (tseitin '(implies p q)))))
(check "T3" (assert (cnfp (tseitin '(iff p q)))))
(check "T4" (assert (cnfp (tseitin '(if p q r)))))
(check "T5" (assert (== (tseitin '(or  p (not p))) t)))
(check "T6" (assert (== (tseitin '(and p (not p))) '(and (or)))))
(check "T7"
  (let ((r (tseitin '(and (foo x) (bar y)))))
    (assert (cnfp r))
    (assert (some (lambda (c) (member '(foo x) (clause->lits c) :test #'equal))
                  (cnf->clauses r)))))
(check "T8"
  (multiple-value-bind (r _) (dp (tseitin '(and (or p q) (implies r s))))
    (assert (== r 'sat))))
(check "T9"
  (multiple-value-bind (r _) (dp (tseitin '(and p (not p))))
    (assert (== r 'unsat))))

;;;; ── Q3: DP (30 pts) ─────────────────────────────────────────────────────

(format t "~%=== Q3 DP ===~%")

(check-sat   "D1 simple SAT"    '(and (or p q)))
(check-unsat "D2 simple UNSAT"  '(and (or p) (or (not p))))
(check-sat   "D3 BCP chain"     '(and (or p) (or (not p) q) (or (not q) r)))
(check-unsat "D4 empty clause"  '(and (or)))
(check-sat   "D5 pure literal"  '(and (or p q) (or p r)))
(check-unsat "D6 3-var UNSAT"   '(and (or p q r) (or (not p) q r) (or p (not q) r)
                                      (or (not p) (not q) r) (or p q (not r))
                                      (or (not p) q (not r)) (or p (not q) (not r))
                                      (or (not p) (not q) (not r))))
(check-sat   "D7 4-var SAT"     '(and (or p q) (or (not p) r) (or (not r) s) (or (not s) q)))
(check "D8 assign valid"
  (multiple-value-bind (r a) (dp '(and (or p (not q)) (or (not p) r) (or q (not r))))
    (assert (== r 'sat))
    (assert (verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) a))))
(check-sat   "D9 compound atoms" '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))))
(check "D10 tseitin round-trip"
  (multiple-value-bind (r _) (dp (tseitin '(and (or p q) (or r s))))
    (assert (== r 'sat))))

;;;; ── Q4: DPLL (30 pts) ───────────────────────────────────────────────────

(format t "~%=== Q4 DPLL ===~%")

(check-dpll-sat   "L1 simple SAT"     '(and (or p q)))
(check-dpll-unsat "L2 empty clause"   '(and (or)))
(check-dpll-sat   "L3 BCP chain"      '(and (or p) (or (not p) q) (or (not q) r)))
(check-dpll-unsat "L4 BCP UNSAT"      '(and (or p) (or (not p))))
(check-dpll-unsat "L5 all-sign UNSAT" '(and (or a b) (or (not a) b)
                                            (or a (not b)) (or (not a) (not b))))
(check-dpll-sat   "L6 L10 slide"
  '(and (or a b) (or b c) (or (not b) c d)
        (or (not a) (not x) y) (or (not a) x z)
        (or (not a) (not y) z) (or (not a) x (not z))
        (or (not a) (not y) (not z))))
(check "L7 assign valid"
  (multiple-value-bind (r a) (dpll '(and (or p (not q)) (or (not p) r) (or q (not r))))
    (assert (== r 'sat))
    (assert (verify-sat '(and (or p (not q)) (or (not p) r) (or q (not r))) a))))
(check-dpll-unsat "L8 3-var UNSAT"
  '(and (or p q r) (or (not p) q r) (or p (not q) r) (or (not p) (not q) r)
        (or p q (not r)) (or (not p) q (not r)) (or p (not q) (not r))
        (or (not p) (not q) (not r))))
(check-dpll-sat   "L9 compound atoms" '(and (or (foo x) (bar y)) (or (not (foo x)) (baz z))))
(check "L10 tseitin round-trip"
  (multiple-value-bind (r _) (dpll (tseitin '(and (or p q) (implies r s))))
    (assert (== r 'sat))))

;;;; ── BENCHMARK EC1: DP (25 pts + 20 EC) ────────────────────────────────
;; Fixed instance — run on every submission, record time, fastest wins.
;; If it hangs (>60s), award correctness points only, no EC.

(format t "~%=== BENCHMARK EC1: DP ===~%")
(time (dp '(and (or p q r) (or (not p) q r) (or p (not q) r)
               (or (not p) (not q) r) (or p q (not r))
               (or (not p) q (not r)) (or p (not q) (not r))
               (or (not p) (not q) (not r)))))

;;;; ── BENCHMARK EC2: DPLL (30 pts + 20 EC) ──────────────────────────────
;; RCA vs CLA adder — always UNSAT. Compare at n=12; tie-break at n=16.
;; DP is not run here — it hangs on structured UNSAT instances.

(defun wire (prefix i) (intern (format nil "~a~a" prefix i)))

(defun make-rca (n)
  (cons 'and
        (loop for i below n
              for a = (wire 'A i) for b = (wire 'B i)
              for cin = (if (= i 0) nil (wire 'RC i))
              append `((iff ,(wire 'RS i) (xor ,a (xor ,b ,(or cin nil))))
                       ,@(when (< i (1- n))
                           `((iff ,(wire 'RC (1+ i))
                                  (or (and ,a ,b) (and ,cin (xor ,a ,b))))))))))

(defun make-cla (n)
  (cons 'and
        (loop for i below n
              for a = (wire 'A i) for b = (wire 'B i)
              for cc = (if (= i 0) nil (wire 'CC i))
              append `((iff ,(wire 'CG i) (and ,a ,b))
                       (iff ,(wire 'CP i) (xor ,a ,b))
                       (iff ,(wire 'CS i) (xor ,(wire 'CP i) ,(or cc nil)))
                       ,@(when (< i (1- n))
                           `((iff ,(wire 'CC (1+ i))
                                  (or ,(wire 'CG i) (and ,(wire 'CP i) ,cc)))))))))

(defun make-cec (n)
  `(and ,(make-rca n) ,(make-cla n)
        (or ,@(loop for i below n collect `(xor ,(wire 'RS i) ,(wire 'CS i))))))

(format t "~%=== BENCHMARK EC2: DPLL — RCA vs CLA (all UNSAT) ===~%")
(dolist (n '(4 8 12))
  (let ((cnf (tseitin (make-cec n))))
    (format t "~%-- ~a-bit --~%" n)
    (time (dpll cnf))))

#| Tie-break at n=16: (time (dpll (tseitin (make-cec 16)))) |#

;;;; ── Grading summary ─────────────────────────────────────────────────────
#|
 Student: ___________________________   Late? Y/N

 Q1  /25   A__/5  B__/5  C__/5  D__/5  E+F__/5
 Q2  /20   structure__/5  equi-sat__/8  compound__/4  trivial__/3
 Q3  /30   BCP__/8  pure__/5  resolution__/9  assign__/8
 Q4a /25   (profiled DP — meets efficiency criteria? Y/N)
 Q4b /30   BCP+trail__/10  1-UIP__/8  backjump+learn__/7  tests__/5
 EC1 /20   DP time: _____s     (fastest across class wins, DNF=no EC)
 EC2 /20   DPLL n=12: _____s   (fastest across class wins)

 Deductions: <10 tests__  no assert-acl2s-equal__  no verify-sat__

 TOTAL: ___/130   w/EC: ___/170
|#
