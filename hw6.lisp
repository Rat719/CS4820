#|

 Copyright © 2026 by Pete Manolios and Andrew Walter
 CS 4820 Spring 2026

 Homework 6
 Due: 3/28 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 6".

 The group members are:

 Wangyuan Zheng

|#

#|

 In this homework, you will learn how to use Z3, a modern
 SMT (satisfiability modulo theories) solver from inside of
 ACL2s. Andrew has developed API bindings that provide a (property
 ...)-like interface to Z3. There are Z3 bindings for most languages,
 including Python, OCaml, Haskell, etc.

 You'll develop a simple Sudoku solver using the Z3 bindings. You will
 also explore different ways of encoding problems and how that affects
 performance.

 SMT solvers combine SAT solvers with solvers for additional
 theories (for example, the theory of uninterpreted functions, or real
 arithmetic with addition and multiplication). In this way, SMT
 solvers can check the satisfiability of expressions that contain
 variables and functions from several different theories at once.

 Consider the following example:
 Let x and y be two strings. Is the following satisfiable?
 (^ (< (length x) 3)
    (< (length y) 3)
    (> (length (string-append x y)) 6))
 It is not - the length of (string-append x y) is at most (length x) + (length y).

 We can state this as an ACL2s property:
 (property (x :string y :string)
           (=> (^ (< (length x) 3)
                  (< (length y) 3))
               (not (> (length (string-append x y)) 6))))

 For an SMT solver to be able to report that this statement is UNSAT,
 it needs to understand how length and string-append relate to each
 other. If we ask our DP implementation from Homework 4 whether the
 propositional skeleton is satisfiable, it will report that it is SAT
 because it doesn't reason about length, <, >, string-append, etc.

 As you'll learn, we can ask Z3 to check the satisfiability of this
 statement using the following query (after setting up dependencies):

 (z3-assert (x :string y :string)
            (and (< (str.len x) 3)
                 (< (str.len y) 3)
                 (> (str.len (str.++ x y)) 6)))
 (check-sat)

 Z3 reports :UNSAT.

 Let's get started by first going through some setup instructions for
 the Z3-Lisp API.
|#

#|
=====================================
=            Z3 Setup               =
=====================================

You first need to install Z3 onto your system. Many package managers
offer a prepackaged version of Z3, so it is likely easiest to install
Z3 using your package manager rather than building it from source. If
you're on macOS, Homebrew provides prebuilt Z3 packages as well.

If using Windows Subsystem for Linux to run ACL2s, you should install
Z3 into WSL rather than in "regular" Windows.

Depending on your operating system, you may also need to install
a "z3-dev" package. On Ubuntu, this package is called `libz3-dev`.

You will also need a working C compiler to use the interface. On
Ubuntu, the `build-essential` package should include everything you
need, though it is fairly large and contains some unneeded
software. One could also try just installing `gcc` or `clang`.

After getting Z3 installed, you should be able to run it through the
command line. To test this, execute `z3 --version` in your terminal
and verify that it reports something along the lines of `Z3 version
4.15.4 - 64 bit` (your version or architecture may be different,
that's OK).

To install the z3 bindings, follow the instructions at
https://github.com/mister-walter/cl-z3.  If you run into any issues,
ask questions on Piazza.

|#

;; Exit out of ACL2s into raw Lisp
:q

(load "~/quicklisp/setup.lisp")
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :hwk6
  (:use :cl :z3))
(in-package :hwk6)

;; Before we do anything, we must start Z3.
(solver-init)

;; ===========================
;;           Basics
;; ===========================
;; To use Z3, one adds one or more assertions to Z3 and then uses
;; (check-sat) to ask Z3 to perform a satisfiability check.
;; Let's try something simple first.
;; We want to know if the formula `x ^ y` is satisfiable. Let's add it
;; to Z3's stack:
(z3-assert (x :bool y :bool)
           (and x y))
;; We can see the contents of the solver using print-solver.
;;(print-solver)

;; Now, we can ask Z3 to check satisfiability:
(check-sat)
(get-model-as-assignment)
;; We get an assignment: ((X T) (Y T)). This indicates that the set of
;; assertions we've added to Z3's stack is satisfiable, and provides a
;; satisfying assignment.

;; Note that Z3 still contains the stack of assertions; if we call
;; check-sat again, we'll get another satisfying assignment.
(check-sat)
(get-model-as-assignment)
;; In this case the satisfying assignment is the same (since there is
;; only one distinct satisfying assignment for the formula `x ^ y`),
;; but in general the assignment may be different.

;; To clear the set of assignments, we can use `(solver-reset)`.
(solver-reset)

;; =========================
;;    The Assertion Stack
;; =========================
;; Sometimes, it may be useful to be able to remove just a subset of
;; assertions instead of resetting all of them. Z3 supports this with
;; the concept of scopes.
;; When a scope `S` is created, Z3 saves the set of assertions that
;; exist at that time. When `S` is popped, Z3 will return its set of
;; assertions to its state at the time `S` was created.

;; Let's see an example.

;; Create an initial scope that we can return to when we want an empty
;; set of assertions
(solver-push)

(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; This is SAT.
(check-sat)
(get-model-as-assignment)

;; There is currently 1 assertion.
(print-solver)

;; Let's create another scope, one that contains the above assertion.
(solver-push)

;; We'll add an assertion that forces x to be false.
(z3-assert (x :bool)
           (not x))

;; Now the set of assertions is UNSAT!
(check-sat)

;; There are now 2 assertions.
(print-solver)

;; Let's pop off the top scope. This will remove the assertion we just
;; added.
(solver-pop)

;; As expected, check-sat returns a satisfying assignment again.
(check-sat)
(get-model-as-assignment)

;; We're back to the same set of assertions that we had when we ran
;; (solver-push) the second time.
(print-solver)

;; We can pop back to the empty set of assertions that we had after we
;; reset the solver.
(solver-pop)
(print-solver)

;; ==================
;;       Sorts
;; ==================
;; Z3 supports many variable types, which it calls "sorts".
;; We've already seen booleans and integers.
(solver-push)
(z3-assert (x :bool y :int z :string)
           (and x (> y 5) (= (str.len z) 3)))
(check-sat)
(get-model-as-assignment)

;; Z3 also supports sequence types, including strings.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y :string)
           (and (> (seq.len x) 3)
                (> (str.len y) 3)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; Here's another example showing more of the sequence operators.
(solver-reset)
(solver-push)
(z3-assert (x (:seq :int) y (:seq :int) z (:seq :int))
           (and (> (seq.len x) 3)
                (> (seq.len y) 1)
                ;; x contains the subsequence consisting of the 0th element of y
                ;; this is equivalent to saying that x contains the 0th element of y
                (seq.contains x (seq.at y 0))
                ;; z equals the concatenation of x and y
                (= z (seq.++ x y))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; You can define enumeration sorts as follows:
(register-enum-sort :my-sort (a b c))
;; this sort consists of one of the three values a, b, and c.

;; Now you can use this sort in assertions!
(solver-push)
(z3-assert (x :my-sort y :my-sort)
           (and (not (= x y))
                ;; To represent an element of an enum, you need to use
                ;; `enumval` as shown here.
                (not (= x (enumval :my-sort a)))
                (not (= y (enumval :my-sort b)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

#|
 Note that operations that may cause exceptions in other languages
 (like division by zero) are underspecified in Z3. This means that Z3
 treats `(/ x 0)` as an uninterpreted function that it may assign any
 value to. This can lead to unexpected behavior if you're not careful.

 For example, Z3 reports that the following is satisfiable, since it
 can assign `x` and `y` different values, and has the flexibility to
 have division by 0 for the value of `x` return 3, and division by 0
 for the value of `y` return 4.
|#
(solver-push)
(z3-assert (x :int y :int)
           (and (= (/ x 0) 3)
                (= (/ y 0) 4)))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; There are many more operators and a few more sorts supported by Z3
;; and the lisp-z3 interface. See the operators.md file in
;; <ql-local-projects>/lisp-z3 for more information. The operator
;; documentation is also available on the course website (right next
;; to the HWK 6 link). Feel free to ask on Piazza if anything is
;; unclear.

;; One final note: sometimes, `check-sat` may not return an assignment
;; for some of the input variables provided to `z3-assert`. This often
;; is because Z3 is able to determine that the value of those
;; variables does not affect the satisfiability of the set of
;; assertions being checked, so it returns a partial assignment. If
;; you get a partial assignment, then all possible ways of extending
;; the partial assignment to total assignments are also assignments.

(solver-reset)

;; ==========================
;;            Q1
;; ==========================
;; 15 pts (3 pts each)
;;
;; For each of the following statements, encode the statement into a
;; SMT problem that Z3 can handle using `z3-assert` and report whether
;; the statement is satisfiable or not.
;;
;; As noted above, the list of operators supported by the Lisp-Z3
;; interface is available in HTML format on the course website <link>,
;; as well as in Markdown format in
;; <ql-local-projects>/lisp-z3/operators.md.

;; 1a:
;; x, y, and z are boolean variables.
;; if x is true, then both y and z are true.
;; if y is true, then x is not true and z is not true.
;; if z is false, then y is false

(solver-push)
(z3-assert (x :bool y :bool z :bool)
           (and (=> x (and y z))
                (=> y (and (not x) (not z)))
                (=> (not z) (not y))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; 1b:
;; x,y,z,p and q are all string variables.
;; the concatenation of x y and z is equal to the concatenation of p and q
;; all of the strings have at least length 2
;; y starts with "ab"
;; p ends with "ba"

(solver-push)
(z3-assert (x :string y :string z :string p :string q :string p-prefix :string)
           (and (= (str.++ x y z) (str.++ p q))
                (>= (str.len x) 2)
                (>= (str.len y) 2)
                (>= (str.len z) 2)
                (>= (str.len p) 2)
                (>= (str.len q) 2)
                (seq.prefixof "ab" y)
                (= p (str.++ p-prefix "ba"))))
(check-sat)
(get-model-as-assignment)
(solver-pop)


;; 1c:
;; x is a sequence of booleans
;; y is an integer variable
;; y is between 0 and 32 inclusive
;; x has length equal to y
;; if x has at least one element and the first element of x is true,
;; then the length of x is even. Otherwise, the length of x is 
(solver-push)
(z3-assert (x (:seq :bool) y :int)
           (and (>= y 0)
                (<= y 32)
                (= (seq.len x) y)
                (ite (and (> (seq.len x) 0)
                          (seq.nth x 0))
                     (= (mod (seq.len x) 2) 0)
                     (= (mod (seq.len x) 2) 1))))
(check-sat)
(get-model-as-assignment)
(solver-pop)


;; Now, we'll have some fun by encoding logic puzzles as SMT problems.

;; 1d:
;; (adapted from "What is the Name of This Book?" by Raymond Smullyan)

;; An island is inhabited by "knights" who always tell the truth, and
;; "knaves" who always lie. A stranger comes across three inhabitants
;; of this island standing together (Alice, Bob, and Clara) and asks
;; Alice "How many knights are among you?". Alice answers
;; indistinctly, and the stranger then asks Bob what Alice said. Bob
;; responds "Alice said there is one knight among us." Clara
;; interjects, saying "Don't believe Bob, he's lying!"
;; Is Bob a knight or a knave? Is Clara a knight or a knave?

(solver-push)
(z3-assert (alice :bool bob :bool clara :bool alice-said-one :bool)
           (and
            (= alice-said-one (= alice (= (+ (ite alice 1 0)
                                             (ite bob 1 0)
                                             (ite clara 1 0)) 1)))
            (= bob alice-said-one)
            (= clara (not bob))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; 1e:
;; (adapted from from "My best puzzles in logic and reasoning" by
;; Hubert Phillips, now public domain)
#|
Mr. Fireman, Mr. Guard, and Mr. Driver are (not necessarily
respectively) the fireman, guard, and driver of an express
train. Exactly one of the following statements is true:
- Mr. Driver is not the guard
- Mr. Fireman is not the driver
- Mr. Driver is the driver
- Mr. Fireman is not the guard

Is the above set of constraints consistent? If so, who has what job?

(hint: an enumeration sort might be helpful here)
|#
(register-enum-sort :job (fireman guard driver))

(solver-push)
(z3-assert (mr-fireman :job mr-guard :job mr-driver :job)
           (and
            (not (= mr-fireman mr-guard))
            (not (= mr-fireman mr-driver))
            (not (= mr-guard mr-driver))
            (= 1 (+ (ite (not (= mr-driver (enumval :job guard))) 1 0)
                    (ite (not (= mr-fireman (enumval :job driver))) 1 0)
                    (ite (= mr-driver (enumval :job driver)) 1 0)
                    (ite (not (= mr-fireman (enumval :job guard))) 1 0)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; ===========================
;;    Generating Constraints
;; ===========================
;;
;; It can get tedious to manually generate the constraints that encode
;; a particular problem. Since constraints are written using
;; S-expressions, we can use Lisp to generate constraints
;; programmatically.

;; Let's take a look at a very simple problem: we want to use Z3 to
;; find a normal semimagic square of order 3. A non-trivial semimagic
;; square of order `n` is an `n` x `n` grid of integers between 1 and
;; n^2 inclusive such that all of the rows and columns sum to the same
;; value. Since we did not specify that the magic square is
;; non-trivial, more than one cell in the square may have the same
;; value.

;; First, let's think about the constraints that we will need to
;; generate for this problem. We will likely want to encode each
;; square in the grid as an integer variable, and then add constraints
;; that state that the sums of the integer variables for each row and
;; column all equal the same value.

;; Let's consider an order-2 semimagic square. For this square, we
;; need 4 integer variables. I'll call them X0, X1, X2, and X3. They
;; need to have values between 1 and 4 inclusive, e.g. the following
;; conjunction must hold:
#|
(and (> X0 0) (<= X0 4)
     (> X1 0) (<= X1 4)
     (> X2 0) (<= X2 4)
     (> X3 0) (<= X3 4))
|#

;; Our square will look like this:
#|
+---------+
| X0 | X1 |
+---------+
| X2 | X3 |
+---------+
|#
;; Now, we need to encode that the sums of the rows and columns are
;; the same. I'll introduce another integer variable, S, to represent
;; the sum of the rows and columns.
;; The constraints are:
;; (= (+ X0 X1) S) ;; row 0
;; (= (+ X2 X3) S) ;; row 1
;; (= (+ X0 X2) S) ;; col 0
;; (= (+ X1 X3) S) ;; col 1

;; To write this in a form that `z3-assert` can understand, we need to
;; take the conjunction of the row and column constraints, and
;; generate a list defining each variable and its sort. We also need
;; to add in the constraints on the range of each variable.
;; In this case, we would generate:

(z3-assert (X0 :int X1 :int X2 :int X3 :int S :int)
           (and (> X0 0) (<= X0 4) ;; x0 is within the appropriate range
                (> X1 0) (<= X1 4) ;; ditto for x1
                (> X2 0) (<= X2 4)
                (> X3 0) (<= X3 4)
                (= (+ X0 X1) S) ;; row 0
                (= (+ X2 X3) S) ;; row 1
                (= (+ X0 X2) S) ;; col 0
                (= (+ X1 X3) S))) ;; col 1
;; We can use Z3 to determine if any such magic square exists:
(check-sat)
;; Indeed, one exists: all of the squares are 1. Boring, but it works.
(solver-reset)

;; Now, let's generate those constraints for an order-3 semimagic
;; square programmatically.

;; When dealing with a grid of variables, it is often useful to have a
;; way of transforming a pair of a row and column indices into the
;; variable at that location. I'll define such a function below.
(defun get-3x3-magic-square-var (row col)
  ;; See the Common Lisp HyperSpec for more information about any
  ;; Common Lisp function.
  ;; For example, the documentation for `concatenate` can be found at
  ;; http://clhs.lisp.se/Body/f_concat.htm
  ;; You can also ask SBCL for documentation for a function
  ;; by running (describe #'<function-name>) in the REPL.
  ;; e.g. (describe #'concatenate)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 3))))))
;;

;; This should give us the variable for the first cell, X0
(get-3x3-magic-square-var 0 0)
;; Don't worry if it prints out :INTERNAL afterwards - `intern`
;; actually returns multiple values (see the HyperSpec for more info)

;; Now, let's define a function that will generate the constraint that
;; states that the sum of a particular row should be equal to some variable.
(defun 3x3-magic-square-row-sum (row sum-var)
  ;; I'm going to use the loop macro here. This is a very powerful
  ;; macro that allows us to avoid writing helper functions just to
  ;; perform basic loops.
  ;; See the HyperSpec and
  ;; https://gigamonkeys.com/book/loop-for-black-belts.html for more
  ;; information.
  ;; We want to first generate the variables corresponding to each
  ;; cell in this row.
  (let ((row-squares
         (loop for col below 3
               collect (get-3x3-magic-square-var row col))))
    ;; Then, we want to say that the sum of the squares is equal to
    ;; whatever the sum-var is.
    `(= ,sum-var (+ . ,row-squares))))

;; Just as a sanity check, let's generate the constraint for the first row.
(3x3-magic-square-row-sum 0 'S)
;; great, exactly as we expected.

;; Now, let's define a similar function for columns.
(defun 3x3-magic-square-col-sum (col sum-var)
  (let ((col-squares
         (loop for row below 3
               collect (get-3x3-magic-square-var row col))))
    `(= ,sum-var (+ . ,col-squares))))
;; Another sanity check...
(3x3-magic-square-col-sum 0 'S)
;; looks good.

;; Now, let's put it all together. We want to generate the constraints
;; for all of the rows and all of the columns and take the conjunction
;; of them.
(defun 3x3-magic-square-row-col-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var))))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints)))
;; Great, this is a conjunction of equalities, which is what we expect.
(3x3-magic-square-row-col-constraints 'S)

;; Finally, we need to generate the list of variables and their sorts.
(defun 3x3-magic-square-var-specs (sum-var)
  (let ((cell-vars (loop for row below 3 append
                         (loop for col below 3 append
                               `(,(get-3x3-magic-square-var row col) :int)))))
    `(,sum-var :int ,@cell-vars)))

(3x3-magic-square-var-specs 'S)

;; We also need to assert that all of the values are between 1 and 9.
(defun 3x3-magic-square-vars-between-1-and-9 ()
  (cons 'and (loop for row below 3 append
                   (loop for col below 3 append
                         `((>= ,(get-3x3-magic-square-var row col) 1)
                           (<= ,(get-3x3-magic-square-var row col) 9))))))

;; Now, we just need to pass this information into `z3-assert`.
;; `z3-assert` is just a macro that calls `z3-assert-fn` on its quoted
;; input. All this means is that we can skip some shenanigans with
;; backquote and just pass the constraints and variable specifications
;; directly into `z3-assert-fn`.

(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-row-col-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(check-sat)
;; We get our satisfying assignment, still boring (all 1s) but correct.
(solver-pop)

;; You'll expand upon this in Q2 below.

(solver-reset)

;; ==========================
;;            Q2
;; ==========================
;; 25 pts

;; Use Z3 to find a normal non-trivial magic square of order 3.

;; You should use a similar approach to that shown above to
;; programmatically generate the constraints and pass them into
;; `z3-assert-fn`.

;; A magic square is a semimagic square that also satisfies the
;; property that all diagonals also sum to the same value as all of
;; the rows and columns.
;; A non-trivial magic square is a magic square such that no two cells
;; have the same value.

(defun 3x3-magic-square-forward-diagonal-sum (sum-var)
     (let ((diagonal-squares
               (loop for each below 3
                    collect (get-3x3-magic-square-var each each))))
          `(= ,sum-var (+ . ,diagonal-squares))
          ))

(defun 3x3-magic-square-backward-diagonal-sum (sum-var)
  (let ((diagonal-squares
         (list (get-3x3-magic-square-var 0 2)
               (get-3x3-magic-square-var 1 1)
               (get-3x3-magic-square-var 2 0))))
    `(= ,sum-var (+ . ,diagonal-squares))))


(defun 3x3-magic-square-non-trivial ()
     (let ((all-vars
     (loop for row below 3 append
          (loop for col below 3 collect
               (get-3x3-magic-square-var row col)))))
     `(distinct  ,@all-vars)))

(defun 3x3-normal-non-trivial-magic-square-row-col-diagonal-constraints (sum-var)
  (let ((row-constraints (loop for row below 3 collect (3x3-magic-square-row-sum row sum-var)))
        (col-constraints (loop for col below 3 collect (3x3-magic-square-col-sum col sum-var)))
        (forward-diagonal (3x3-magic-square-forward-diagonal-sum sum-var))
        (backward-diagonal (3x3-magic-square-backward-diagonal-sum sum-var)))
    ;; ,@ splices a list into an S-expression. e.g. `(1 ,@(list 2 3)) = '(1 2 3)
    `(and ,@row-constraints ,@col-constraints ,forward-diagonal ,backward-diagonal)))


(solver-push)
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-normal-non-trivial-magic-square-row-col-diagonal-constraints 'S))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-vars-between-1-and-9))
(z3-assert-fn (3x3-magic-square-var-specs 'S)
              (3x3-magic-square-non-trivial))
              
(check-sat)
(solver-pop)
(solver-reset)


;; ==========================
;;            Q3
;; ==========================
;; 30 pts
;;
;; Develop a Sudoku solver that uses an approach similar to that
;; described above to use Z3 to generate solutions to a given starting
;; board. The top-level function should be called `solve-sudoku`, and
;; should take a starting board as an argument. The format of the
;; starting board will be defined below. `solve-sudoku` should return
;; either 'UNSAT (if no valid Sudoku board also satisfies the starting
;; board) or an assignment (a list of 2-element lists, similar to a
;; let binding, where the first element is the variable name and the
;; second is the assignment) that represents a filled-in Sudoku board
;; that satisfies the starting board's assignments.
;;
;; A valid Sudoku board is a 3x3 grid of 3x3 boxes. The 9 cells in
;; each box must all be integers from 1 to 9 inclusive, and must all
;; be different. Every row and column of the 9x9 Sudoku grid must
;; contain every integer from 1 to 9 inclusive exactly once.
;;
;; You will first use a bit-blasting encoding for this problem,
;; similar to the approach that I used to generate the example Sudoku
;; problems that I evaluated your DP algorithms using.  What I mean by
;; this is that each Sudoku square will be represented by 9 variables,
;; one for each possible value it may have.
;;
;; A starting board consists of a standard 3x3 Sudoku board with only
;; a subset of cells having specified values. We will use _ to denote
;; unspecified values. The starting board will be represented by a
;; list of 81 elements, where each element can be an integer between 1
;; and 9 inclusive or _.
;;
;; `solve-sudoku` should return an alist mapping Sudoku cell variables
;; (see `sudoku-cell-var` below) to booleans depending on whether the
;; cell represented by the cell variable has the value represented by
;; the cell variable.
;;
;; I have provided the function that generates a variable
;; corresponding to the Sudoku cell at a given row and column having a
;; particular value.
;; row and col should both be integers from 0 to 8, inclusive.
;; val should be an integer from 1 to 9, inclusive.
(defun sudoku-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 9))) "_" (write-to-string val))))

;; I have provided some utilities for pretty-printing Sudoku solutions
;; below.

(defun assoc-equal (x a)
  (assoc x a :test #'equal))

;; Given a solution that is an alist from cell vars to booleans, get
;; the assigned value for the cell at the given row and column, or nil
;; if it is unassigned.
(defun get-square-value (soln row col)
  (block outer
    (loop for i from 1 to 9
          do (when (and (cdr (assoc-equal (sudoku-cell-var row col i) soln))
                        (cadr (assoc-equal (sudoku-cell-var row col i) soln)))
               (return-from outer i)))
    nil))

;; This pretty-prints a Sudoku solution, using `get-square-value` to
;; handle the task of getting the value of a cell from the solution
;; representation used.
(defun pretty-print-3x3-sudoku-solution (soln)
  (loop for row below 9
        do (progn (terpri)
                  (loop for col below 9
                        do (progn (format t "~A " (get-square-value soln row col))
                                  (when (equal (mod col 3) 2) (format t "  "))))
                  (when (equal (mod row 3) 2) (terpri)))))

;; Here's an example starting board. It has a unique solution.
(defconstant *sudoku-example-board*
  '(7 _ _   _ 1 _   _ _ _
    _ 1 _   _ _ 3   7 _ 8
    _ 5 3   _ _ _   _ _ 4

    5 _ 9   3 _ _   _ _ 2
    4 _ 1   2 6 _   3 7 _
    _ _ 7   _ 8 5   9 4 _

    2 7 _   _ 9 4   _ 3 _
    8 _ _   5 _ 1   _ 6 _
    _ 3 _   _ _ 2   4 5 _))

;; Here's its solution.
#|
 7 4 8   9 1 6   5 2 3
 6 1 2   4 5 3   7 9 8
 9 5 3   7 2 8   6 1 4

 5 6 9   3 4 7   1 8 2
 4 8 1   2 6 9   3 7 5
 3 2 7   1 8 5   9 4 6

 2 7 5   6 9 4   8 3 1
 8 9 4   5 3 1   2 6 7
 1 3 6   8 7 2   4 5 9
|#

(defun sudoku-cell-vars (row col)
  (loop for val from 1 to 9
      collect (sudoku-cell-var row col val)))

(defun sudoku-exactly-one (vars)
  `(and ((_ at-least 1) ,@vars)
        ((_ at-most 1) ,@vars)))

(defun sudoku-cell-constraints ()
  (cons 'and 
         (loop for row below 9 append
            (loop for col below 9
              collect (sudoku-exactly-one
                        (sudoku-cell-vars row col))))))

(defun sudoku-row-value-vars (row val)
  (loop for col below 9
      collect (sudoku-cell-var row col val)))

(defun sudoku-row-constraints ()
  (cons 'and
      (loop for row below 9 append
        (loop for val from 1 to 9
          collect (sudoku-exactly-one
                    (sudoku-row-value-vars row val))))))

(defun sudoku-col-value-vars (col val)
  (loop for row below 9
    collect (sudoku-cell-var row col val)))

(defun sudoku-col-constraints ()
  (cons 'and
      (loop for col below 9 append
        (loop for val from 1 to 9
            collect (sudoku-exactly-one
                      (sudoku-col-value-vars col val))))))

(defun sudoku-box-value-vars (box-row box-col val)
    (loop for row from (* 3 box-row) below (+ (* 3 box-row) 3) append
        (loop for col from (* 3 box-col) below (+ (* 3 box-col) 3)
            collect (sudoku-cell-var row col val))))

(defun sudoku-box-constraints ()
  (cons 'and
      (loop for box-row below 3 append
          (loop for box-col below 3 append
              (loop for val from 1 to 9
                  collect (sudoku-exactly-one
                              (sudoku-box-value-vars box-row box-col val)))))))

(defun sudoku-starting-board-constraints (input-grid)
    (cons 'and
        (loop for entry in input-grid 
              for idx from 0
              unless (equal entry '_)
                collect (sudoku-cell-var (floor idx 9)
                                          (mod idx 9)
                                          entry))))

(defun sudoku-var-specs ()
  (loop for row below 9 append
      (loop for col below 9 append
          (loop for val from 1 to 9 append
             `(,(sudoku-cell-var row col val) :bool)))))

(defun solve-sudoku (input-grid)
  (let ((var-specs (sudoku-var-specs)))
    (solver-push)
    (z3-assert-fn var-specs (sudoku-cell-constraints))
    (z3-assert-fn var-specs (sudoku-row-constraints))
    (z3-assert-fn var-specs (sudoku-col-constraints))
    (z3-assert-fn var-specs (sudoku-box-constraints))
    (z3-assert-fn var-specs (sudoku-starting-board-constraints input-grid))
    (let ((res (check-sat)))
      (prog1
          (if (or (equal res 'SAT)
                  (equal res :SAT)
                  (equal res 'sat)
                  (equal res :sat))
                (get-model-as-assignment)
                'UNSAT)
              (solver-pop)))))

;; This should print out the solution given above.
(pretty-print-3x3-sudoku-solution (time (solve-sudoku *sudoku-example-board*)))

;; ==========================
;;            Q4
;; ==========================
;; 30 pts
;;
;; 4a. (15 pts)
;;
;; Experiment with a different encoding for Sudoku cells. For example,
;; you could use integers to represent each square, or enumeration
;; sorts. You should define `solve-sudoku-alternate` below to behave
;; like `solve-sudoku` as described in Q3, except that it must use a
;; different encoding to represent the value of each Sudoku cell.
;;
;; You likely will want to define your own version of
;; `sudoku-cell-var`, perhaps omitting the `val` parameter if it is
;; not necessary for your cell value representation.
;;
;; You can continue to use the `pretty-print-3x3-sudoku-solution`
;; function I provided if you redefine `get-square-value` to work with
;; your variable encoding.

(register-enum-sort :sudoku-val (v1 v2 v3 v4 v5 v6 v7 v8 v9))

(defun sudoku-cell-var-alt (row col)
  (intern (concatenate 'string "C" (write-to-string (+ col (* row 9))))))

;; helper to generate all pairwise
(defun all-different (vars)
  (loop for (v . rest) on vars
        append (loop for v2 in rest
                     collect `(not (= ,v ,v2)))))

;; Get all the row var
(defun sudoku-row-vars (row)
  (loop for col below 9
        collect (sudoku-cell-var-alt row col)))

;; get all the col vars
(defun sudoku-col-vars (col)
  (loop for row below 9
        collect (sudoku-cell-var-alt row col)))

;; makes a 3x3 box
(defun sudoku-box-vars (box-row box-col)
  (let ((start-row (* box-row 3))
        (start-col (* box-col 3)))
    (loop for r below 3
          append (loop for c below 3
                       collect (sudoku-cell-var-alt (+ start-row r)
                                                    (+ start-col c))))))

;; convert integer 1-9 to enum value
(defun int-to-sudoku-val (n)
  (nth (- n 1) '((enumval :sudoku-val v1)
                  (enumval :sudoku-val v2)
                  (enumval :sudoku-val v3)
                  (enumval :sudoku-val v4)
                  (enumval :sudoku-val v5)
                  (enumval :sudoku-val v6)
                  (enumval :sudoku-val v7)
                  (enumval :sudoku-val v8)
                  (enumval :sudoku-val v9))))

;; convert enum assignment back to integer for pretty printing
(defun sudoku-val-to-int (val)
  (cond ((string= (symbol-name val) "V1") 1)
        ((string= (symbol-name val) "V2") 2)
        ((string= (symbol-name val) "V3") 3)
        ((string= (symbol-name val) "V4") 4)
        ((string= (symbol-name val) "V5") 5)
        ((string= (symbol-name val) "V6") 6)
        ((string= (symbol-name val) "V7") 7)
        ((string= (symbol-name val) "V8") 8)
        ((string= (symbol-name val) "V9") 9)))

(defun sudoku-alt-var-specs ()
  (loop for row below 9
        append (loop for col below 9
                     append `(,(sudoku-cell-var-alt row col) :sudoku-val))))

(defun sudoku-alt-constraints (input-grid)
  (let* (;; all-different for rows
         (row-constraints
          (loop for row below 9
                append (all-different (sudoku-row-vars row))))
         ;; all-different for cols
         (col-constraints
          (loop for col below 9
                append (all-different (sudoku-col-vars col))))
         ;; all-different for boxes
         (box-constraints
          (loop for br below 3
                append (loop for bc below 3
                             append (all-different (sudoku-box-vars br bc)))))
         ;; starting board constraints
         (given-constraints
          (loop for i below 81
                for val in input-grid
                when (not (equal val '_))
                collect `(= ,(sudoku-cell-var-alt (floor i 9) (mod i 9))
                            ,(int-to-sudoku-val val)))))
    `(and ,@row-constraints
          ,@col-constraints
          ,@box-constraints
          ,@given-constraints)))


(defun get-square-value-alt (soln row col)
  (let ((entry (assoc (symbol-name (sudoku-cell-var-alt row col))
                      soln
                      :key #'symbol-name
                      :test #'string=)))
    (when entry (sudoku-val-to-int (cadr entry)))))

(defun get-square-value (soln row col)
  (get-square-value-alt soln row col))

(defun solve-sudoku-alternate (input-grid)
  (solver-reset)
  (solver-push)
  (z3-assert-fn (sudoku-alt-var-specs)
                (sudoku-alt-constraints input-grid))
  (let ((result (check-sat)))
    (if (equal result :sat)
        (get-model-as-assignment)
        'unsat)))

;; 4b. (15 pts)
;;
;; Compare the performance of `solve-sudoku` and
;; `solve-sudoku-alternate`. Come up with the hardest Sudoku grid you
;; can find for each solver and explain why you think it is hard.
;;
;; Note that Z3 uses a variant of DPLL called DPLL(T) for solving SMT
;; problems.
;;
;; You may find it useful to see internal statistics that Z3 collects
;; during SMT solving. These statistics are cumulative, so you should
;; re-initialize Z3 before each query that you want to measure.
;; These statistics can be printed by calling `(z3::get-solver-stats)`.
;;
;; Unfortunately there is no single resource that describes what all
;; of the returned statistics means, but some statistics of note are:
;; - :conflicts: the number of conflicts found during DPLL
;; - :decisions: the number of DPLL decisions made
;; - :propagations: the number of times unit propagation was performed
;; - :restarts: the number of times that Z3 decided to restart DPLL
;;   from the beginning, retaining learned conflict clauses (recall
;;   nonchronological backtracking)

;; The hardest Sudoku board for your `solve-sudoku` implementation.

(defconstant *hardest-sudoku-board*
  '(1 _ _  _ _ 7  _ 9 _
    _ 3 _  _ 2 _  _ _ 8
    _ _ 9  6 _ _  5 _ _
    _ _ 5  3 _ _  9 _ _
    _ 1 _  _ 8 _  _ _ 2
    6 _ _  _ _ 4  _ _ _
    3 _ _  _ _ _  _ 1 _
    _ 4 _  _ _ _  _ _ 7
    _ _ 7  _ _ _  3 _ _))

(solver-init)
(time (solve-sudoku *hardest-sudoku-board*))
(z3::get-solver-stats)

(solver-reset)

;; The hardest Sudoku board for your `solve-sudoku-alternate`
;; implementation.
(defconstant *hardest-sudoku-board-alternate*
  '(1 _ _  _ _ 7  _ 9 _
    _ 3 _  _ 2 _  _ _ 8
    _ _ 9  6 _ _  5 _ _

    _ _ 5  3 _ _  9 _ _
    _ 1 _  _ 8 _  _ _ 2
    6 _ _  _ _ 4  _ _ _

    3 _ _  _ _ _  _ 1 _
    _ 4 _  _ _ _  _ _ 7
    _ _ 7  _ _ _  3 _ _))

(solver-init)
(register-enum-sort :sudoku-val (v1 v2 v3 v4 v5 v6 v7 v8 v9))
(time (solve-sudoku-alternate *hardest-sudoku-board-alternate*))
(z3::get-solver-stats)


;; EXTRA CREDIT #2 
;; unruly is NP-hard but it is easy to encode hehe
;; basically encode it like we encode sudoku
;; 8x8 board
;; then we only have black or white so i encode black as 1 and white as 2
;; then we encode constraints: each row or col must have 4 black and 4 white
;; and no consecutive 3 for black or white is even easier, we literally start
;; counting one by one until there is not enough items on the same row (like col 6)
;; finally we encode the board and boom it is done
;; i don't want to write too many examples so one example you can just have everything
;; as empty so we start with an empty board
;; second instance we can have an obviously unsat board with consecutive 3 white or black
;; for a working example, see the board i supplied as example, it is taken from the website
;; so it definitely works and our solution gives an answer
;; chatgpt usage about 10 percent


(defun unruly-cell-var (row col val)
  (intern (concatenate 'string "X" (write-to-string (+ col (* row 8))) "_" (write-to-string val))))

(defun get-unruly-value (soln row col)
    (cond
      ((cadr (assoc-equal (unruly-cell-var row col 1) soln)) 1)
      ((cadr (assoc-equal (unruly-cell-var row col 2) soln)) 2)
      (t '_)))

(defun pretty-print-unruly (soln)
  (loop for row below 8 do
      (progn
          (terpri)
          (loop for col below 8 do
              (format t "~A " (get-unruly-value soln row col))))))

(defun unruly-cell-vars (row col)
  (loop for val from 1 to 2
      collect (unruly-cell-var row col val)))


(defconstant *unruly-example-board*
  '(_ _ _ _  _ _ _ 1
    1 _ 1 2  _ 2 _ 1
    _ _ _ 2  _ 2 _ _ 
    _ _ _ _  _ _ _ 2
    1 1 _ _  _ _ _ _ 
    1 _ 2 _  _ 1 _ _
    _ _ _ _  _ _ 1 _ 
    _ 2 _ _  _ _ 2 _
  ))

(defun unruly-exactly-one (vars)
  `(and ((_ at-least 1) ,@vars)
        ((_ at-most 1) ,@vars)))

(defun unruly-exactly-four (vars)
  `(and ((_ at-least 4) ,@vars)
        ((_ at-most 4) ,@vars)))


;; each cell in unruly can only have 1 or 2
(defun unruly-cell-constraints ()
  (cons 'and
          (loop for row below 8 append
            (loop for col below 8
              collect (unruly-exactly-one
                        (unruly-cell-vars row col))))))


;; each row in unruly must have 4 1s and 4 2s
(defun unruly-row-value-vars (row val)
  (loop for col below 8
      collect (unruly-cell-var row col val)))

(defun unruly-row-constraints ()
  (cons 'and
    (loop for row below 8 append
      (loop for val from 1 to 2
        collect (unruly-exactly-four
                  (unruly-row-value-vars row val))))))


(defun unruly-col-value-vars (col val)
  (loop for row below 8
    collect (unruly-cell-var row col val)))

(defun unruly-col-constraints ()
  (cons 'and
      (loop for col below 8 append
        (loop for val from 1 to 2
            collect (unruly-exactly-four
                      (unruly-col-value-vars col val))))))

;; for consecutive 3s, row 0 to 5 cannot have consecutive
(defun consecutive-row-constraints ()
  (cons 'and
      (loop for row below 8 append
        (loop for col from 0 to 5 append
            (list
                `(not (and ,(unruly-cell-var row col 1)
                           ,(unruly-cell-var row (+ col 1) 1)
                           ,(unruly-cell-var row (+ col 2) 1)))
                `(not (and ,(unruly-cell-var row col 2)
                           ,(unruly-cell-var row (+ col 1) 2)
                           ,(unruly-cell-var row (+ col 2) 2))))))))

(defun consecutive-col-constraints ()
  (cons 'and
      (loop for col below 8 append
        (loop for row from 0 to 5 append
            (list
                `(not (and ,(unruly-cell-var row col 1)
                           ,(unruly-cell-var (+ row 1) col 1)
                           ,(unruly-cell-var (+ row 2) col 1)))
                `(not (and ,(unruly-cell-var row col 2)
                           ,(unruly-cell-var (+ row 1) col 2)
                           ,(unruly-cell-var (+ row 2) col 2))))))))

(defun unruly-starting-board-constraints (input-grid)
    (cons 'and
        (loop for entry in input-grid
              for idx from 0
              unless (equal entry '_)
                collect (unruly-cell-var (floor idx 8)
                                         (mod idx 8)
                                         entry))))

(defun unruly-var-specs ()
  (loop for row below 8 append 
    (loop for col below 8 append
      (loop for val from 1 to 2 append
        `(,(unruly-cell-var row col val) :bool)))))

(defun solve-unruly (input-grid)
  (let ((var-specs (unruly-var-specs)))
      (solver-push)
      (z3-assert-fn var-specs (unruly-cell-constraints))
      (z3-assert-fn var-specs (unruly-row-constraints))
      (z3-assert-fn var-specs (unruly-col-constraints))
      (z3-assert-fn var-specs (consecutive-row-constraints))
      (z3-assert-fn var-specs (consecutive-col-constraints))
      (z3-assert-fn var-specs (unruly-starting-board-constraints input-grid))
        (let ((res (check-sat)))
            (prog1 
                (if (member res '(SAT :SAT sat :sat))
                    (get-model-as-assignment)
                    'UNSAT)
                  (solver-pop)))))


(pretty-print-unruly (time (solve-unruly *unruly-example-board*)))
