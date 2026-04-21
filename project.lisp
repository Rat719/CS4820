; STLC Type Soundness in ACL2s
; Christopher Wright-Williams & Zheng Wangyuan (Patrick)
; CS4820 — Professor Manolios

(in-package "ACL2S")

;;;;                                         PART 1: DATA DEFINITIONS

; stype: Bool or (Fun S T)
(defdata stype
  (oneof 'Bool
         (list 'Fun stype stype)))

; expr: the six forms of STLC expressions
(defdata expr
  (oneof 'True
         'False
         (list 'Var symbol)
         (list 'Lam symbol stype expr)
         (list 'App expr expr)
         (list 'If expr expr expr)))

; env (aka Gamma): maps variable names to their types
(defdata env (alistof symbol stype))

;;;;                                         PART 2: TYPING RELATION

; helper lemmas so type-check's guard verification goes through
(defthm lam-var-symbolp
  (implies (and (exprp e)
                (consp (double-rewrite e))
                (equal (car e) 'Lam))
           (symbolp (cadr e))))

(defthm lam-ty-stypep
  (implies (and (exprp e)
                (consp (double-rewrite e))
                (equal (car e) 'Lam))
           (stypep (caddr e))))

(defthm lam-body-exprp
  (implies (and (exprp e)
                (consp (double-rewrite e))
                (equal (car e) 'Lam))
           (exprp (cadddr e))))

(defthm envp-cons-extension
  (implies (and (envp g)
                (symbolp v)
                (stypep ty))
           (envp (cons (cons v ty) g))))

(defthm lam-env-extension
  (implies (and (envp g)
                (exprp e)
                (consp (double-rewrite e))
                (equal (car e) 'Lam))
           (envp (cons (cons (cadr e) (caddr e)) g))))

; type-check: returns the type of e under context g, or nil if ill-typed
; implements T-True, T-False, T-Var, T-Abs, T-App, T-If
; NOTE: :skip-body-contractsp t for now — guards need more work
(definec type-check (g :env e :expr) :all
  :skip-body-contractsp t
  (match e
    ('True  'Bool)
    ('False 'Bool)
    (('Var v) (cdr (assoc-equal v g)))
    (('Lam v ty body)
     (let ((body-type (type-check (cons (cons v ty) g) body)))
       (if body-type (list 'Fun ty body-type) nil)))
    (('App f a)
     (let ((ft (type-check g f))
           (at (type-check g a)))
       (if (and ft at
                (consp ft)
                (equal (car ft) 'Fun)
                (equal (cadr ft) at))
           (caddr ft)
           nil)))
    (('If cond thn els)
     (let ((ct (type-check g cond))
           (tt (type-check g thn))
           (et (type-check g els)))
       (if (and (equal ct 'Bool) tt (equal tt et))
           tt
           nil)))
    (& nil)))

;;;;                               PART 3: VALUES AND EVALUATION

; values are True, False, and lambdas
(definec valuep (e :expr) :bool
  (match e
    ('True t)
    ('False t)
    (('Lam & & &) t)
    (& nil)))

; free variables of an expression
(definec free-vars (e :expr) :tl
  (match e
    ('True nil)
    ('False nil)
    (('Var v) (list v))
    (('Lam v & body) (remove-equal v (free-vars body)))
    (('App f a) (union-equal (free-vars f) (free-vars a)))
    (('If c thn els) (union-equal (free-vars c)
                                  (union-equal (free-vars thn)
                                               (free-vars els))))
    (& nil)))

; accessors — give us named projections instead of raw cadr/caddr
; these admit cleanly and make downstream code much more readable

(definec expr-tag (e :expr) :all
  (cond ((equal e 'True)  'True)
        ((equal e 'False) 'False)
        ((consp e) (car e))
        (t nil)))

(definec var-name (e :expr) :all
  (if (and (consp e) (equal (car e) 'Var)) (cadr e) nil))

(definec lam-var (e :expr) :all
  (if (and (consp e) (equal (car e) 'Lam)) (cadr e) nil))

(definec lam-type (e :expr) :all
  (if (and (consp e) (equal (car e) 'Lam)) (caddr e) nil))

(definec lam-body (e :expr) :all
  (if (and (consp e) (equal (car e) 'Lam)) (cadddr e) nil))

(definec app-fun (e :expr) :all
  (if (and (consp e) (equal (car e) 'App)) (cadr e) nil))

(definec app-arg (e :expr) :all
  (if (and (consp e) (equal (car e) 'App)) (caddr e) nil))

(definec if-cond (e :expr) :all
  (if (and (consp e) (equal (car e) 'If)) (cadr e) nil))

(definec if-then (e :expr) :all
  (if (and (consp e) (equal (car e) 'If)) (caddr e) nil))

(definec if-else (e :expr) :all
  (if (and (consp e) (equal (car e) 'If)) (cadddr e) nil))

; constructors — parallel to the accessors
(definec mk-lam (v :symbol ty :stype body :expr) :expr
  (list 'Lam v ty body))

(definec mk-app (f :expr a :expr) :expr
  (list 'App f a))

(definec mk-if (c :expr thn :expr els :expr) :expr
  (list 'If c thn els))

; stlc-subst: naive substitution [v |-> val] e
; precondition: val should be closed (no free vars) to avoid capture
; we don't enforce this in the function — the substitution lemma will
; carry the closedness hypothesis
(definec stlc-subst (v :symbol val :expr e :expr) :expr
  (cond
    ((equal (expr-tag e) 'True)  e)
    ((equal (expr-tag e) 'False) e)
    ((equal (expr-tag e) 'Var)
     (if (equal (var-name e) v) val e))
    ((equal (expr-tag e) 'Lam)
     (if (equal (lam-var e) v)
         e                                                ; shadowed
         (mk-lam (lam-var e) (lam-type e)
                 (stlc-subst v val (lam-body e)))))
    ((equal (expr-tag e) 'App)
     (mk-app (stlc-subst v val (app-fun e))
             (stlc-subst v val (app-arg e))))
    ((equal (expr-tag e) 'If)
     (mk-if (stlc-subst v val (if-cond e))
            (stlc-subst v val (if-then e))
            (stlc-subst v val (if-else e))))
    (t e)))


; stlc-step: one step of call-by-value evaluation
; returns nil if e is a value or stuck
; rules: E-AppAbs, E-App1, E-App2, E-IfTrue, E-IfFalse, E-IfCond
(definec stlc-step (e :expr) :all
  :skip-body-contractsp t
  (cond
    ; values don't step
    ((valuep e) nil)

    ; application
    ((equal (expr-tag e) 'App)
     (let ((f (app-fun e))
           (a (app-arg e)))
       (cond
         ; E-App1: reduce the function position first
         ((not (valuep f))
          (let ((f2 (stlc-step f)))
            (if f2 (mk-app f2 a) nil)))
         ; E-App2: then reduce the argument
         ((not (valuep a))
          (let ((a2 (stlc-step a)))
            (if a2 (mk-app f a2) nil)))
         ; E-AppAbs: both values — f must be a Lam, else stuck
         ((equal (expr-tag f) 'Lam)
          (stlc-subst (lam-var f) a (lam-body f)))
         (t nil))))

    ; conditional
    ((equal (expr-tag e) 'If)
     (let ((c (if-cond e))
           (thn (if-then e))
           (els (if-else e)))
       (cond
         ((equal c 'True)  thn)         ; E-IfTrue
         ((equal c 'False) els)         ; E-IfFalse
         ((not (valuep c))              ; E-IfCond
          (let ((c2 (stlc-step c)))
            (if c2 (mk-if c2 thn els) nil)))
         ; stuck: scrutinee is a Lam value
         (t nil))))

    ; lone Var (unbound) or anything else — stuck
    (t nil)))

;;;;                               PART 4: TYPE SOUNDNESS

; all proofs depend on stlc-step being admitted first

; TODO: env-agree-on helper (needed for permutation)
; (defun env-agree-on (g1 g2 vars) ...)


;;;;                               PART 4a: ENV-AGREE-ON

; env-agree-on: g1 and g2 give the same lookup for every variable in vars.
; Using (cdr (assoc-equal ...)) — total, matches type-check's Var case.
(definec env-agree-on (g1 :env g2 :env vars :tl) :bool
  (if (endp vars)
      t
    (and (equal (cdr (assoc-equal (car vars) g1))
                (cdr (assoc-equal (car vars) g2)))
         (env-agree-on g1 g2 (cdr vars)))))

; L1: reflexivity — trivially any env agrees with itself.
(defthm env-agree-on-refl
    (implies (and (envp g) (tlp vars))
             (env-agree-on g g vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; L2: pointwise consequence. This is the lemma that actually fires
; on the Var case of context-independence.
(defthm env-agree-on-assoc
    (implies (and (envp g1) (envp g2) (tlp vars)
                  (env-agree-on g1 (double-rewrite g2) (double-rewrite vars))
                  (member-equal v vars))
             (equal (cdr (assoc-equal v g1))
                    (cdr (assoc-equal v g2))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; L3: subset monotonicity — narrow agreement to a sublist.
; Carries the App and If cases through: each subterm's free-vars is
; a subset of (union-equal ...).
(defthm env-agree-on-subsetp
    (implies (and (envp g1) (envp g2) (tlp vars) (tlp vars2)
                  (env-agree-on g1 g2 vars)
                  (subsetp-equal (double-rewrite vars2) (double-rewrite vars)))
             (env-agree-on g1 g2 vars2))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; L4: extending both sides with the same binding.
; Carries the Lam case: free-vars (Lam v ty body) = (remove-equal v (free-vars body)),
; and we need agreement on (free-vars body) under the extended envs.
(defthm env-agree-on-cons-both
    (implies (and (envp g1) (envp g2) (tlp vars)
                  (symbolp v) (stypep ty)
                  (env-agree-on g1 g2 (remove-equal v vars)))
             (env-agree-on (cons (cons v ty) g1)
                           (cons (cons v ty) g2)
                           vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;;;                               PART 4b: LIST-THEORY HELPERS

; removing stuff from a list makes it smaller. used for the Lam case later:
; free-vars of (Lam v _ body) = (remove v (free-vars body)), and we need to
; connect that back to (free-vars body) when reasoning about the body.
(defthm subsetp-remove-equal
  (subsetp-equal (remove-equal v vars) vars))

; the left half of a union is inside the union. in the App case, the free
; vars of (App f a) are (union (free-vars f) (free-vars a)) — this lets us
; narrow agreement from the whole union down to just (free-vars f) so the
; IH on f applies. same idea for the cond position of If.
(defthm subsetp-union-equal-left
  (subsetp-equal vs1 (union-equal vs1 vs2)))

; same thing for the right half. handles the argument side of App and the
; then/else sides of If. the tlp hypothesis is there because union-equal's
; base case only behaves right when vs2 is a true-list — in our uses vs2 is
; always (free-vars ...), which has :tl output, so this discharges for free.
(defthm subsetp-union-equal-right
  (implies (tlp vs2)
           (subsetp-equal vs2 (union-equal vs1 vs2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;;;                               PART 4c: CONTEXT-INDEPENDENCE

 ; scaffolding function for a custom induction scheme. does nothing
; computationally — just traces out the shape of induction we need.
;
; why we need this: the default scheme inherited from type-check extends
; only g1 in the Lam case, giving an IH of shape
;   (equal (type-check (cons v:ty g1) body) (type-check g2 body))
; but what we actually need is
;   (equal (type-check (cons v:ty g1) body) (type-check (cons v:ty g2) body))
; this scheme extends BOTH envs in parallel, producing the right IH.
; (ignorable g1 g2) because they're used in recursive-call positions but
; don't affect the return value — RAP Ch. 5 sanctions this pattern.
(defun ctx-indep-ind (g1 g2 e)
  (declare (xargs :measure (acl2-count e))
           (ignorable g1 g2))
  (cond
    ((or (equal e 'True) (equal e 'False)) 0)
    ((atom e) 0)
    ((equal (car e) 'Var) 0)
    ((equal (car e) 'Lam)
     (+ 1 (ctx-indep-ind (cons (cons (cadr e) (caddr e)) g1)
                         (cons (cons (cadr e) (caddr e)) g2)
                         (cadddr e))))
    ((equal (car e) 'App)
     (+ 1 (ctx-indep-ind g1 g2 (cadr e))
        (ctx-indep-ind g1 g2 (caddr e))))
    ((equal (car e) 'If)
     (+ 1 (ctx-indep-ind g1 g2 (cadr e))
        (ctx-indep-ind g1 g2 (caddr e))
        (ctx-indep-ind g1 g2 (cadddr e))))
    (t 0)))

; the main lemma everything in Part 4 is built on: type-check only cares
; about the env at the free variables of e. if two envs g1 and g2 agree
; on (free-vars e), then e has the same type under both.
;
; weakening (adding an unused binding doesn't change types) and permutation
; (reordering distinct bindings doesn't change types) both fall out as
; one-line corollaries using :use on this.
;
; :induct hint forces our custom scheme that extends both envs in parallel.
; :rule-classes nil because as a rewrite rule this would loop forever —
; the conclusion has the same shape on both sides and g2 is free.

(defthm type-check-context-independent
    (implies (and (envp g1) (envp g2) (exprp e)
                  (env-agree-on g1 g2 (free-vars e)))
             (equal (type-check g1 e) (type-check g2 e)))
  :hints (("Goal" :induct (ctx-indep-ind g1 g2 e)))
  :rule-classes nil)

;;;;                               PART 4d.1: Weakening
(defthm env-agree-on-cons-irrelevant
    (implies (and (envp g) (tlp vars)
                  (symbolp v) (stypep tv)
                  (not (member-equal v (double-rewrite vars))))
             (env-agree-on g (cons (cons v tv) g) vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))



;;;;                               PART 4d.2: PERMUTATION

; env-agree-on-swap: two envs with a swapped pair of adjacent
; distinct bindings give the same lookup for every key. induction on
; vars, with case-split on whether the head key is v1, v2, or neither.
; v1 ≠ v2 is what makes the two non-matching cases collapse through
; to the same tail lookup in g.
(defthm env-agree-on-swap
  (implies (and (envp g) (tlp vars)
                (symbolp v1) (stypep t1)
                (symbolp v2) (stypep t2)
                (not (equal v1 v2)))
           (env-agree-on (cons (cons v1 t1) (cons (cons v2 t2) g))
                         (cons (cons v2 t2) (cons (cons v1 t1) g))
                         vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; permutation-swap: swapping two adjacent distinct bindings in the
; env doesn't change the type. same two-:use pattern as weakening —
; context-independence + a concrete env-agree-on fact.
;
; :rule-classes nil: the equality is directionless (both sides are
; concrete env shapes with no preferred orientation); as a rewrite
; it would loop. callers in the substitution lemma will :use it with
; the right instantiation to drive the swap in the intended direction.
(defthm permutation-swap
  (implies (and (envp g) (exprp e)
                (symbolp v1) (stypep t1)
                (symbolp v2) (stypep t2)
                (not (equal v1 v2)))
           (equal (type-check (cons (cons v1 t1) (cons (cons v2 t2) g)) e)
                  (type-check (cons (cons v2 t2) (cons (cons v1 t1) g)) e)))
  :hints (("Goal"
           :use ((:instance type-check-context-independent
                            (g1 (cons (cons v1 t1) (cons (cons v2 t2) g)))
                            (g2 (cons (cons v2 t2) (cons (cons v1 t1) g))))
                 (:instance env-agree-on-swap
                            (vars (free-vars e))))))
  :rule-classes nil)


; TODO: substitution lemma (the hard one)
; if Γ,v:T1 ⊢ body : T2 and ⊢ val : T1 with val closed, then Γ ⊢ [v|->val]body : T2
; (defthm substitution-lemma
;   (implies (and (force (equal (type-check (cons (cons v t1) g) body) t2))
;                 (force (equal (type-check nil val) t1))
;                 (force (equal (free-vars val) nil))
;                 (force t2))
;            (equal (type-check g (stlc-subst v val body)) t2)))

(defthm type-check-closed
    (implies (and (envp g) (exprp e)
                  (equal (free-vars e) nil)
                  (type-check nil e))
             (equal (type-check g e) (type-check nil e)))
  :hints (("Goal"
           :use ((:instance type-check-context-independent
                            (g1 nil) (g2 g)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


;;;;                               PART 4e.2: SUBSTITUTION — PER-CONSTRUCTOR

                                        ; substitution on 'True: identity. both sides are 'Bool. one-liner.
(defthm substitution-true
    (implies (and (envp g) (exprp val) (symbolp v)
                  (equal (free-vars val) nil)
                  (type-check nil val))
             (equal (type-check g (stlc-subst v val 'True))
                    (type-check (cons (cons v (type-check nil val)) g) 'True)))
  :rule-classes nil)

                                        ; substitution on 'False: identity. symmetric.
(defthm substitution-false
    (implies (and (envp g) (exprp val) (symbolp v)
                  (equal (free-vars val) nil)
                  (type-check nil val))
             (equal (type-check g (stlc-subst v val 'False))
                    (type-check (cons (cons v (type-check nil val)) g) 'False)))
  :rule-classes nil)

                                        ; substitution on (Var w): two subcases hidden in stlc-subst's if.
                                        ; subcase w = v: stlc-subst returns val; (type-check nil val) is t1;
                                        ;   conclusion is (type-check g val) = t1. type-check-closed handles it.
                                        ; subcase w ≠ v: stlc-subst returns (Var w); both lookups bypass the
                                        ;   v:t1 binding and hit g directly.
                                        ; both subcases close by type-check unfolding on Var and the helpers.
(defthm substitution-var
    (implies (and (envp g) (exprp val) (symbolp v) (symbolp w)
                  (equal (free-vars val) nil)
                  (type-check nil val))
             (equal (type-check g (stlc-subst v val (list 'Var w)))
                    (type-check (cons (cons v (type-check nil val)) g)
                                (list 'Var w))))
  :rule-classes nil)


; substitution on (App f a): apply IH on f and a separately.
; type-check unfolds on App: need (type-check g [v|->val]f) to be a
; (Fun argty resty), and (type-check g [v|->val]a) to match argty.
; the IHs give us that these equal the corresponding type-checks under
; (v:t1 . g), which is precisely what the RHS needs.
(defthm substitution-app
  (implies (and (envp g) (exprp val) (exprp f) (exprp a) (symbolp v)
                (equal (free-vars val) nil)
                (type-check nil val)
                ; IHs — the inductive content, stated as hypotheses
                (equal (type-check g (stlc-subst v val f))
                       (type-check (cons (cons v (type-check nil val)) g) f))
                (equal (type-check g (stlc-subst v val a))
                       (type-check (cons (cons v (type-check nil val)) g) a)))
           (equal (type-check g (stlc-subst v val (list 'App f a)))
                  (type-check (cons (cons v (type-check nil val)) g)
                              (list 'App f a))))
  :rule-classes nil)

; substitution on (If c thn els): apply IH on all three subterms.
; the case analysis inside type-check (is cond bool? is thn-type = els-type?)
; doesn't matter — we're showing the WHOLE type-check is preserved, and
; the IHs give us that each subterm's type is preserved.
(defthm substitution-if
  (implies (and (envp g) (exprp val) (exprp c) (exprp thn) (exprp els)
                (symbolp v)
                (equal (free-vars val) nil)
                (type-check nil val)
                (equal (type-check g (stlc-subst v val c))
                       (type-check (cons (cons v (type-check nil val)) g) c))
                (equal (type-check g (stlc-subst v val thn))
                       (type-check (cons (cons v (type-check nil val)) g) thn))
                (equal (type-check g (stlc-subst v val els))
                       (type-check (cons (cons v (type-check nil val)) g) els)))
           (equal (type-check g (stlc-subst v val (list 'If c thn els)))
                  (type-check (cons (cons v (type-check nil val)) g)
                              (list 'If c thn els))))
  :rule-classes nil)


                                        ; substitution on (Lam w tw inner): two subcases.
                                        ;
                                        ; subcase w = v: stlc-subst returns (Lam v tw inner) unchanged (binder
                                        ;   shadows substituted var). RHS typechecks (Lam v tw inner) under
                                        ;   (v:t1 . g); this reduces to typing inner under (v:tw . v:t1 . g).
                                        ;   LHS typechecks (Lam v tw inner) under g; reduces to typing inner
                                        ;   under (v:tw . g). type-check-shadow collapses the redundant v:t1.
                                        ;
                                        ; subcase w ≠ v: the real inductive case. RHS wants inner typed under
                                        ;   (w:tw . v:t1 . g); we have IH on inner under (v:t1 . w:tw . g).
                                        ;   permutation-swap bridges them.
                                        ;
                                        ; hypothesis: IH on inner, under g extended by (w:tw). this is
                                        ;   precisely what subst-lemma-ind's Lam case gives us.

(defthm substitution-lam
  (implies (and (envp g) (exprp val) (exprp inner)
                (symbolp v) (symbolp w) (stypep tw)
                (equal (free-vars val) nil)
                (type-check nil val)
                (equal (type-check (cons (cons w tw) g) (stlc-subst v val inner))
                       (type-check (cons (cons v (type-check nil val))
                                         (cons (cons w tw) g))
                                   inner)))
           (equal (type-check g (stlc-subst v val (list 'Lam w tw inner)))
                  (type-check (cons (cons v (type-check nil val)) g)
                              (list 'Lam w tw inner))))
  :hints (("Goal"
           :cases ((equal v w))
           :in-theory (disable type-check)
           :expand ((type-check g (list 'Lam w tw (stlc-subst v val inner)))
                    (type-check g (list 'Lam w tw inner))
                    (type-check (cons (cons v (type-check nil val)) g)
                                (list 'Lam w tw inner))
                    (stlc-subst v val (list 'Lam w tw inner))))
          ("Subgoal 2"  ; the (not (equal v w)) case
           :use ((:instance permutation-swap
                            (g g)
                            (v1 w) (t1 tw)
                            (v2 v) (t2 (type-check nil val))
                            (e inner)))))
  :rule-classes nil)
; TODO: preservation
; (defthm preservation
;   (implies (and (type-check nil e) (stlc-step e))
;            (equal (type-check nil (stlc-step e)) (type-check nil e))))

; TODO: progress
; (defthm progress
;   (implies (type-check nil e)
;            (or (valuep e) (stlc-step e))))
