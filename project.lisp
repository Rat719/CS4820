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

;;;; PART 3: VALUES AND SMALL-STEP EVALUATION
;;;; ============================================================

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

; TODO: fresh-var
; needs a valid termination measure — appending primes doesn't work
; idea: use a nat counter suffix instead of primes
; (defun fresh-var (base used) ...)

; TODO: subst-expr — capture-avoiding substitution [v |-> val] e
; depends on fresh-var
; tricky case: (Lam u T body) where u is free in val — need to alpha-rename
; (definec subst-expr (v :symbol val :expr e :expr) :expr ...)

; TODO: step — single step of call-by-value evaluation, nil if stuck/value
; depends on subst-expr
; cases: E-AppAbs, E-App1, E-App2, E-IfTrue, E-IfFalse, E-IfCond
; (definec step (e :expr) :all ...)

;;;; PART 4: TYPE SOUNDNESS
;;;; ============================================================


; TODO: env-agree-on helper (needed for permutation)
; (defun env-agree-on (g1 g2 vars) ...)

; TODO: env-subst helper (needed for alpha-renaming)
; (defun env-subst (v1 v2 g) ...)

; TODO: weakening
; if v not free in e, adding v:tv to g doesn't change the type of e
; (defthm weakening
;   (implies (and (force (type-check g e))
;                 (force (not (member-equal v (free-vars e)))))
;            (equal (type-check (cons (cons v tv) g) e)
;                   (type-check g e)))
;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

; TODO: permutation
; same bindings for free vars = same type
; (defthm permutation
;   (implies (and (force (type-check g1 e))
;                 (force (env-agree-on g1 g2 (free-vars e))))
;            (equal (type-check g2 e) (type-check g1 e)))
;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

; TODO: alpha-renaming
; renaming a bound variable preserves typing
; (defthm alpha-renaming
;   (implies (and (force (type-check g e))
;                 (force (not (member-equal v2 (free-vars e)))))
;            (equal (type-check (env-subst v1 v2 g)
;                               (subst-expr v1 (list 'Var v2) e))
;                   (type-check g e)))
;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

; TODO: substitution lemma — key lemma for preservation
; if Γ,v:T1 ⊢ body : T2 and Γ ⊢ val : T1 then Γ ⊢ [v|->val]body : T2
; (defthm substitution-lemma
;   (implies (and (force (equal (type-check (cons (cons v t1) g) body) t2))
;                 (force (equal (type-check g val) t1))
;                 (force t2))
;            (equal (type-check g (subst-expr v val body)) t2)))

; TODO: preservation
; if Γ ⊢ e : T and e steps, then Γ ⊢ e' : T
; E-AppAbs case uses substitution-lemma, rest by induction
; (defthm preservation
;   (implies (and (type-check g e) (step e))
;            (equal (type-check g (step e)) (type-check g e))))

; TODO: progress
; if ⊢ e : T then e is a value or it can step
; (defthm progress
;   (implies (type-check nil e)
;            (or (valuep e) (step e))))


;;; Type inference 
