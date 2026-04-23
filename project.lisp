; STLC Type Soundness in ACL2s
; Christopher Wright-Williams & Zheng Wangyuan (Patrick)
; CS4820 — Professor Manolios

(in-package "ACL2S")

;;;;                                         PART 1: DATA DEFINITIONS

(defdata stype
  (oneof 'Bool
         (list 'Fun stype stype)))

(defdata expr
  (oneof 'True
         'False
         (list 'Var symbol)
         (list 'Lam symbol stype expr)
         (list 'App expr expr)
         (list 'If expr expr expr)))

(defdata env (alistof symbol stype))

;;;;                                         PART 2: TYPING RELATION

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

(definec valuep (e :expr) :bool
  (match e
    ('True t)
    ('False t)
    (('Lam & & &) t)
    (& nil)))

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

(definec mk-lam (v :symbol ty :stype body :expr) :expr
  (list 'Lam v ty body))

(definec mk-app (f :expr a :expr) :expr
  (list 'App f a))

(definec mk-if (c :expr thn :expr els :expr) :expr
  (list 'If c thn els))

(definec stlc-subst (v :symbol val :expr e :expr) :expr
  (cond
    ((equal (expr-tag e) 'True)  e)
    ((equal (expr-tag e) 'False) e)
    ((equal (expr-tag e) 'Var)
     (if (equal (var-name e) v) val e))
    ((equal (expr-tag e) 'Lam)
     (if (equal (lam-var e) v)
         e
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

(definec stlc-step (e :expr) :all
  :skip-body-contractsp t
  (cond
    ((valuep e) nil)
    ((equal (expr-tag e) 'App)
     (let ((f (app-fun e))
           (a (app-arg e)))
       (cond
         ((not (valuep f))
          (let ((f2 (stlc-step f)))
            (if f2 (mk-app f2 a) nil)))
         ((not (valuep a))
          (let ((a2 (stlc-step a)))
            (if a2 (mk-app f a2) nil)))
         ((equal (expr-tag f) 'Lam)
          (stlc-subst (lam-var f) a (lam-body f)))
         (t nil))))
    ((equal (expr-tag e) 'If)
     (let ((c (if-cond e))
           (thn (if-then e))
           (els (if-else e)))
       (cond
         ((equal c 'True)  thn)
         ((equal c 'False) els)
         ((not (valuep c))
          (let ((c2 (stlc-step c)))
            (if c2 (mk-if c2 thn els) nil)))
         (t nil))))
    (t nil)))

;;;;                               PART 4a: ENV-AGREE-ON

(definec env-agree-on (g1 :env g2 :env vars :tl) :bool
  (if (endp vars)
      t
    (and (equal (cdr (assoc-equal (car vars) g1))
                (cdr (assoc-equal (car vars) g2)))
         (env-agree-on g1 g2 (cdr vars)))))

(defthm env-agree-on-refl
  (implies (and (envp g) (tlp vars))
           (env-agree-on g g vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm env-agree-on-assoc
  (implies (and (envp g1) (envp g2) (tlp vars)
                (env-agree-on g1 (double-rewrite g2) (double-rewrite vars))
                (member-equal v vars))
           (equal (cdr (assoc-equal v g1))
                  (cdr (assoc-equal v g2))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm env-agree-on-subsetp
  (implies (and (envp g1) (envp g2) (tlp vars) (tlp vars2)
                (env-agree-on g1 g2 vars)
                (subsetp-equal (double-rewrite vars2) (double-rewrite vars)))
           (env-agree-on g1 g2 vars2))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm env-agree-on-cons-both
  (implies (and (envp g1) (envp g2) (tlp vars)
                (symbolp v) (stypep ty)
                (env-agree-on g1 g2 (remove-equal v vars)))
           (env-agree-on (cons (cons v ty) g1)
                         (cons (cons v ty) g2)
                         vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;;;                               PART 4b: LIST-THEORY HELPERS

(defthm subsetp-remove-equal
  (subsetp-equal (remove-equal v vars) vars))

(defthm subsetp-union-equal-left
  (subsetp-equal vs1 (union-equal vs1 vs2)))

(defthm subsetp-union-equal-right
  (implies (tlp vs2)
           (subsetp-equal vs2 (union-equal vs1 vs2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;;;                               PART 4c: CONTEXT-INDEPENDENCE

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

(defthm env-agree-on-union-left
    (implies (and (envp g1) (envp g2)
                  (tlp vs1) (tlp vs2)
                  (env-agree-on g1 g2 (union-equal vs1 vs2)))
             (env-agree-on g1 g2 vs1))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((env-agree-on g1 g2 (union-equal vs1 vs2))))))

(defthm env-agree-on-union-right
    (implies (and (envp g1) (envp g2)
                  (tlp vs1) (tlp vs2)
                  (env-agree-on g1 g2 (union-equal vs1 vs2)))
             (env-agree-on g1 g2 vs2))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((env-agree-on g1 g2 (union-equal vs1 vs2))))))
(defthm type-check-context-independent
  (implies (and (envp g1) (envp g2) (exprp e)
                (env-agree-on g1 g2 (free-vars e)))
           (equal (type-check g1 e) (type-check g2 e)))
  :hints (("Goal" :induct (ctx-indep-ind g1 g2 e)))
  :rule-classes nil)

;;;;                               PART 4d: WEAKENING AND PERMUTATION

(defthm env-agree-on-cons-irrelevant
  (implies (and (envp g) (tlp vars)
                (symbolp v) (stypep tv)
                (not (member-equal v (double-rewrite vars))))
           (env-agree-on g (cons (cons v tv) g) vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm env-agree-on-sym
    (implies (and (envp g1) (envp g2) (tlp vars)
                  (env-agree-on g1 g2 vars))
             (env-agree-on g2 g1 vars))
  :hints (("Goal" :induct (env-agree-on g1 g2 vars)
                  :in-theory (enable env-agree-on)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm env-agree-on-swap
  (implies (and (envp g) (tlp vars)
                (symbolp v1) (stypep t1)
                (symbolp v2) (stypep t2)
                (not (equal v1 v2)))
           (env-agree-on (cons (cons v1 t1) (cons (cons v2 t2) g))
                         (cons (cons v2 t2) (cons (cons v1 t1) g))
                         vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

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

;;;;                               PART 4e: SUBSTITUTION LEMMA

(defthm type-check-closed
  (implies (and (envp g) (exprp e)
                (equal (free-vars e) nil)
                (type-check nil e))
           (equal (type-check g e) (type-check nil e)))
  :hints (("Goal"
           :use ((:instance type-check-context-independent
                            (g1 nil) (g2 g)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm type-check-is-stype
    (implies (and (envp g) (exprp e) (type-check g e))
             (stypep (type-check g e)))
  :hints (("Goal" :induct (type-check g e)))
  :rule-classes ((:forward-chaining 
                  :trigger-terms ((type-check g e)))))

;;;;                               PART 4e.0: SHADOWING HELPERS

; env-agree-on-cons-shadow: with (v . tw) already on top, prepending
; another (v . t1) is invisible. any v-lookup terminates on tw in both
; envs; any other lookup skips past (v . tw) and hits g identically
; (on the RHS directly, on the LHS after also skipping (v . t1)).
; induction on vars; case-split on car vars ∈ {v, other}.
(defthm env-agree-on-cons-shadow
  (implies (and (envp g) (tlp vars)
                (symbolp v) (stypep tw) (stypep t1))
           (env-agree-on (cons (cons v tw) (cons (cons v t1) g))
                         (cons (cons v tw) g)
                         vars))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; type-check-shadow: a shadowed binding disappears under type-check.
; needed for the Lam w=v subcase of substitution, where v shadows v.
; same two-:use pattern as weakening and permutation-swap.
(defthm type-check-shadow
  (implies (and (envp g) (exprp e)
                (symbolp v) (stypep tw) (stypep t1))
           (equal (type-check (cons (cons v tw) (cons (cons v t1) g)) e)
                  (type-check (cons (cons v tw) g) e)))
  :hints (("Goal"
           :use ((:instance type-check-context-independent
                            (g1 (cons (cons v tw) (cons (cons v t1) g)))
                            (g2 (cons (cons v tw) g)))
                 (:instance env-agree-on-cons-shadow
                            (vars (free-vars e))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm type-check-lam-var-irrelevant
    (implies (and (envp g) (exprp body) (consp body)
                  (equal (car body) 'Lam)
                  (stypep tv))
             (equal (type-check g body)
                    (type-check (cons (cons (cadr body) tv) g) body)))
  :hints (("Goal"
           :use ((:instance type-check-context-independent
                            (g1 g)
                            (g2 (cons (cons (cadr body) tv) g)))
                 (:instance env-agree-on-cons-irrelevant
                            (v (cadr body))
                            (vars (free-vars body))
                            (tv tv))
                 (:instance env-agree-on-sym
                            (g1 g)
                            (g2 (cons (cons (cadr body) tv) g))
                            (vars (free-vars body))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; custom induction scheme: extends g by (w.tw) in the Lam case
; so the IH has the right env shape for substitution-lam-rw to fire
(set-ld-redefinition-action '(:doit . :overwrite) state)

(defun subst-lemma-ind (g v val body)
  (declare (xargs :measure (acl2-count body))
           (ignorable g v val))
  (cond
    ((or (equal body 'True) (equal body 'False)) 0)
    ((atom body) 0)
    ((equal (car body) 'Var) 0)
    ((equal (car body) 'Lam)
     (if (equal (cadr body) v)
         0
         (+ 1 (subst-lemma-ind (cons (cons (cadr body) (caddr body)) g)
                               v val (cadddr body)))))
    ((equal (car body) 'App)
     (+ 1 (subst-lemma-ind g v val (cadr body))
        (subst-lemma-ind g v val (caddr body))))
    ((equal (car body) 'If)
     (+ 1 (subst-lemma-ind g v val (cadr body))
        (subst-lemma-ind g v val (caddr body))
        (subst-lemma-ind g v val (cadddr body))))
    (t 0)))

(set-ld-redefinition-action nil state)

; per-constructor type-check openers: unfold type-check on a known
; constructor shape without enabling the whole function
(defthm type-check-lam-open
  (implies (and (envp g) (symbolp w) (stypep tw) (exprp inner))
           (equal (type-check g (list 'Lam w tw inner))
                  (let ((bt (type-check (cons (cons w tw) g) inner)))
                    (if bt (list 'Fun tw bt) nil))))
  :hints (("Goal" :expand (type-check g (list 'Lam w tw inner))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm type-check-app-open
  (implies (and (envp g) (exprp f) (exprp a))
           (equal (type-check g (list 'App f a))
                  (let ((ft (type-check g f))
                        (at (type-check g a)))
                    (if (and ft at (consp ft)
                             (equal (car ft) 'Fun)
                             (equal (cadr ft) at))
                        (caddr ft) nil))))
  :hints (("Goal" :expand (type-check g (list 'App f a))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm type-check-if-open
  (implies (and (envp g) (exprp c) (exprp thn) (exprp els))
           (equal (type-check g (list 'If c thn els))
                  (let ((ct (type-check g c))
                        (tt (type-check g thn))
                        (et (type-check g els)))
                    (if (and (equal ct 'Bool) tt (equal tt et))
                        tt nil))))
  :hints (("Goal" :expand (type-check g (list 'If c thn els))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm type-check-var-open
  (implies (and (envp g) (symbolp w))
           (equal (type-check g (list 'Var w))
                  (cdr (assoc-equal w g))))
  :hints (("Goal" :expand (type-check g (list 'Var w))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; permutation-swap as a rewrite rule: the key fix for the Lam case
; of substitution-lemma. without this the env order mismatch between
; the IH and the goal can't be bridged automatically.
(defthm permutation-swap-rw
  (implies (and (envp g) (exprp e)
                (symbolp v1) (stypep t1)
                (symbolp v2) (stypep t2)
                (not (equal v1 v2)))
           (equal (type-check (cons (cons v1 t1) (cons (cons v2 t2) g)) e)
                  (type-check (cons (cons v2 t2) (cons (cons v1 t1) g)) e)))
  :hints (("Goal" :use ((:instance permutation-swap))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm substitution-lemma
  (implies (and (envp g) (exprp val) (exprp body)
                (symbolp v)
                (equal (free-vars val) nil)
                (type-check nil val))
           (equal (type-check g (stlc-subst v val body))
                  (type-check (cons (cons v (type-check nil val)) g) body)))
  :hints (("Goal"
           :induct (subst-lemma-ind g v val body)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;;;                               PART 4f: PRESERVATION

(defthm member-of-union-equal
  (iff (member-equal a (union-equal x y))
       (or (member-equal a x) (member-equal a y))))

(defthm union-equal-nil-implies-left
  (implies (and (tlp x)
                (equal (union-equal x y) nil))
           (equal x nil))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((union-equal x y)))))

(defthm union-equal-nil-implies-right
  (implies (equal (union-equal x y) nil)
           (equal y nil))
  :hints (("Goal"
           :use ((:instance member-of-union-equal
                            (a (car y))))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((union-equal x y)))))

(defthm closed-app-parts
  (implies (and (exprp e) (consp e)
                (equal (car e) 'App)
                (equal (free-vars e) nil))
           (and (equal (free-vars (cadr e)) nil)
                (equal (free-vars (caddr e)) nil)))
  :hints (("Goal" :expand (free-vars e)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm closed-if-parts
  (implies (and (exprp e) (consp e)
                (equal (car e) 'If)
                (equal (free-vars e) nil))
           (and (equal (free-vars (cadr e)) nil)
                (equal (free-vars (caddr e)) nil)
                (equal (free-vars (cadddr e)) nil)))
  :hints (("Goal"
           :expand (free-vars e)
           :use ((:instance union-equal-nil-implies-left
                            (x (free-vars (cadr e)))
                            (y (union-equal (free-vars (caddr e))
                                            (free-vars (cadddr e)))))
                 (:instance union-equal-nil-implies-left
                            (x (free-vars (caddr e)))
                            (y (free-vars (cadddr e))))
                 (:instance union-equal-nil-implies-right
                            (x (free-vars (caddr e)))
                            (y (free-vars (cadddr e)))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm stlc-step-exprp
  (implies (and (exprp e) (stlc-step e))
           (exprp (stlc-step e)))
  :hints (("Goal" :induct (stlc-step e)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining
                  :trigger-terms ((stlc-step e)))))

(defthm remove-equal-union-nil-implies-free-vars-nil
  (implies (and (tlp (free-vars body))
                (equal (union-equal (remove-equal v (free-vars body)) y) nil))
           (equal y nil))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((union-equal (remove-equal v (free-vars body)) y)))))

(defthm preservation-if-true
  (implies (and (exprp thn) (exprp els)
                (type-check nil (list 'If 'True thn els)))
           (equal (type-check nil thn)
                  (type-check nil (list 'If 'True thn els))))
  :hints (("Goal" :expand (type-check nil (list 'If 'True thn els))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation-if-false
  (implies (and (exprp thn) (exprp els)
                (type-check nil (list 'If 'False thn els)))
           (equal (type-check nil els)
                  (type-check nil (list 'If 'False thn els))))
  :hints (("Goal" :expand (type-check nil (list 'If 'False thn els))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation-if-cond
  (implies (and (exprp c) (exprp thn) (exprp els)
                (exprp (stlc-step c))
                (type-check nil (list 'If c thn els))
                (stlc-step c)
                (equal (type-check nil (stlc-step c))
                       (type-check nil c)))
           (equal (type-check nil (list 'If (stlc-step c) thn els))
                  (type-check nil (list 'If c thn els))))
  :hints (("Goal"
           :expand ((type-check nil (list 'If c thn els))
                    (type-check nil (list 'If (stlc-step c) thn els)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation-app1
  (implies (and (exprp f) (exprp a)
                (type-check nil (list 'App f a))
                (stlc-step f)
                (equal (type-check nil (stlc-step f))
                       (type-check nil f)))
           (equal (type-check nil (list 'App (stlc-step f) a))
                  (type-check nil (list 'App f a))))
  :hints (("Goal"
           :expand ((type-check nil (list 'App f a))
                    (type-check nil (list 'App (stlc-step f) a)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation-app2
  (implies (and (exprp f) (exprp a)
                (type-check nil (list 'App f a))
                (stlc-step a)
                (equal (type-check nil (stlc-step a))
                       (type-check nil a)))
           (equal (type-check nil (list 'App f (stlc-step a)))
                  (type-check nil (list 'App f a))))
  :hints (("Goal"
           :expand ((type-check nil (list 'App f a))
                    (type-check nil (list 'App f (stlc-step a))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation-app-abs
  (implies (and (exprp a) (symbolp v) (stypep ty) (exprp body)
                (equal (free-vars a) nil)
                (type-check nil (list 'App (list 'Lam v ty body) a)))
           (equal (type-check nil (stlc-subst v a body))
                  (type-check nil (list 'App (list 'Lam v ty body) a))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance substitution-lemma
                            (g nil)
                            (val a)
                            (body body)))
           :expand ((type-check nil (list 'App (list 'Lam v ty body) a))
                    (type-check nil (list 'Lam v ty body)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm preservation
  (implies (and (exprp e)
                (equal (free-vars e) nil)
                (type-check nil e)
                (stlc-step e))
           (equal (type-check nil (stlc-step e))
                  (type-check nil e)))
  :hints (("Goal"
           :induct (stlc-step e)
           :do-not '(generalize eliminate-destructors))
          ("Subgoal *1/6'''"
           :use ((:instance preservation-if-false
                             (thn (caddr e))
                             (els (cadddr e)))))
          ("Subgoal *1/5'''"
           :use ((:instance preservation-if-true
                             (thn (caddr e))
                             (els (cadddr e)))))
          ("Subgoal *1/4.2.3'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e)))
          ("Subgoal *1/4.2.2'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e)))
          ("Subgoal *1/4.2.1'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e)))
          ("Subgoal *1/4.1.3'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e)))
          ("Subgoal *1/4.1.2'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e)))
          ("Subgoal *1/4.1.1'"
           :use ((:instance preservation-app-abs
                             (v (cadr (cadr e)))
                             (ty (caddr (cadr e)))
                             (body (cadddr (cadr e)))
                             (a (caddr e))))
           :expand ((type-check nil (cadr e))
                    (type-check nil e))))
  :rule-classes nil)
; TODO: progress
;;;;                               PART 5: PROGRESS

;; Canonical forms: values of known types

(defthm canonical-bool
  (implies (and (exprp e)
                (valuep e)
                (equal (free-vars e) nil)
                (equal (type-check nil e) 'Bool))
           (or (equal e 'True) (equal e 'False)))
  :hints (("Goal" :in-theory (enable valuep type-check free-vars)))
  :rule-classes nil)

(defthm canonical-fun
  (implies (and (exprp e)
                (valuep e)
                (equal (free-vars e) nil)
                (consp (type-check nil e))
                (equal (car (type-check nil e)) 'Fun))
           (and (consp e) (equal (car e) 'Lam)))
  :hints (("Goal" :in-theory (enable valuep type-check free-vars)))
  :rule-classes nil)

;; mk-* expressions are always truthy (consp => non-nil)

(defthm mk-app-non-nil
    (implies (and (exprp f) (exprp a))
             (mk-app f a))
  :hints (("Goal" :expand (mk-app f a)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm mk-if-non-nil
    (implies (and (exprp c) (exprp thn) (exprp els))
             (mk-if c thn els))
  :hints (("Goal" :expand (mk-if c thn els)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
;; stlc-subst always returns a non-nil expr

(defthm stlc-subst-non-nil
  (implies (and (symbolp v) (exprp val) (exprp body))
           (stlc-subst v val body))
  :hints (("Goal" :induct (stlc-subst v val body)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining
                  :trigger-terms ((stlc-subst v val body)))))

;; App sub-expressions are well-typed when the App is

(defthm type-check-app-fun-typed
  (implies (and (exprp f) (exprp a)
                (type-check nil (list 'App f a)))
           (and (type-check nil f)
                (type-check nil a)
                (consp (type-check nil f))
                (equal (car (type-check nil f)) 'Fun)
                (equal (cadr (type-check nil f)) (type-check nil a))))
  :hints (("Goal" :expand (type-check nil (list 'App f a))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining
                  :trigger-terms ((type-check nil (list 'App f a))))))

;; If sub-expressions are well-typed when the If is

(defthm type-check-if-parts-typed
  (implies (and (exprp c) (exprp thn) (exprp els)
                (type-check nil (list 'If c thn els)))
           (and (equal (type-check nil c) 'Bool)
                (type-check nil thn)
                (type-check nil els)))
  :hints (("Goal" :expand (type-check nil (list 'If c thn els))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining
                  :trigger-terms ((type-check nil (list 'If c thn els))))))

;; Closed If/App propagate closure to parts (restatements for FC use)

(defthm closed-app-fun
  (implies (and (exprp e) (consp e)
                (equal (car e) 'App)
                (equal (free-vars e) nil))
           (equal (free-vars (cadr e)) nil))
  :hints (("Goal" :use closed-app-parts))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining :trigger-terms ((free-vars e)))))

(defthm closed-app-arg
  (implies (and (exprp e) (consp e)
                (equal (car e) 'App)
                (equal (free-vars e) nil))
           (equal (free-vars (caddr e)) nil))
  :hints (("Goal" :use closed-app-parts))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining :trigger-terms ((free-vars e)))))

(defthm closed-if-cond-part
  (implies (and (exprp e) (consp e)
                (equal (car e) 'If)
                (equal (free-vars e) nil))
           (equal (free-vars (cadr e)) nil))
  :hints (("Goal" :use closed-if-parts))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining :trigger-terms ((free-vars e)))))

;; Progress

(defthm value-does-not-step
    (implies (and (exprp e) (valuep e))
             (not (stlc-step e)))
  :hints (("Goal" :expand (stlc-step e)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 (:forward-chaining :trigger-terms ((valuep e)))))

(defthm progress-app
    (implies (and (exprp f) (exprp a)
                  (equal (free-vars (list 'App f a)) nil)
                  (type-check nil (list 'App f a))
                  (or (valuep f) (stlc-step f))
                  (or (valuep a) (stlc-step a)))
             (stlc-step (list 'App f a)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((stlc-step (list 'App f a))
                    (free-vars (list 'App f a)))
           :use ((:instance canonical-fun (e f))
                 (:instance closed-app-parts
                            (e (list 'App f a))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm progress-if
    (implies (and (exprp c) (exprp thn) (exprp els)
                  (equal (free-vars (list 'If c thn els)) nil)
                  (type-check nil (list 'If c thn els))
                  (or (valuep c) (stlc-step c)))
             (stlc-step (list 'If c thn els)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((stlc-step (list 'If c thn els))
                    (free-vars (list 'If c thn els)))
           :use ((:instance canonical-bool (e c)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defun progress-ind (e)
  (declare (xargs :measure (acl2-count e))
           (ignorable e))
  (cond
    ((or (equal e 'True) (equal e 'False)) 0)
    ((atom e) 0)
    ((equal (car e) 'Lam) 0)
    ((equal (car e) 'App)
     (+ 1 (progress-ind (cadr e))
        (progress-ind (caddr e))))
    ((equal (car e) 'If)
     (+ 1 (progress-ind (cadr e))))
    (t 0)))

(defthm progress
  (implies (and (exprp e)
                (equal (free-vars e) nil)
                (type-check nil e))
           (or (valuep e)
               (stlc-step e)))
  :hints (("Goal"
           :induct (progress-ind e)
           :do-not '(generalize eliminate-destructors))
          ("Subgoal *1/2"
           :use ((:instance progress-app
                             (f (cadr e))
                             (a (caddr e)))))
          ("Subgoal *1/5"
           :use ((:instance progress-if
                             (c (cadr e))
                             (thn (caddr e))
                             (els (cadddr e)))
                 (:instance canonical-bool (e (cadr e)))
                 (:instance value-does-not-step (e (cadr e)))))
          ("Subgoal *1/1"
           :use ((:instance progress-if
                             (c (cadr e))
                             (thn (caddr e))
                             (els (cadddr e)))
                 (:instance canonical-bool (e (cadr e)))
                 (:instance value-does-not-step (e (cadr e))))))
  :rule-classes nil)
