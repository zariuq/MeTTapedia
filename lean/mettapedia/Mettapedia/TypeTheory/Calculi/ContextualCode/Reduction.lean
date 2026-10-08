import Mettapedia.TypeTheory.Calculi.ContextualCode.Syntax
import Mathlib.Logic.Relation

/-!
# Reduction of contextual code

The rules of the sealed-code calculus, with templates and matching.

* `beta`: `(λ b) a → b[a]`.
* `run`: `drop (cquote k M) → λ…λ M`. Running a template gives the function of
  its parameters; for `k = 0` this is running the code of a name.
* `runLift`: `drop (lift M) → M`.
* `name`: `lift V → cquote 0 V` when `V` is closed and normal. This is the only
  rule that makes code: substitution passes through `lift`, evaluation
  completes the code, and the closed normal form is sealed.
* `cmatch`: when the code of the template has the shape of the pattern, the
  handler receives the names of the pieces in the holes.

Reduction never enters a template.

The bracket `T[x := A]` is not a rule. It is the derived form `instAll`: run
the template, apply it to the runs of the names, and seal the result with
`lift`. `instAll_name` computes it, and `instAll_asWritten` shows that it
agrees with filling the template as written exactly when the filled code is
already normal; `lift_reaches_normal` shows that a name built by `lift` always
has normal code.

`Step.subst` shows that a step survives every substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-- Normal forms: no redex outside a template. A `lift` is normal only while
its code is open, since only the enclosing binders can still complete it. -/
inductive Normal : {n : Nat} → Term n → Prop where
  | var {n : Nat} (i : Fin n) : Normal (.var i)
  | sym {n : Nat} (s : String) : Normal (.sym s : Term n)
  | cquote {n : Nat} (k : Nat) (M : Term k) : Normal (.cquote k M : Term n)
  | lam {n : Nat} {b : Term (n + 1)} : Normal b → Normal (.lam b)
  | app {n : Nat} {f a : Term n} :
      Normal f → Normal a → (∀ b, f ≠ .lam b) → Normal (.app f a)
  | lift {n : Nat} {M : Term n} : Normal M → M.Open → Normal (.lift M)
  | drop {n : Nat} {K : Term n} :
      Normal K → (∀ (k : Nat) (M : Term k), K ≠ .cquote k M) → (∀ M, K ≠ .lift M) →
        Normal (.drop K)
  | cmatch {n m k : Nat} {K F : Term n} {P : Pat m k} :
      Normal K → Normal F → (∀ σ, P.Covers → K ≠ .cquote k (P.fill σ)) →
        Normal (.cmatch k K P F)

/-- One reduction step. -/
inductive Step : {n : Nat} → Term n → Term n → Prop where
  | beta {n : Nat} (b : Term (n + 1)) (a : Term n) : Step (.app (.lam b) a) (b.subst1 a)
  | run {n : Nat} (k : Nat) (M : Term k) :
      Step (.drop (.cquote k M) : Term n) (ofClosed (lamN k M))
  | runLift {n : Nat} (M : Term n) : Step (.drop (.lift M)) M
  | name {n : Nat} (V : Term 0) : Normal V → Step (.lift (ofClosed V) : Term n) (.cquote 0 V)
  | cmatch {n m k : Nat} (P : Pat m k) (σ : Fin m → Term 0) (F : Term n) : P.Covers →
      Step (.cmatch k (.cquote k (P.fill σ)) P F) (appsN F (fun j => .cquote 0 (σ j)))
  | lam {n : Nat} {b b' : Term (n + 1)} : Step b b' → Step (.lam b) (.lam b')
  | appL {n : Nat} {f f' a : Term n} : Step f f' → Step (.app f a) (.app f' a)
  | appR {n : Nat} {f a a' : Term n} : Step a a' → Step (.app f a) (.app f a')
  | lift {n : Nat} {M M' : Term n} : Step M M' → Step (.lift M) (.lift M')
  | drop {n : Nat} {K K' : Term n} : Step K K' → Step (.drop K) (.drop K')
  | cmatchL {n m k : Nat} {K K' F : Term n} {P : Pat m k} :
      Step K K' → Step (.cmatch k K P F) (.cmatch k K' P F)
  | cmatchR {n m k : Nat} {K F F' : Term n} {P : Pat m k} :
      Step F F' → Step (.cmatch k K P F) (.cmatch k K P F')

/-- Many steps. -/
abbrev Steps {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen (@Step n)

/-! ## Stability under substitution -/

/-- **A step stays a step under every substitution.** -/
theorem Step.subst {n : Nat} {M N : Term n} (h : Step M N) :
    ∀ {m : Nat} (σ : Sub n m), Step (M.subst σ) (N.subst σ) := by
  induction h with
  | beta b a =>
      intro m σ
      simp only [Term.subst]
      rw [subst_subst1]
      exact .beta _ _
  | run k M =>
      intro m σ
      simp only [Term.subst, subst_ofClosed]
      exact .run k M
  | runLift M => intro m σ; exact .runLift _
  | name V normal =>
      intro m σ
      simp only [Term.subst, subst_ofClosed]
      exact .name V normal
  | cmatch P τ F covers =>
      intro m σ
      rw [subst_appsN]
      exact .cmatch P τ _ covers
  | lam _ ih => intro m σ; exact .lam (ih _)
  | appL _ ih => intro m σ; exact .appL (ih _)
  | appR _ ih => intro m σ; exact .appR (ih _)
  | lift _ ih => intro m σ; exact .lift (ih _)
  | drop _ ih => intro m σ; exact .drop (ih _)
  | cmatchL _ ih => intro m σ; exact .cmatchL (ih _)
  | cmatchR _ ih => intro m σ; exact .cmatchR (ih _)

theorem Step.rename {n m : Nat} {M N : Term n} (h : Step M N) (ρ : Ren n m) :
    Step (M.rename ρ) (N.rename ρ) := by
  rw [← subst_ren, ← subst_ren]
  exact h.subst _

theorem Steps.subst {n m : Nat} {M N : Term n} (h : Steps M N) (σ : Sub n m) :
    Steps (M.subst σ) (N.subst σ) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst σ)

theorem Steps.rename {n m : Nat} {M N : Term n} (h : Steps M N) (ρ : Ren n m) :
    Steps (M.rename ρ) (N.rename ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.rename ρ)

/-! ## Congruence of many steps -/

theorem Steps.lam {n : Nat} {b b' : Term (n + 1)} (h : Steps b b') :
    Steps (.lam b) (.lam b') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.lam step)

theorem Steps.app {n : Nat} {f f' a a' : Term n} (hf : Steps f f') (ha : Steps a a') :
    Steps (.app f a) (.app f' a') := by
  have left : Steps (.app f a) (.app f' a) := by
    induction hf with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (.appL step)
  have right : Steps (.app f' a) (.app f' a') := by
    induction ha with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (.appR step)
  exact left.trans right

theorem Steps.lift {n : Nat} {M M' : Term n} (h : Steps M M') :
    Steps (.lift M) (.lift M') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.lift step)

theorem Steps.drop {n : Nat} {K K' : Term n} (h : Steps K K') :
    Steps (.drop K) (.drop K') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.drop step)

theorem Steps.cmatch {n m k : Nat} {K K' F F' : Term n} {P : Pat m k}
    (hK : Steps K K') (hF : Steps F F') : Steps (.cmatch k K P F) (.cmatch k K' P F') := by
  have left : Steps (.cmatch k K P F) (.cmatch k K' P F) := by
    induction hK with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (.cmatchL step)
  have right : Steps (.cmatch k K' P F) (.cmatch k K' P F') := by
    induction hF with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (.cmatchR step)
  exact left.trans right

theorem Steps.appsN {n k : Nat} {F F' : Term n} {a a' : Fin k → Term n} (hF : Steps F F')
    (ha : ∀ i, Steps (a i) (a' i)) : Steps (appsN F a) (appsN F' a') := by
  induction k with
  | zero => exact hF
  | succ k ih =>
      exact Steps.app (ih (fun i => ha i.castSucc)) (ha (Fin.last k))

/-! ## Shapes kept by renaming -/

theorem rename_eq_lam {n m : Nat} {ρ : Ren n m} {f : Term n} {b : Term (m + 1)}
    (h : f.rename ρ = .lam b) : ∃ b', f = .lam b' := by
  cases f with
  | lam b' => exact ⟨b', rfl⟩
  | _ => simp [Term.rename] at h

theorem rename_eq_cquote {n m k : Nat} {ρ : Ren n m} {K : Term n} {M : Term k}
    (h : K.rename ρ = .cquote k M) : K = .cquote k M := by
  cases K with
  | cquote k' M' =>
      simp only [Term.rename, Term.cquote.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_heq h]
  | _ => simp [Term.rename] at h

theorem rename_eq_lift {n m : Nat} {ρ : Ren n m} {K : Term n} {M : Term m}
    (h : K.rename ρ = .lift M) : ∃ M', K = .lift M' := by
  cases K with
  | lift M' => exact ⟨M', rfl⟩
  | _ => simp [Term.rename] at h

theorem cquote_inj {n k : Nat} {M M' : Term k} (h : (.cquote k M : Term n) = .cquote k M') :
    M = M' := by
  simp only [Term.cquote.injEq, heq_eq_eq, true_and] at h
  exact h

/-! ## Normal forms -/

/-- Renaming keeps a term normal. -/
theorem Normal.rename {n : Nat} {M : Term n} (h : Normal M) :
    ∀ {m : Nat} (ρ : Ren n m), Normal (M.rename ρ) := by
  induction h with
  | var i => intro m ρ; exact .var _
  | sym s => intro m ρ; exact .sym s
  | cquote k M => intro m ρ; exact .cquote k M
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | app _ _ notLam ihf iha =>
      intro m ρ
      refine .app (ihf ρ) (iha ρ) ?_
      intro b hb
      obtain ⟨b', rfl⟩ := rename_eq_lam hb
      exact notLam b' rfl
  | lift _ isOpen ih =>
      intro m ρ
      exact .lift (ih ρ) ((open_rename ρ _).mpr isOpen)
  | drop _ notQuote notLift ih =>
      intro m ρ
      refine .drop (ih ρ) ?_ ?_
      · intro k M hM
        exact notQuote k M (rename_eq_cquote hM)
      · intro M hM
        obtain ⟨M', rfl⟩ := rename_eq_lift hM
        exact notLift M' rfl
  | cmatch _ _ noMatch ihK ihF =>
      intro m ρ
      refine .cmatch (ihK ρ) (ihF ρ) ?_
      intro σ covers hK
      exact noMatch σ covers (rename_eq_cquote hK)

theorem Normal.ofClosed {n : Nat} {M : Term 0} (h : Normal M) :
    Normal (Term.ofClosed M : Term n) :=
  h.rename _

/-- **A normal term does not step.** -/
theorem Normal.no_step {n : Nat} {M : Term n} (h : Normal M) : ∀ N, ¬ Step M N := by
  induction h with
  | var i => intro N step; cases step
  | sym s => intro N step; cases step
  | cquote k M => intro N step; cases step
  | lam _ ih =>
      intro N step
      cases step with
      | lam inner => exact ih _ inner
  | app _ _ notLam ihf iha =>
      intro N step
      cases step with
      | beta b a => exact notLam b rfl
      | appL inner => exact ihf _ inner
      | appR inner => exact iha _ inner
  | lift _ isOpen ih =>
      intro N step
      cases step with
      | name V _ => exact not_open_ofClosed V isOpen
      | lift inner => exact ih _ inner
  | drop _ notQuote notLift ih =>
      intro N step
      cases step with
      | run k M₀ => exact notQuote k M₀ rfl
      | runLift => exact notLift _ rfl
      | drop inner => exact ih _ inner
  | cmatch _ _ noMatch ihK ihF =>
      intro N step
      cases step with
      | cmatch P σ F covers => exact noMatch σ covers rfl
      | cmatchL inner => exact ihK _ inner
      | cmatchR inner => exact ihF _ inner

/-- A template does not step. -/
theorem cquote_no_step {n k : Nat} (M : Term k) (N : Term n) : ¬ Step (.cquote k M) N :=
  (Normal.cquote k M).no_step N

/-! ## Running a template on closed arguments -/

/-- **The function of a template, applied to closed arguments, reduces to the
code with its parameters filled.** -/
theorem steps_appsN_lamN {n : Nat} : ∀ {k : Nat} (M : Term k) (V : Fin k → Term 0),
    Steps (appsN (ofClosed (lamN k M) : Term n) (fun i => ofClosed (V i)))
      (ofClosed (M.subst (fillSub V)))
  | 0, M, V => by
      have : (fillSub V : Sub 0 0) = Term.var := funext fun i => i.elim0
      simp only [appsN, lamN, this, subst_var]
      exact .refl
  | k + 1, M, V => by
      have ih := steps_appsN_lamN (n := n) (.lam M) (fun i => V i.castSucc)
      refine (Steps.app ih .refl).tail ?_
      have key : (ofClosed (M.subst (fillSub V)) : Term n) =
          (Term.rename (liftRen Fin.elim0)
            (M.subst (liftSub (fillSub (fun i => V i.castSucc))))).subst1
            (ofClosed (V (Fin.last k))) := by
        unfold ofClosed
        rw [← rename_subst1]
        congr 1
        unfold subst1
        rw [subst_subst]
        congr 1
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            simp only [liftSub_succ, subst_rename, single_succ, subst_var]
            rfl
      rw [key]
      exact .beta _ _

/-! ## The bracket, derived from `lift` -/

/-- The bracket `T[x := A]`: run the template `T`, apply its function to the
run of the name `A`, and seal the result with `lift`. -/
def inst {n : Nat} (T A : Term n) : Term n := .lift (.app (.drop T) (.drop A))

/-- The bracket with one name for each parameter, in order. -/
def instAll {n k : Nat} (T : Term n) (A : Fin k → Term n) : Term n :=
  .lift (appsN (.drop T) (fun i => .drop (A i)))

theorem instAll_one {n : Nat} (T A : Term n) : instAll T (fun _ : Fin 1 => A) = inst T A := rfl

/-- The bracket on a template and names reduces to `lift` of the code with
its parameters filled. -/
theorem instAll_template {n k : Nat} (M : Term k) (V : Fin k → Term 0) :
    Steps (instAll (.cquote k M : Term n) (fun i => .cquote 0 (V i)))
      (.lift (ofClosed (M.subst (fillSub V)))) := by
  unfold instAll
  apply Steps.lift
  have hT : Steps (.drop (.cquote k M) : Term n) (ofClosed (lamN k M)) := .single (.run k M)
  have hA : ∀ i, Steps (.drop (.cquote 0 (V i)) : Term n) (ofClosed (V i)) :=
    fun i => .single (.run 0 (V i))
  exact (Steps.appsN hT hA).trans (steps_appsN_lamN M V)

/-- **The bracket names the normal form of the filled code.** -/
theorem instAll_name {n k : Nat} (M : Term k) (V : Fin k → Term 0) {W : Term 0}
    (h : Steps (M.subst (fillSub V)) W) (normal : Normal W) :
    Steps (instAll (.cquote k M : Term n) (fun i => .cquote 0 (V i))) (.cquote 0 W) :=
  ((instAll_template M V).trans (h.rename Fin.elim0).lift).tail (.name W normal)

/-- **The bracket agrees with filling as written when the filled code is
normal.** -/
theorem instAll_asWritten {n k : Nat} (M : Term k) (V : Fin k → Term 0)
    (normal : Normal (M.subst (fillSub V))) :
    Steps (instAll (.cquote k M : Term n) (fun i => .cquote 0 (V i)))
      (.cquote 0 (M.subst (fillSub V))) :=
  instAll_name M V .refl normal

/-- Every reduct of a `lift` is a `lift` or the name of normal code. -/
theorem lift_reducts {n : Nat} {X N : Term n} (h : Steps (.lift X) N) :
    (∃ X', N = .lift X') ∨ (∃ W, N = .cquote 0 W ∧ Normal W) := by
  induction h with
  | refl => exact .inl ⟨X, rfl⟩
  | tail _ step ih =>
      rcases ih with ⟨X', rfl⟩ | ⟨W, rfl, _⟩
      · cases step with
        | name V normal => exact .inr ⟨V, rfl, normal⟩
        | lift inner => exact .inl ⟨_, rfl⟩
      · exact absurd step (cquote_no_step W _)

/-- **A name built by `lift` has normal code.** In particular the bracket
never names code that still has a redex. -/
theorem lift_reaches_normal {n : Nat} {X : Term n} {W : Term 0}
    (h : Steps (.lift X) (.cquote 0 W)) : Normal W := by
  rcases lift_reducts h with ⟨_, h'⟩ | ⟨W', h', normal⟩
  · cases h'
  · rw [cquote_inj h']
    exact normal

end Mettapedia.TypeTheory.Calculi.ContextualCode
