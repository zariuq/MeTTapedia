import Mettapedia.TypeTheory.Calculi.SealedCode.Syntax
import Mathlib.Logic.Relation

/-!
# Reduction with sealed names

Beta reduction, running a name, and sealing. `lift M` becomes the name
`quote M` once its code is closed and normal, so a constructed name is always
the name of a value. Reduction never enters a sealed name; it does enter the
code of `lift`, since that code is still being computed.

Normal forms are syntactic: no redex occurs outside sealed code. A `lift` is
normal only while its code is open, since only the enclosing binders can still
complete it.

The first law is substitution stability: a step stays a step after any
substitution. Sealing fires only on closed code, which no substitution
changes, and substitution never enters the name it produces.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SealedCode

open Term

/-- Normal forms: no redex outside sealed code. -/
inductive Normal : {n : Nat} → Term n → Prop where
  | var {n : Nat} (i : Fin n) : Normal (.var i)
  | sym {n : Nat} (s : String) : Normal (.sym s : Term n)
  | quote {n : Nat} (M : Term 0) : Normal (.quote M : Term n)
  | lam {n : Nat} {b : Term (n + 1)} : Normal b → Normal (.lam b)
  | app {n : Nat} {f a : Term n} :
      Normal f → Normal a → (∀ b, f ≠ .lam b) → Normal (.app f a)
  | lift {n : Nat} {M : Term n} : Normal M → M.Open → Normal (.lift M)
  | drop {n : Nat} {K : Term n} :
      Normal K → (∀ M, K ≠ .quote M) → (∀ M, K ≠ .lift M) → Normal (.drop K)

/-- One reduction step. -/
inductive Step : {n : Nat} → Term n → Term n → Prop where
  | beta {n : Nat} (b : Term (n + 1)) (a : Term n) : Step (.app (.lam b) a) (b.inst a)
  | runQuote {n : Nat} (M : Term 0) : Step (.drop (.quote M) : Term n) (ofClosed M)
  | runLift {n : Nat} (M : Term n) : Step (.drop (.lift M)) M
  | name {n : Nat} (M : Term 0) : Normal M → Step (.lift (ofClosed M) : Term n) (.quote M)
  | lam {n : Nat} {b b' : Term (n + 1)} : Step b b' → Step (.lam b) (.lam b')
  | appL {n : Nat} {f f' a : Term n} : Step f f' → Step (.app f a) (.app f' a)
  | appR {n : Nat} {f a a' : Term n} : Step a a' → Step (.app f a) (.app f a')
  | lift {n : Nat} {M M' : Term n} : Step M M' → Step (.lift M) (.lift M')
  | drop {n : Nat} {K K' : Term n} : Step K K' → Step (.drop K) (.drop K')

/-- Many steps. -/
abbrev Steps {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen (@Step n)

/-! ## Substitution stability -/

/-- **A step stays a step under every substitution.** -/
theorem Step.subst {n : Nat} {M N : Term n} (h : Step M N) :
    ∀ {m : Nat} (σ : Sub n m), Step (M.subst σ) (N.subst σ) := by
  induction h with
  | beta b a =>
      intro m σ
      simp only [Term.subst]
      rw [subst_inst]
      exact .beta _ _
  | runQuote M =>
      intro m σ
      simp only [Term.subst, subst_ofClosed]
      exact .runQuote M
  | runLift M =>
      intro m σ
      exact .runLift _
  | name M normal =>
      intro m σ
      simp only [Term.subst, subst_ofClosed]
      exact .name M normal
  | lam _ ih => intro m σ; exact .lam (ih _)
  | appL _ ih => intro m σ; exact .appL (ih _)
  | appR _ ih => intro m σ; exact .appR (ih _)
  | lift _ ih => intro m σ; exact .lift (ih _)
  | drop _ ih => intro m σ; exact .drop (ih _)

theorem Step.rename {n m : Nat} {M N : Term n} (h : Step M N) (ρ : Ren n m) :
    Step (M.rename ρ) (N.rename ρ) := by
  rw [← subst_ren, ← subst_ren]
  exact h.subst _

theorem Steps.subst {n m : Nat} {M N : Term n} (h : Steps M N) (σ : Sub n m) :
    Steps (M.subst σ) (N.subst σ) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst σ)

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

/-! ## Normal forms -/

/-- Renaming keeps a term normal. -/
theorem Normal.rename {n : Nat} {M : Term n} (h : Normal M) :
    ∀ {m : Nat} (ρ : Ren n m), Normal (M.rename ρ) := by
  induction h with
  | var i => intro m ρ; exact .var _
  | sym s => intro m ρ; exact .sym s
  | quote M => intro m ρ; exact .quote M
  | lam _ ih => intro m ρ; exact .lam (ih _)
  | @app n f a _ _ notLam ihf iha =>
      intro m ρ
      refine .app (ihf ρ) (iha ρ) ?_
      intro b hb
      cases f with
      | lam b' => exact notLam b' rfl
      | _ => simp [Term.rename] at hb
  | lift _ isOpen ih =>
      intro m ρ
      exact .lift (ih ρ) ((open_rename ρ _).mpr isOpen)
  | @drop n K _ notQuote notLift ih =>
      intro m ρ
      refine .drop (ih ρ) ?_ ?_
      · intro M hM
        cases K with
        | quote M' => exact notQuote M' rfl
        | _ => simp [Term.rename] at hM
      · intro M hM
        cases K with
        | lift M' => exact notLift M' rfl
        | _ => simp [Term.rename] at hM

theorem Normal.ofClosed {n : Nat} {M : Term 0} (h : Normal M) :
    Normal (Term.ofClosed M : Term n) :=
  h.rename _

/-- **A normal term does not step.** -/
theorem Normal.no_step {n : Nat} {M : Term n} (h : Normal M) : ∀ N, ¬ Step M N := by
  induction h with
  | var i => intro N step; cases step
  | sym s => intro N step; cases step
  | quote M => intro N step; cases step
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
      | name M₀ _ => exact not_open_ofClosed M₀ isOpen
      | lift inner => exact ih _ inner
  | drop _ notQuote notLift ih =>
      intro N step
      cases step with
      | runQuote M₀ => exact notQuote M₀ rfl
      | runLift => exact notLift _ rfl
      | drop inner => exact ih _ inner

/-- A sealed name does not step. -/
theorem quote_no_step {n : Nat} (M : Term 0) (N : Term n) : ¬ Step (.quote M) N :=
  (Normal.quote M).no_step N

end Mettapedia.TypeTheory.Calculi.SealedCode
