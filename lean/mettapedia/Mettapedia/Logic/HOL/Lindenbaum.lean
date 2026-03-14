import Mathlib.Order.Heyting.Basic
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A finite closed HOL theory, represented as a list of closed formulas. -/
abbrev ClosedTheory (Const : Ty Base → Type v) := List (ClosedFormula Const)

namespace ClosedTheory

/-- Closed derivability from a finite closed theory. -/
abbrev Provable (Δ : ClosedTheory Const) (φ : ClosedFormula Const) : Prop :=
  ExtDerivation Const Δ φ

/-- Closed provable equivalence over a fixed finite theory. -/
def ProvablyEquivalent (Δ : ClosedTheory Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  Provable (Const := Const) Δ (.imp φ ψ) ∧
    Provable (Const := Const) Δ (.imp ψ φ)

namespace Provable

variable {Δ Δ' : ClosedTheory Const} {φ ψ χ : ClosedFormula Const}

theorem mono
    (hsub : ∀ {ξ : ClosedFormula Const}, ξ ∈ Δ → ξ ∈ Δ') :
    Provable (Const := Const) Δ φ →
      Provable (Const := Const) Δ' φ :=
  ExtDerivation.mono hsub

theorem assumption (hφ : φ ∈ Δ) : Provable (Const := Const) Δ φ :=
  .hyp hφ

theorem top : Provable (Const := Const) Δ (.top : ClosedFormula Const) :=
  .topI

theorem imp_top : Provable (Const := Const) Δ (.imp φ (.top : ClosedFormula Const)) :=
  .impI .topI

theorem bot_imp : Provable (Const := Const) Δ (.imp (.bot : ClosedFormula Const) φ) :=
  .impI (.botE (.hyp (show (.bot : ClosedFormula Const) ∈ (.bot :: Δ) from by simp)))

theorem imp_refl : Provable (Const := Const) Δ (.imp φ φ) :=
  .impI (.hyp (by simp))

theorem imp_mp
    (hImp : Provable (Const := Const) Δ (.imp φ ψ))
    (hφ : Provable (Const := Const) Δ φ) :
    Provable (Const := Const) Δ ψ :=
  .impE hImp hφ

theorem imp_trans
    (hφψ : Provable (Const := Const) Δ (.imp φ ψ))
    (hψχ : Provable (Const := Const) Δ (.imp ψ χ)) :
    Provable (Const := Const) Δ (.imp φ χ) := by
  refine .impI ?_
  have hψ : Provable (Const := Const) (φ :: Δ) ψ :=
    .impE
      (mono (Δ := Δ) (Δ' := φ :: Δ) (φ := .imp φ ψ) (by
        intro ξ hξ
        simp [hξ]) hφψ)
      (.hyp (by simp))
  exact
    .impE
      (mono (Δ := Δ) (Δ' := φ :: Δ) (φ := .imp ψ χ) (by
        intro ξ hξ
        simp [hξ]) hψχ)
      hψ

theorem and_left : Provable (Const := Const) Δ (.imp (.and φ ψ) φ) :=
  .impI (.andEL (.hyp (show (.and φ ψ : ClosedFormula Const) ∈ (.and φ ψ :: Δ) from by simp)))

theorem and_right : Provable (Const := Const) Δ (.imp (.and φ ψ) ψ) :=
  .impI (.andER (.hyp (show (.and φ ψ : ClosedFormula Const) ∈ (.and φ ψ :: Δ) from by simp)))

theorem and_intro
    (hφ : Provable (Const := Const) Δ (.imp χ φ))
    (hψ : Provable (Const := Const) Δ (.imp χ ψ)) :
    Provable (Const := Const) Δ (.imp χ (.and φ ψ)) := by
  refine .impI ?_
  refine .andI ?_ ?_
  · exact .impE (mono (Δ := Δ) (Δ' := χ :: Δ) (φ := .imp χ φ) (by
      intro ξ hξ
      simp [hξ]) hφ) (.hyp (by simp))
  · exact .impE (mono (Δ := Δ) (Δ' := χ :: Δ) (φ := .imp χ ψ) (by
      intro ξ hξ
      simp [hξ]) hψ) (.hyp (by simp))

theorem or_intro_left : Provable (Const := Const) Δ (.imp φ (.or φ ψ)) :=
  .impI (.orIL (.hyp (show φ ∈ (φ :: Δ) from by simp)))

theorem or_intro_right : Provable (Const := Const) Δ (.imp ψ (.or φ ψ)) :=
  .impI (.orIR (.hyp (show ψ ∈ (ψ :: Δ) from by simp)))

theorem or_elim
    (hφ : Provable (Const := Const) Δ (.imp φ χ))
    (hψ : Provable (Const := Const) Δ (.imp ψ χ)) :
    Provable (Const := Const) Δ (.imp (.or φ ψ) χ) := by
  refine .impI ?_
  refine .orE (.hyp (show (.or φ ψ : ClosedFormula Const) ∈ (.or φ ψ :: Δ) from by simp)) ?_ ?_
  · exact .impE
      (mono (Δ := Δ) (Δ' := φ :: (.or φ ψ) :: Δ) (φ := .imp φ χ) (by
        intro ξ hξ
        simp [hξ]) hφ)
      (.hyp (show φ ∈ (φ :: (.or φ ψ) :: Δ) from by simp))
  · exact .impE
      (mono (Δ := Δ) (Δ' := ψ :: (.or φ ψ) :: Δ) (φ := .imp ψ χ) (by
        intro ξ hξ
        simp [hξ]) hψ)
      (.hyp (show ψ ∈ (ψ :: (.or φ ψ) :: Δ) from by simp))

theorem not_congr
    (hφψ : Provable (Const := Const) Δ (.imp φ ψ)) :
    Provable (Const := Const) Δ (.imp (.not ψ) (.not φ)) := by
  refine .impI ?_
  refine .notI ?_
  have hNotψ : Provable (Const := Const) (φ :: .not ψ :: Δ) (.not ψ) :=
    .hyp (by simp)
  have hφ : Provable (Const := Const) (φ :: .not ψ :: Δ) φ :=
    .hyp (by simp)
  have hψ : Provable (Const := Const) (φ :: .not ψ :: Δ) ψ :=
    .impE
      (mono (Δ := Δ) (Δ' := φ :: .not ψ :: Δ) (φ := .imp φ ψ) (by
        intro ξ hξ
        simp [hξ]) hφψ)
      hφ
  exact .notE hNotψ hψ

theorem imp_congr
    (hφφ' : Provable (Const := Const) Δ (.imp φ φ'))
    (hφ'φ : Provable (Const := Const) Δ (.imp φ' φ))
    (hψψ' : Provable (Const := Const) Δ (.imp ψ ψ'))
    (hψ'ψ : Provable (Const := Const) Δ (.imp ψ' ψ)) :
    ProvablyEquivalent (Const := Const) Δ (.imp φ ψ) (.imp φ' ψ') := by
  constructor
  · refine .impI ?_
    refine .impI ?_
    have hφ' : Provable (Const := Const) (φ' :: .imp φ ψ :: Δ) φ :=
      .impE
        (mono (Δ := Δ) (Δ' := φ' :: .imp φ ψ :: Δ) (φ := .imp φ' φ) (by
          intro ξ hξ
          simp [hξ]) hφ'φ)
        (.hyp (show φ' ∈ (φ' :: .imp φ ψ :: Δ) from by simp))
    have hψ : Provable (Const := Const) (φ' :: .imp φ ψ :: Δ) ψ :=
      .impE (.hyp (show (.imp φ ψ : ClosedFormula Const) ∈ (φ' :: .imp φ ψ :: Δ) from by simp)) hφ'
    have hψψ'_ctx : Provable (Const := Const) (φ' :: .imp φ ψ :: Δ) (.imp ψ ψ') :=
      mono (Δ := Δ) (Δ' := φ' :: .imp φ ψ :: Δ) (φ := .imp ψ ψ') (by
        intro ξ hξ
        simp [hξ]) hψψ'
    exact .impE
      hψψ'_ctx
      hψ
  · refine .impI ?_
    refine .impI ?_
    have hφ : Provable (Const := Const) (φ :: .imp φ' ψ' :: Δ) φ' :=
      .impE
        (mono (Δ := Δ) (Δ' := φ :: .imp φ' ψ' :: Δ) (φ := .imp φ φ') (by
          intro ξ hξ
          simp [hξ]) hφφ')
        (.hyp (show φ ∈ (φ :: .imp φ' ψ' :: Δ) from by simp))
    have hψ' : Provable (Const := Const) (φ :: .imp φ' ψ' :: Δ) ψ' :=
      .impE (.hyp (show (.imp φ' ψ' : ClosedFormula Const) ∈ (φ :: .imp φ' ψ' :: Δ) from by simp)) hφ
    have hψ'ψ_ctx : Provable (Const := Const) (φ :: .imp φ' ψ' :: Δ) (.imp ψ' ψ) :=
      mono (Δ := Δ) (Δ' := φ :: .imp φ' ψ' :: Δ) (φ := .imp ψ' ψ) (by
        intro ξ hξ
        simp [hξ]) hψ'ψ
    exact .impE
      hψ'ψ_ctx
      hψ'

theorem imp_uncurry
    (h : Provable (Const := Const) Δ (.imp φ (.imp ψ χ))) :
    Provable (Const := Const) Δ (.imp (.and φ ψ) χ) := by
  refine .impI ?_
  have hCtx : Provable (Const := Const) (.and φ ψ :: Δ) (.imp φ (.imp ψ χ)) :=
    mono (Δ := Δ) (Δ' := .and φ ψ :: Δ) (φ := .imp φ (.imp ψ χ)) (by
      intro ξ hξ
      simp [hξ]) h
  have hφ : Provable (Const := Const) (.and φ ψ :: Δ) φ :=
    .andEL (.hyp (show (.and φ ψ : ClosedFormula Const) ∈ (.and φ ψ :: Δ) from by simp))
  have hψχ : Provable (Const := Const) (.and φ ψ :: Δ) (.imp ψ χ) :=
    .impE hCtx hφ
  have hψ : Provable (Const := Const) (.and φ ψ :: Δ) ψ :=
    .andER (.hyp (show (.and φ ψ : ClosedFormula Const) ∈ (.and φ ψ :: Δ) from by simp))
  exact .impE hψχ hψ

theorem imp_curry
    (h : Provable (Const := Const) Δ (.imp (.and φ ψ) χ)) :
    Provable (Const := Const) Δ (.imp φ (.imp ψ χ)) := by
  refine .impI ?_
  refine .impI ?_
  have hCtx : Provable (Const := Const) (ψ :: φ :: Δ) (.imp (.and φ ψ) χ) :=
    mono (Δ := Δ) (Δ' := ψ :: φ :: Δ) (φ := .imp (.and φ ψ) χ) (by
      intro ξ hξ
      simp [hξ]) h
  have hAnd : Provable (Const := Const) (ψ :: φ :: Δ) (.and φ ψ) :=
    .andI
      (.hyp (show φ ∈ (ψ :: φ :: Δ) from by simp))
      (.hyp (show ψ ∈ (ψ :: φ :: Δ) from by simp))
  exact .impE hCtx hAnd

end Provable

namespace ProvablyEquivalent

variable {Δ : ClosedTheory Const} {φ ψ χ : ClosedFormula Const}

theorem refl (Δ : ClosedTheory Const) (φ : ClosedFormula Const) :
    ProvablyEquivalent (Const := Const) Δ φ φ :=
  ⟨Provable.imp_refl (Δ := Δ) (φ := φ), Provable.imp_refl (Δ := Δ) (φ := φ)⟩

theorem symm :
    ProvablyEquivalent (Const := Const) Δ φ ψ →
      ProvablyEquivalent (Const := Const) Δ ψ φ
  | ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem trans
    (hφψ : ProvablyEquivalent (Const := Const) Δ φ ψ)
    (hψχ : ProvablyEquivalent (Const := Const) Δ ψ χ) :
    ProvablyEquivalent (Const := Const) Δ φ χ :=
  ⟨Provable.imp_trans hφψ.1 hψχ.1, Provable.imp_trans hψχ.2 hφψ.2⟩

theorem and_congr
    (hφ : ProvablyEquivalent (Const := Const) Δ φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) Δ χ ξ) :
    ProvablyEquivalent (Const := Const) Δ (.and φ χ) (.and ψ ξ) := by
  constructor
  · exact Provable.and_intro
      (Provable.imp_trans Provable.and_left hφ.1)
      (Provable.imp_trans Provable.and_right hχ.1)
  · exact Provable.and_intro
      (Provable.imp_trans Provable.and_left hφ.2)
      (Provable.imp_trans Provable.and_right hχ.2)

theorem or_congr
    (hφ : ProvablyEquivalent (Const := Const) Δ φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) Δ χ ξ) :
    ProvablyEquivalent (Const := Const) Δ (.or φ χ) (.or ψ ξ) := by
  constructor
  · exact Provable.or_elim
      (Provable.imp_trans hφ.1 Provable.or_intro_left)
      (Provable.imp_trans hχ.1 Provable.or_intro_right)
  · exact Provable.or_elim
      (Provable.imp_trans hφ.2 Provable.or_intro_left)
      (Provable.imp_trans hχ.2 Provable.or_intro_right)

theorem imp_congr
    (hφ : ProvablyEquivalent (Const := Const) Δ φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) Δ χ ξ) :
    ProvablyEquivalent (Const := Const) Δ (.imp φ χ) (.imp ψ ξ) :=
  Provable.imp_congr hφ.1 hφ.2 hχ.1 hχ.2

theorem not_congr
    (hφ : ProvablyEquivalent (Const := Const) Δ φ ψ) :
    ProvablyEquivalent (Const := Const) Δ (.not φ) (.not ψ) :=
  ⟨Provable.not_congr hφ.2, Provable.not_congr hφ.1⟩

theorem provable_iff_top
    (Δ : ClosedTheory Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) Δ φ ↔
      ProvablyEquivalent (Const := Const) Δ φ (.top : ClosedFormula Const) := by
  constructor
  · intro hφ
    constructor
    · exact Provable.imp_top (Δ := Δ) (φ := φ)
    · refine .impI ?_
      exact Provable.mono (Δ := Δ) (Δ' := (.top : ClosedFormula Const) :: Δ) (φ := φ) (by
        intro ξ hξ
        simp [hξ]) hφ
  · intro hEq
    exact .impE hEq.2 Provable.top

def setoid (Δ : ClosedTheory Const) : Setoid (ClosedFormula Const) where
  r := ProvablyEquivalent (Const := Const) Δ
  iseqv :=
    { refl := refl (Const := Const) Δ
      symm := symm
      trans := trans }

abbrev Lindenbaum (Δ : ClosedTheory Const) :=
  Quotient (setoid (Const := Const) Δ)

namespace Lindenbaum

variable (Δ : ClosedTheory Const)

noncomputable instance : DecidableEq (ClosedFormula Const) := by
  classical
  infer_instance

lemma eq_iff {φ ψ : ClosedFormula Const} :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ) = ⟦ψ⟧ ↔
      ProvablyEquivalent (Const := Const) Δ φ ψ :=
  Quotient.eq

instance : Top (Lindenbaum (Const := Const) Δ) := ⟨⟦(.top : ClosedFormula Const)⟧⟩

instance : Bot (Lindenbaum (Const := Const) Δ) := ⟨⟦(.bot : ClosedFormula Const)⟧⟩

instance : Min (Lindenbaum (Const := Const) Δ) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.and φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.and_congr hφ hψ))⟩

instance : Max (Lindenbaum (Const := Const) Δ) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.or φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.or_congr hφ hψ))⟩

instance : HImp (Lindenbaum (Const := Const) Δ) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.imp φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.imp_congr hφ hψ))⟩

instance : Compl (Lindenbaum (Const := Const) Δ) :=
  ⟨Quotient.lift (fun φ => ⟦(.imp φ (.bot : ClosedFormula Const) : ClosedFormula Const)⟧)
      (fun φ ψ hφ => by
        exact Quotient.sound
          (ProvablyEquivalent.imp_congr hφ
            (ProvablyEquivalent.refl (Const := Const) Δ (.bot : ClosedFormula Const))))⟩

instance : LE (Lindenbaum (Const := Const) Δ) :=
  ⟨Quotient.lift₂
      (fun φ ψ => Provable (Const := Const) Δ (.imp φ ψ))
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        apply propext
        have hEq : ProvablyEquivalent (Const := Const) Δ (.imp φ₁ ψ₁) (.imp φ₂ ψ₂) :=
          ProvablyEquivalent.imp_congr hφ hψ
        constructor
        · intro h
          exact Provable.imp_mp hEq.1 h
        · intro h
          exact Provable.imp_mp hEq.2 h)⟩

lemma le_def {φ ψ : ClosedFormula Const} :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ) ≤ ⟦ψ⟧ ↔
      Provable (Const := Const) Δ (.imp φ ψ) :=
  iff_of_eq rfl

lemma top_def :
    (⊤ : Lindenbaum (Const := Const) Δ) = ⟦(.top : ClosedFormula Const)⟧ := rfl

lemma bot_def :
    (⊥ : Lindenbaum (Const := Const) Δ) = ⟦(.bot : ClosedFormula Const)⟧ := rfl

lemma inf_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ) ⊓ ⟦ψ⟧ =
      ⟦(.and φ ψ : ClosedFormula Const)⟧ := rfl

lemma sup_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ) ⊔ ⟦ψ⟧ =
      ⟦(.or φ ψ : ClosedFormula Const)⟧ := rfl

lemma himp_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ) ⇨ ⟦ψ⟧ =
      ⟦(.imp φ ψ : ClosedFormula Const)⟧ := rfl

lemma compl_def (φ : ClosedFormula Const) :
    (⟦φ⟧ : Lindenbaum (Const := Const) Δ)ᶜ =
      ⟦(.imp φ (.bot : ClosedFormula Const) : ClosedFormula Const)⟧ := rfl

lemma provable_iff_eq_top {φ : ClosedFormula Const} :
    Provable (Const := Const) Δ φ ↔
      (⟦φ⟧ : Lindenbaum (Const := Const) Δ) = ⊤ := by
  rw [top_def, eq_iff]
  exact ProvablyEquivalent.provable_iff_top (Const := Const) Δ φ

instance : PartialOrder (Lindenbaum (Const := Const) Δ) where
  le := (· ≤ ·)
  le_refl := by
    intro a
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (Δ := Δ) (φ := φ) (ψ := φ)).2 (Provable.imp_refl (Δ := Δ) (φ := φ))
  le_trans := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφψ hψχ
    exact (le_def (Δ := Δ) (φ := φ) (ψ := χ)).2 (Provable.imp_trans hφψ hψχ)
  le_antisymm := by
    intro a b hab hba
    refine Quotient.inductionOn₂ a b ?_ hab hba
    intro φ ψ hφψ hψφ
    exact (eq_iff (Δ := Δ)).2 ⟨hφψ, hψφ⟩

instance : GeneralizedHeytingAlgebra (Lindenbaum (Const := Const) Δ) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  top := ⊤
  le := (· ≤ ·)
  himp := (· ⇨ ·)
  le_refl := by intro a; exact le_rfl
  le_trans := by intro a b c; exact le_trans
  le_antisymm := by intro a b; exact le_antisymm
  inf_le_left a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (Δ := Δ) (φ := .and φ ψ) (ψ := φ)).2
      (Provable.and_left (Δ := Δ) (φ := φ) (ψ := ψ))
  inf_le_right a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (Δ := Δ) (φ := .and φ ψ) (ψ := ψ)).2
      (Provable.and_right (Δ := Δ) (φ := φ) (ψ := ψ))
  le_inf a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφ hψ
    exact (le_def (Δ := Δ) (φ := φ) (ψ := .and ψ χ)).2
      (Provable.and_intro hφ hψ)
  le_sup_left a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (Δ := Δ) (φ := φ) (ψ := .or φ ψ)).2
      (Provable.or_intro_left (Δ := Δ) (φ := φ) (ψ := ψ))
  le_sup_right a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (Δ := Δ) (φ := ψ) (ψ := .or φ ψ)).2
      (Provable.or_intro_right (Δ := Δ) (φ := φ) (ψ := ψ))
  sup_le a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφ hψ
    exact (le_def (Δ := Δ) (φ := .or φ ψ) (ψ := χ)).2
      (Provable.or_elim hφ hψ)
  le_top a := by
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (Δ := Δ) (φ := φ) (ψ := .top)).2
      (Provable.imp_top (Δ := Δ) (φ := φ))
  le_himp_iff a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ
    constructor
    · intro h
      exact (le_def (Δ := Δ) (φ := .and φ ψ) (ψ := χ)).2
        (Provable.imp_uncurry h)
    · intro h
      exact (le_def (Δ := Δ) (φ := φ) (ψ := .imp ψ χ)).2
        (Provable.imp_curry h)

instance : HeytingAlgebra (Lindenbaum (Const := Const) Δ) where
  bot := ⊥
  bot_le a := by
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (Δ := Δ) (φ := .bot) (ψ := φ)).2
      (Provable.bot_imp (Δ := Δ) (φ := φ))
  himp_bot a := by
    refine Quotient.inductionOn a ?_
    intro φ
    rw [compl_def, bot_def, himp_def]
  __ := inferInstanceAs (GeneralizedHeytingAlgebra (Lindenbaum (Const := Const) Δ))

end Lindenbaum

end ProvablyEquivalent

end ClosedTheory

end Mettapedia.Logic.HOL
