import Mathlib.Order.Heyting.Basic
import Mettapedia.Logic.HOL.CanonicalTheory

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace ClosedTheorySet

/-- Closed provable equivalence over a fixed closed HOL theory set. -/
def ProvablyEquivalent (T : ClosedTheorySet Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  Provable (Const := Const) T (.imp φ ψ) ∧
    Provable (Const := Const) T (.imp ψ φ)

namespace Provable

variable {T U : ClosedTheorySet Const} {φ ψ χ ξ : ClosedFormula Const}

theorem mono
    (hTU : ∀ {ζ : ClosedFormula Const}, ζ ∈ T → ζ ∈ U) :
    Provable (Const := Const) T φ →
      Provable (Const := Const) U φ :=
  provable_mono (Const := Const) hTU

theorem top (T : ClosedTheorySet Const) :
    Provable (Const := Const) T (.top : ClosedFormula Const) :=
  provable_top (Const := Const) T

theorem imp_refl (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp φ φ) :=
  provable_imp_refl (Const := Const) T φ

theorem imp_top (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp φ (.top : ClosedFormula Const)) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.imp_top (Δ := []) (Const := Const) (φ := φ))

theorem bot_imp (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp (.bot : ClosedFormula Const) φ) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.bot_imp (Δ := []) (Const := Const) (φ := φ))

theorem imp_mp
    (hImp : Provable (Const := Const) T (.imp φ ψ))
    (hφ : Provable (Const := Const) T φ) :
    Provable (Const := Const) T ψ :=
  provable_mp (Const := Const) hImp hφ

theorem imp_trans
    (hφψ : Provable (Const := Const) T (.imp φ ψ))
    (hψχ : Provable (Const := Const) T (.imp ψ χ)) :
    Provable (Const := Const) T (.imp φ χ) := by
  rcases hφψ with ⟨Γ₁, hΓ₁, hφψ⟩
  rcases hψχ with ⟨Γ₂, hΓ₂, hψχ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ζ hζ
    rcases List.mem_append.mp hζ with hζ | hζ
    · exact hΓ₁ ζ hζ
    · exact hΓ₂ ζ hζ
  · exact ClosedTheory.Provable.imp_trans
      (ClosedTheory.Provable.mono
        (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := .imp φ ψ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inl hζ))
        hφψ)
      (ClosedTheory.Provable.mono
        (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := .imp ψ χ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inr hζ))
        hψχ)

theorem and_left (T : ClosedTheorySet Const) (φ ψ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp (.and φ ψ) φ) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.and_left (Δ := []) (Const := Const) (φ := φ) (ψ := ψ))

theorem and_right (T : ClosedTheorySet Const) (φ ψ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp (.and φ ψ) ψ) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.and_right (Δ := []) (Const := Const) (φ := φ) (ψ := ψ))

theorem and_intro
    (hφ : Provable (Const := Const) T (.imp χ φ))
    (hψ : Provable (Const := Const) T (.imp χ ψ)) :
    Provable (Const := Const) T (.imp χ (.and φ ψ)) := by
  rcases hφ with ⟨Γ₁, hΓ₁, hφ⟩
  rcases hψ with ⟨Γ₂, hΓ₂, hψ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ζ hζ
    rcases List.mem_append.mp hζ with hζ | hζ
    · exact hΓ₁ ζ hζ
    · exact hΓ₂ ζ hζ
  · exact ClosedTheory.Provable.and_intro
      (ClosedTheory.Provable.mono
        (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := .imp χ φ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inl hζ))
        hφ)
      (ClosedTheory.Provable.mono
        (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := .imp χ ψ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inr hζ))
        hψ)

theorem or_intro_left (T : ClosedTheorySet Const) (φ ψ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp φ (.or φ ψ)) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.or_intro_left (Δ := []) (Const := Const) (φ := φ) (ψ := ψ))

theorem or_intro_right (T : ClosedTheorySet Const) (φ ψ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp ψ (.or φ ψ)) := by
  exact provable_of_closedTheory
    (Const := Const) (T := T) (Δ := [])
    (hΔ := by intro ξ hξ; cases hξ)
    (hφ := ClosedTheory.Provable.or_intro_right (Δ := []) (Const := Const) (φ := φ) (ψ := ψ))

theorem or_elim
    (hφ : Provable (Const := Const) T (.imp φ χ))
    (hψ : Provable (Const := Const) T (.imp ψ χ)) :
    Provable (Const := Const) T (.imp (.or φ ψ) χ) := by
  rcases hφ with ⟨Γ₁, hΓ₁, hφ⟩
  rcases hψ with ⟨Γ₂, hΓ₂, hψ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ζ hζ
    rcases List.mem_append.mp hζ with hζ | hζ
    · exact hΓ₁ ζ hζ
    · exact hΓ₂ ζ hζ
  · exact ClosedTheory.Provable.or_elim
      (ClosedTheory.Provable.mono
        (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := .imp φ χ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inl hζ))
        hφ)
      (ClosedTheory.Provable.mono
        (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := .imp ψ χ)
        (by
          intro ζ hζ
          exact List.mem_append.mpr (.inr hζ))
        hψ)

theorem imp_uncurry
    (h : Provable (Const := Const) T (.imp φ (.imp ψ χ))) :
    Provable (Const := Const) T (.imp (.and φ ψ) χ) := by
  rcases h with ⟨Γ, hΓ, h⟩
  exact ⟨Γ, hΓ, ClosedTheory.Provable.imp_uncurry h⟩

theorem imp_curry
    (h : Provable (Const := Const) T (.imp (.and φ ψ) χ)) :
    Provable (Const := Const) T (.imp φ (.imp ψ χ)) := by
  rcases h with ⟨Γ, hΓ, h⟩
  exact ⟨Γ, hΓ, ClosedTheory.Provable.imp_curry h⟩

theorem not_congr
    (hφψ : Provable (Const := Const) T (.imp φ ψ)) :
    Provable (Const := Const) T (.imp (.not ψ) (.not φ)) := by
  rcases hφψ with ⟨Γ, hΓ, hφψ⟩
  exact ⟨Γ, hΓ, ClosedTheory.Provable.not_congr hφψ⟩

theorem imp_congr
    (hφφ' : Provable (Const := Const) T (.imp φ φ'))
    (hφ'φ : Provable (Const := Const) T (.imp φ' φ))
    (hψψ' : Provable (Const := Const) T (.imp ψ ψ'))
    (hψ'ψ : Provable (Const := Const) T (.imp ψ' ψ)) :
    ProvablyEquivalent (Const := Const) T (.imp φ ψ) (.imp φ' ψ') := by
  rcases hφφ' with ⟨Γ₁, hΓ₁, hφφ'⟩
  rcases hφ'φ with ⟨Γ₂, hΓ₂, hφ'φ⟩
  rcases hψψ' with ⟨Γ₃, hΓ₃, hψψ'⟩
  rcases hψ'ψ with ⟨Γ₄, hΓ₄, hψ'ψ⟩
  let Γ12 : ClosedTheory Const := Γ₁ ++ Γ₂
  let Γ34 : ClosedTheory Const := Γ₃ ++ Γ₄
  let Γ : ClosedTheory Const := Γ12 ++ Γ34
  constructor
  · refine ⟨Γ, ?_, ?_⟩
    · intro ζ hζ
      rcases List.mem_append.mp hζ with hζ | hζ
      · rcases List.mem_append.mp hζ with hζ | hζ
        · exact hΓ₁ ζ hζ
        · exact hΓ₂ ζ hζ
      · rcases List.mem_append.mp hζ with hζ | hζ
        · exact hΓ₃ ζ hζ
        · exact hΓ₄ ζ hζ
    · exact (ClosedTheory.Provable.imp_congr
        (ClosedTheory.Provable.mono
          (Δ := Γ₁) (Δ' := Γ) (φ := .imp φ φ')
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hζ))))
          hφφ')
        (ClosedTheory.Provable.mono
          (Δ := Γ₂) (Δ' := Γ) (φ := .imp φ' φ)
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hζ))))
          hφ'φ)
        (ClosedTheory.Provable.mono
          (Δ := Γ₃) (Δ' := Γ) (φ := .imp ψ ψ')
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hζ)))
          )
          hψψ')
        (ClosedTheory.Provable.mono
          (Δ := Γ₄) (Δ' := Γ) (φ := .imp ψ' ψ)
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr hζ)))
          )
          hψ'ψ)).1
  · refine ⟨Γ, ?_, ?_⟩
    · intro ζ hζ
      rcases List.mem_append.mp hζ with hζ | hζ
      · rcases List.mem_append.mp hζ with hζ | hζ
        · exact hΓ₁ ζ hζ
        · exact hΓ₂ ζ hζ
      · rcases List.mem_append.mp hζ with hζ | hζ
        · exact hΓ₃ ζ hζ
        · exact hΓ₄ ζ hζ
    · exact (ClosedTheory.Provable.imp_congr
        (ClosedTheory.Provable.mono
          (Δ := Γ₂) (Δ' := Γ) (φ := .imp φ' φ)
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hζ))))
          hφ'φ)
        (ClosedTheory.Provable.mono
          (Δ := Γ₁) (Δ' := Γ) (φ := .imp φ φ')
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hζ))))
          hφφ')
        (ClosedTheory.Provable.mono
          (Δ := Γ₄) (Δ' := Γ) (φ := .imp ψ' ψ)
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr hζ)))
          )
          hψ'ψ)
        (ClosedTheory.Provable.mono
          (Δ := Γ₃) (Δ' := Γ) (φ := .imp ψ ψ')
          (by
            intro ζ hζ
            exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hζ)))
          )
          hψψ')).1

end Provable

namespace ProvablyEquivalent

variable {T : ClosedTheorySet Const} {φ ψ χ ξ : ClosedFormula Const}

theorem refl (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    ProvablyEquivalent (Const := Const) T φ φ :=
  ⟨Provable.imp_refl (T := T) φ, Provable.imp_refl (T := T) φ⟩

theorem symm :
    ProvablyEquivalent (Const := Const) T φ ψ →
      ProvablyEquivalent (Const := Const) T ψ φ
  | ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem trans
    (hφψ : ProvablyEquivalent (Const := Const) T φ ψ)
    (hψχ : ProvablyEquivalent (Const := Const) T ψ χ) :
    ProvablyEquivalent (Const := Const) T φ χ :=
  ⟨Provable.imp_trans hφψ.1 hψχ.1, Provable.imp_trans hψχ.2 hφψ.2⟩

theorem and_congr
    (hφ : ProvablyEquivalent (Const := Const) T φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) T χ ξ) :
    ProvablyEquivalent (Const := Const) T (.and φ χ) (.and ψ ξ) := by
  constructor
  · exact Provable.and_intro
      (Provable.imp_trans (Provable.and_left (T := T) φ χ) hφ.1)
      (Provable.imp_trans (Provable.and_right (T := T) φ χ) hχ.1)
  · exact Provable.and_intro
      (Provable.imp_trans (Provable.and_left (T := T) ψ ξ) hφ.2)
      (Provable.imp_trans (Provable.and_right (T := T) ψ ξ) hχ.2)

theorem or_congr
    (hφ : ProvablyEquivalent (Const := Const) T φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) T χ ξ) :
    ProvablyEquivalent (Const := Const) T (.or φ χ) (.or ψ ξ) := by
  constructor
  · exact Provable.or_elim
      (Provable.imp_trans hφ.1 (Provable.or_intro_left (T := T) ψ ξ))
      (Provable.imp_trans hχ.1 (Provable.or_intro_right (T := T) ψ ξ))
  · exact Provable.or_elim
      (Provable.imp_trans hφ.2 (Provable.or_intro_left (T := T) φ χ))
      (Provable.imp_trans hχ.2 (Provable.or_intro_right (T := T) φ χ))

theorem imp_congr
    (hφ : ProvablyEquivalent (Const := Const) T φ ψ)
    (hχ : ProvablyEquivalent (Const := Const) T χ ξ) :
    ProvablyEquivalent (Const := Const) T (.imp φ χ) (.imp ψ ξ) :=
  Provable.imp_congr hφ.1 hφ.2 hχ.1 hχ.2

theorem provable_iff_top
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) T φ ↔
      ProvablyEquivalent (Const := Const) T φ (.top : ClosedFormula Const) := by
  constructor
  · intro hφ
    rcases hφ with ⟨Γ, hΓ, hφ⟩
    constructor
    · exact Provable.imp_top (T := T) φ
    · refine ⟨Γ, hΓ, ?_⟩
      refine ExtDerivation.impI ?_
      exact ExtDerivation.mono
        (Δ := Γ) (Δ' := (.top : ClosedFormula Const) :: Γ) (φ := φ)
        (by
          intro ξ hξ
          simp [hξ])
        hφ
  · intro hEq
    exact Provable.imp_mp hEq.2 (Provable.top T)

/-- Closed provable equivalence over a theory set is an equivalence relation. -/
def setoid (T : ClosedTheorySet Const) : Setoid (ClosedFormula Const) where
  r := ProvablyEquivalent (Const := Const) T
  iseqv :=
    { refl := refl (Const := Const) T
      symm := symm
      trans := trans }

abbrev LindenbaumSet (T : ClosedTheorySet Const) :=
  Quotient (setoid (Const := Const) T)

namespace LindenbaumSet

variable (T : ClosedTheorySet Const)

noncomputable instance : DecidableEq (ClosedFormula Const) := by
  classical
  infer_instance

lemma eq_iff {φ ψ : ClosedFormula Const} :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T) = ⟦ψ⟧ ↔
      ProvablyEquivalent (Const := Const) T φ ψ :=
  Quotient.eq

instance : Top (LindenbaumSet (Const := Const) T) := ⟨⟦(.top : ClosedFormula Const)⟧⟩

instance : Bot (LindenbaumSet (Const := Const) T) := ⟨⟦(.bot : ClosedFormula Const)⟧⟩

instance : Min (LindenbaumSet (Const := Const) T) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.and φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.and_congr hφ hψ))⟩

instance : Max (LindenbaumSet (Const := Const) T) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.or φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.or_congr hφ hψ))⟩

instance : LE (LindenbaumSet (Const := Const) T) :=
  ⟨Quotient.lift₂
      (fun φ ψ => Provable (Const := Const) T (.imp φ ψ))
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        apply propext
        have hEq : ProvablyEquivalent (Const := Const) T (.imp φ₁ ψ₁) (.imp φ₂ ψ₂) :=
          ProvablyEquivalent.imp_congr hφ hψ
        constructor
        · intro h
          exact Provable.imp_mp hEq.1 h
        · intro h
          exact Provable.imp_mp hEq.2 h)⟩

lemma le_def {φ ψ : ClosedFormula Const} :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T) ≤ ⟦ψ⟧ ↔
      Provable (Const := Const) T (.imp φ ψ) :=
  iff_of_eq rfl

lemma top_def :
    (⊤ : LindenbaumSet (Const := Const) T) = ⟦(.top : ClosedFormula Const)⟧ := rfl

lemma bot_def :
    (⊥ : LindenbaumSet (Const := Const) T) = ⟦(.bot : ClosedFormula Const)⟧ := rfl

lemma inf_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T) ⊓ ⟦ψ⟧ =
      ⟦(.and φ ψ : ClosedFormula Const)⟧ := rfl

lemma sup_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T) ⊔ ⟦ψ⟧ =
      ⟦(.or φ ψ : ClosedFormula Const)⟧ := rfl

lemma provable_iff_eq_top {φ : ClosedFormula Const} :
    Provable (Const := Const) T φ ↔
      (⟦φ⟧ : LindenbaumSet (Const := Const) T) = ⊤ := by
  rw [top_def, eq_iff]
  exact ProvablyEquivalent.provable_iff_top (Const := Const) T φ

instance : PartialOrder (LindenbaumSet (Const := Const) T) where
  le := (· ≤ ·)
  le_refl := by
    intro a
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (T := T) (φ := φ) (ψ := φ)).2 (Provable.imp_refl (T := T) φ)
  le_trans := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφψ hψχ
    exact (le_def (T := T) (φ := φ) (ψ := χ)).2 (Provable.imp_trans hφψ hψχ)
  le_antisymm := by
    intro a b hab hba
    refine Quotient.inductionOn₂ a b ?_ hab hba
    intro φ ψ hφψ hψφ
    exact (eq_iff (T := T)).2 ⟨hφψ, hψφ⟩

instance : HImp (LindenbaumSet (Const := Const) T) :=
  ⟨Quotient.lift₂ (fun φ ψ => ⟦(.imp φ ψ : ClosedFormula Const)⟧)
      (fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
        exact Quotient.sound (ProvablyEquivalent.imp_congr hφ hψ))⟩

instance : Compl (LindenbaumSet (Const := Const) T) :=
  ⟨Quotient.lift (fun φ => ⟦(.imp φ (.bot : ClosedFormula Const) : ClosedFormula Const)⟧)
      (fun φ ψ hφ => by
        exact Quotient.sound
          (ProvablyEquivalent.imp_congr hφ
            (ProvablyEquivalent.refl (Const := Const) T (.bot : ClosedFormula Const))))⟩

lemma himp_def (φ ψ : ClosedFormula Const) :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T) ⇨ ⟦ψ⟧ =
      ⟦(.imp φ ψ : ClosedFormula Const)⟧ := rfl

lemma compl_def (φ : ClosedFormula Const) :
    (⟦φ⟧ : LindenbaumSet (Const := Const) T)ᶜ =
      ⟦(.imp φ (.bot : ClosedFormula Const) : ClosedFormula Const)⟧ := rfl

instance : GeneralizedHeytingAlgebra (LindenbaumSet (Const := Const) T) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le := (· ≤ ·)
  top := ⊤
  himp := (· ⇨ ·)
  le_refl := by intro a; exact le_rfl
  le_trans := by intro a b c; exact le_trans
  le_antisymm := by intro a b; exact le_antisymm
  inf_le_left a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (T := T) (φ := .and φ ψ) (ψ := φ)).2
      (Provable.and_left (T := T) φ ψ)
  inf_le_right a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (T := T) (φ := .and φ ψ) (ψ := ψ)).2
      (Provable.and_right (T := T) φ ψ)
  le_inf a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφ hψ
    exact (le_def (T := T) (φ := φ) (ψ := .and ψ χ)).2
      (Provable.and_intro hφ hψ)
  le_sup_left a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (T := T) (φ := φ) (ψ := .or φ ψ)).2
      (Provable.or_intro_left (T := T) φ ψ)
  le_sup_right a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ
    exact (le_def (T := T) (φ := ψ) (ψ := .or φ ψ)).2
      (Provable.or_intro_right (T := T) φ ψ)
  sup_le a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ hφ hψ
    exact (le_def (T := T) (φ := .or φ ψ) (ψ := χ)).2
      (Provable.or_elim hφ hψ)
  le_top := by
    intro a
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (T := T) (φ := φ) (ψ := .top)).2
      (Provable.imp_top (T := T) φ)
  le_himp_iff a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ
    constructor
    · intro h
      exact (le_def (T := T) (φ := .and φ ψ) (ψ := χ)).2
        (Provable.imp_uncurry
          ((le_def (T := T) (φ := φ) (ψ := .imp ψ χ)).1 h))
    · intro h
      exact (le_def (T := T) (φ := φ) (ψ := .imp ψ χ)).2
        (Provable.imp_curry
          ((le_def (T := T) (φ := .and φ ψ) (ψ := χ)).1 h))

instance : HeytingAlgebra (LindenbaumSet (Const := Const) T) where
  bot := ⊥
  bot_le a := by
    refine Quotient.inductionOn a ?_
    intro φ
    exact (le_def (T := T) (φ := .bot) (ψ := φ)).2
      (Provable.bot_imp (T := T) φ)
  himp_bot a := by
    refine Quotient.inductionOn a ?_
    intro φ
    rw [compl_def, bot_def, himp_def]
  __ := inferInstanceAs (GeneralizedHeytingAlgebra (LindenbaumSet (Const := Const) T))

end LindenbaumSet

end ProvablyEquivalent

end ClosedTheorySet

end Mettapedia.Logic.HOL
