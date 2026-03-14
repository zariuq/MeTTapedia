import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Lindenbaum

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A closed HOL theory presented as a set of closed formulas. -/
abbrev ClosedTheorySet (Const : Ty Base → Type v) := Set (ClosedFormula Const)

namespace ClosedTheorySet

/-- Finite-context derivability from a set of closed HOL formulas. -/
def Provable (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Prop :=
  ∃ Γ : ClosedTheory Const,
    (∀ ψ, ψ ∈ Γ → ψ ∈ T) ∧ ClosedTheory.Provable (Const := Const) Γ φ

/-- A set of closed formulas is deductively closed when every finitely derivable formula belongs to it. -/
def DeductivelyClosed (T : ClosedTheorySet Const) : Prop :=
  ∀ {φ : ClosedFormula Const}, Provable (Const := Const) T φ → φ ∈ T

/-- Inconsistency means finite derivability of falsity. -/
def Inconsistent (T : ClosedTheorySet Const) : Prop :=
  Provable (Const := Const) T (.bot : ClosedFormula Const)

/-- Consistency is absence of a finite derivation of falsity. -/
def Consistent (T : ClosedTheorySet Const) : Prop :=
  ¬Inconsistent (Const := Const) T

theorem provable_mono {T U : ClosedTheorySet Const}
    (hTU : ∀ {φ : ClosedFormula Const}, φ ∈ T → φ ∈ U) :
    Provable (Const := Const) T φ →
      Provable (Const := Const) U φ := by
  rintro ⟨Γ, hΓ, hφ⟩
  refine ⟨Γ, ?_, hφ⟩
  intro ψ hψ
  exact hTU (hΓ ψ hψ)

theorem provable_of_closedTheory {Δ : ClosedTheory Const}
    (hΔ : ∀ {φ : ClosedFormula Const}, φ ∈ Δ → φ ∈ T)
    (hφ : ClosedTheory.Provable (Const := Const) Δ φ) :
    Provable (Const := Const) T φ :=
  ⟨Δ, by intro ψ hψ; exact hΔ hψ, hφ⟩

theorem provable_of_mem {T : ClosedTheorySet Const} (hφ : φ ∈ T) :
    Provable (Const := Const) T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact hφ
  · exact .hyp (by simp)

theorem provable_top (T : ClosedTheorySet Const) :
    Provable (Const := Const) T (.top : ClosedFormula Const) := by
  refine ⟨[], ?_, ?_⟩
  · intro ψ hψ
    cases hψ
  · exact .topI

theorem provable_imp_refl (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) T (.imp φ φ) := by
  refine ⟨[], ?_, ?_⟩
  · intro ψ hψ
    cases hψ
  · exact ClosedTheory.Provable.imp_refl (Δ := []) (Const := Const) (φ := φ)

theorem provable_mp {T : ClosedTheorySet Const}
    (hImp : Provable (Const := Const) T (.imp φ ψ))
    (hφ : Provable (Const := Const) T φ) :
    Provable (Const := Const) T ψ := by
  rcases hImp with ⟨Γ₁, hΓ₁, hImp⟩
  rcases hφ with ⟨Γ₂, hΓ₂, hφ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · exact
      ExtDerivation.impE
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := .imp φ ψ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inl hξ))
          hImp)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := φ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inr hξ))
          hφ)

theorem provable_and_intro {T : ClosedTheorySet Const}
    (hφ : Provable (Const := Const) T φ)
    (hψ : Provable (Const := Const) T ψ) :
    Provable (Const := Const) T (.and φ ψ) := by
  rcases hφ with ⟨Γ₁, hΓ₁, hφ⟩
  rcases hψ with ⟨Γ₂, hΓ₂, hψ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · exact
      ExtDerivation.andI
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := φ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inl hξ))
          hφ)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := ψ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inr hξ))
          hψ)

theorem provable_and_left {T : ClosedTheorySet Const}
    (h : Provable (Const := Const) T (.and φ ψ)) :
    Provable (Const := Const) T φ := by
  exact provable_mp
    (T := T)
    (φ := .and φ ψ)
    (ψ := φ)
    (provable_of_closedTheory
      (Const := Const)
      (T := T)
      (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      (hφ := ClosedTheory.Provable.and_left (Δ := []) (Const := Const) (φ := φ) (ψ := ψ)))
    h

theorem provable_and_right {T : ClosedTheorySet Const}
    (h : Provable (Const := Const) T (.and φ ψ)) :
    Provable (Const := Const) T ψ := by
  exact provable_mp
    (T := T)
    (φ := .and φ ψ)
    (ψ := ψ)
    (provable_of_closedTheory
      (Const := Const)
      (T := T)
      (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      (hφ := ClosedTheory.Provable.and_right (Δ := []) (Const := Const) (φ := φ) (ψ := ψ)))
    h

theorem provable_or_intro_left {T : ClosedTheorySet Const}
    (h : Provable (Const := Const) T φ) :
    Provable (Const := Const) T (.or φ ψ) := by
  exact provable_mp
    (T := T)
    (φ := φ)
    (ψ := .or φ ψ)
    (provable_of_closedTheory
      (Const := Const)
      (T := T)
      (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      (hφ := ClosedTheory.Provable.or_intro_left (Δ := []) (Const := Const) (φ := φ) (ψ := ψ)))
    h

theorem provable_or_intro_right {T : ClosedTheorySet Const}
    (h : Provable (Const := Const) T ψ) :
    Provable (Const := Const) T (.or φ ψ) := by
  exact provable_mp
    (T := T)
    (φ := ψ)
    (ψ := .or φ ψ)
    (provable_of_closedTheory
      (Const := Const)
      (T := T)
      (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      (hφ := ClosedTheory.Provable.or_intro_right (Δ := []) (Const := Const) (φ := φ) (ψ := ψ)))
    h

theorem provable_not_of_bot {T : ClosedTheorySet Const}
    (h : Provable (Const := Const) T (.bot : ClosedFormula Const)) :
    Provable (Const := Const) T (.not φ) := by
  rcases h with ⟨Γ, hΓ, hbot⟩
  refine ⟨Γ, hΓ, ?_⟩
  exact ExtDerivation.notI (ExtDerivation.mono (Δ := Γ) (Δ' := φ :: Γ) (φ := .bot)
    (by
      intro ξ hξ
      simp [hξ])
    hbot)

theorem provable_bot_of_not {T : ClosedTheorySet Const}
    (hNot : Provable (Const := Const) T (.not φ))
    (hφ : Provable (Const := Const) T φ) :
    Provable (Const := Const) T (.bot : ClosedFormula Const) := by
  rcases hNot with ⟨Γ₁, hΓ₁, hNot⟩
  rcases hφ with ⟨Γ₂, hΓ₂, hφ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · exact
      ExtDerivation.notE
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := .not φ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inl hξ))
          hNot)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := φ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inr hξ))
          hφ)

/-- A canonical-world candidate for the future intuitionistic HOL completeness proof. -/
structure World (Const : Ty Base → Type v) where
  carrier : ClosedTheorySet Const
  closed : DeductivelyClosed (Const := Const) carrier
  consistent : Consistent (Const := Const) carrier
  prime_or :
    ∀ {φ ψ : ClosedFormula Const},
      (.or φ ψ : ClosedFormula Const) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier
  exists_witness :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.ex φ : ClosedFormula Const) ∈ carrier →
        ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ carrier
  all_counterexample :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.all φ : ClosedFormula Const) ∉ carrier →
        ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∉ carrier

namespace World

variable {W : ClosedTheorySet.World Const}

theorem mem_of_provable {φ : ClosedFormula Const}
    (h : Provable (Const := Const) W.carrier φ) :
    φ ∈ W.carrier :=
  W.closed h

theorem top_mem : (.top : ClosedFormula Const) ∈ W.carrier :=
  mem_of_provable (W := W) (provable_top (Const := Const) W.carrier)

theorem mp {φ ψ : ClosedFormula Const}
    (hImp : (.imp φ ψ : ClosedFormula Const) ∈ W.carrier)
    (hφ : φ ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_mp (Const := Const)
    (provable_of_mem (Const := Const) hImp)
    (provable_of_mem (Const := Const) hφ)

theorem and_mem {φ ψ : ClosedFormula Const}
    (hφ : φ ∈ W.carrier) (hψ : ψ ∈ W.carrier) :
    (.and φ ψ : ClosedFormula Const) ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_and_intro (Const := Const)
    (provable_of_mem (Const := Const) hφ)
    (provable_of_mem (Const := Const) hψ)

theorem and_left_mem {φ ψ : ClosedFormula Const}
    (h : (.and φ ψ : ClosedFormula Const) ∈ W.carrier) :
    φ ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_and_left (Const := Const) (provable_of_mem (Const := Const) h)

theorem and_right_mem {φ ψ : ClosedFormula Const}
    (h : (.and φ ψ : ClosedFormula Const) ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_and_right (Const := Const) (provable_of_mem (Const := Const) h)

theorem or_left_mem {φ ψ : ClosedFormula Const}
    (h : φ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula Const) ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_or_intro_left (Const := Const) (provable_of_mem (Const := Const) h)

theorem or_right_mem {φ ψ : ClosedFormula Const}
    (h : ψ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula Const) ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_or_intro_right (Const := Const) (provable_of_mem (Const := Const) h)

theorem not_mem_of_bot {φ : ClosedFormula Const}
    (h : (.bot : ClosedFormula Const) ∈ W.carrier) :
    (.not φ : ClosedFormula Const) ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_not_of_bot (Const := Const) (provable_of_mem (Const := Const) h)

theorem bot_not_mem : (.bot : ClosedFormula Const) ∉ W.carrier := by
  intro hbot
  exact W.consistent (provable_of_mem (Const := Const) hbot)

end World

end ClosedTheorySet

end Mettapedia.Logic.HOL
