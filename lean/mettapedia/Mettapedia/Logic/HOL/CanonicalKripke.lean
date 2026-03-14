import Mathlib.Order.UpperLower.CompleteLattice
import Mettapedia.Logic.HOL.CanonicalTheory

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace ClosedTheorySet.World

/-- Canonical worlds are ordered by theory extension. -/
instance : LE (ClosedTheorySet.World Const) where
  le W V := W.carrier ⊆ V.carrier

/-- Upward-closed truth values over canonical worlds. -/
abbrev TruthVal (Const : Ty Base → Type v) :=
  UpperSet (ClosedTheorySet.World Const)

theorem mem_mono {W V : ClosedTheorySet.World Const} (hWV : W ≤ V)
    {φ : ClosedFormula Const} (hφ : φ ∈ W.carrier) :
    φ ∈ V.carrier :=
  hWV hφ

/-- The canonical truth set of a closed formula. -/
def truthSet (φ : ClosedFormula Const) : TruthVal Const where
  carrier := {W | φ ∈ W.carrier}
  upper' := by
    intro W V hWV hφ
    exact mem_mono hWV hφ

@[simp] theorem mem_truthSet_iff {W : ClosedTheorySet.World Const}
    {φ : ClosedFormula Const} :
    W ∈ truthSet (Const := Const) φ ↔ φ ∈ W.carrier :=
  Iff.rfl

@[simp] theorem mem_truthSet_top_iff {W : ClosedTheorySet.World Const} :
    W ∈ truthSet (Const := Const) (.top : ClosedFormula Const) := by
  simpa [truthSet] using W.top_mem

@[simp] theorem mem_truthSet_and_iff {W : ClosedTheorySet.World Const}
    {φ ψ : ClosedFormula Const} :
    W ∈ truthSet (Const := Const) (.and φ ψ) ↔
      W ∈ truthSet (Const := Const) φ ∧
        W ∈ truthSet (Const := Const) ψ := by
  constructor
  · intro h
    exact ⟨W.and_left_mem h, W.and_right_mem h⟩
  · rintro ⟨hφ, hψ⟩
    exact W.and_mem hφ hψ

@[simp] theorem mem_truthSet_or_iff {W : ClosedTheorySet.World Const}
    {φ ψ : ClosedFormula Const} :
    W ∈ truthSet (Const := Const) (.or φ ψ) ↔
      W ∈ truthSet (Const := Const) φ ∨
        W ∈ truthSet (Const := Const) ψ := by
  constructor
  · intro h
    exact W.prime_or h
  · intro h
    rcases h with h | h
    · exact W.or_left_mem h
    · exact W.or_right_mem h

@[simp] theorem mem_truthSet_ex_iff {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} :
    W ∈ truthSet (Const := Const) (.ex φ : ClosedFormula Const) ↔
      ∃ t : ClosedTerm Const σ,
        W ∈ truthSet (Const := Const) (instantiate (Base := Base) t φ) := by
  constructor
  · intro h
    exact W.exists_witness h
  · rintro ⟨t, ht⟩
    rcases ClosedTheorySet.provable_of_mem (Const := Const) (T := W.carrier) ht with
      ⟨Γ, hΓ, hder⟩
    exact W.mem_of_provable ⟨Γ, hΓ, ExtDerivation.exI t hder⟩

@[simp] theorem mem_truthSet_all_iff {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} :
    W ∈ truthSet (Const := Const) (.all φ : ClosedFormula Const) ↔
      ∀ t : ClosedTerm Const σ,
        W ∈ truthSet (Const := Const) (instantiate (Base := Base) t φ) := by
  constructor
  · intro hAll t
    rcases ClosedTheorySet.provable_of_mem (Const := Const) (T := W.carrier) hAll with
      ⟨Γ, hΓ, hder⟩
    exact W.mem_of_provable ⟨Γ, hΓ, ExtDerivation.allE t hder⟩
  · intro hInst
    by_contra hNot
    rcases W.all_counterexample hNot with ⟨t, ht⟩
    exact ht (hInst t)

/-- Canonical Kripke forcing clause for implication on closed formulas. -/
def ForcesImp (W : ClosedTheorySet.World Const)
    (φ ψ : ClosedFormula Const) : Prop :=
  ∀ ⦃V : ClosedTheorySet.World Const⦄, W ≤ V →
    V ∈ truthSet (Const := Const) φ →
      V ∈ truthSet (Const := Const) ψ

/-- Canonical Kripke forcing clause for negation on closed formulas. -/
def ForcesNot (W : ClosedTheorySet.World Const)
    (φ : ClosedFormula Const) : Prop :=
  ∀ ⦃V : ClosedTheorySet.World Const⦄, W ≤ V →
    V ∉ truthSet (Const := Const) φ

theorem imp_mem_implies_forcesImp {W : ClosedTheorySet.World Const}
    {φ ψ : ClosedFormula Const}
    (hImp : W ∈ truthSet (Const := Const) (.imp φ ψ)) :
    ForcesImp (Const := Const) W φ ψ := by
  intro V hWV hφ
  have hImpV : (.imp φ ψ : ClosedFormula Const) ∈ V.carrier := hWV hImp
  exact V.mp hImpV hφ

theorem not_mem_implies_forcesNot {W : ClosedTheorySet.World Const}
    {φ : ClosedFormula Const}
    (hNot : W ∈ truthSet (Const := Const) (.not φ)) :
    ForcesNot (Const := Const) W φ := by
  intro V hWV hφ
  have hNotV : (.not φ : ClosedFormula Const) ∈ V.carrier := hWV hNot
  have hBot : (.bot : ClosedFormula Const) ∈ V.carrier := by
    exact V.mem_of_provable <|
      ClosedTheorySet.provable_bot_of_not
        (Const := Const)
        (T := V.carrier)
        (ClosedTheorySet.provable_of_mem (Const := Const) hNotV)
        (ClosedTheorySet.provable_of_mem (Const := Const) hφ)
  exact V.bot_not_mem hBot

end ClosedTheorySet.World

end Mettapedia.Logic.HOL
