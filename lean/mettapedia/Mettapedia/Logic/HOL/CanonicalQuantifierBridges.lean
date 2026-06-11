import Mettapedia.Logic.HOL.CanonicalTheory

/-!
# Quantifier bridges for `ClosedTheorySet.Provable`

The canonical-model truth lemma needs the quantifier analogues of the existing
propositional `Provable` helpers (`provable_mp`, `provable_and_intro`, …).  This
file adds the two structural quantifier bridges that follow directly from the
`ExtDerivation` rules:

* `provable_all_elim`  — universal instantiation;
* `provable_ex_intro`  — existential introduction at a witness.

The harder fresh-constant generalization (`provable_all_intro_fresh`), which
turns a derivation over a fresh parameter into a universal statement, is built
separately on top of the substitution machinery.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Universal instantiation at a closed witness: from `∀x.φ` provable over `T`,
`φ[t]` is provable over `T`. -/
theorem provable_all_elim {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : Provable (Const := Const) T (.all φ)) :
    Provable (Const := Const) T (instantiate (Base := Base) t φ) := by
  rcases h with ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, hΓ, ExtDerivation.allE (Base := Base) t hd⟩

/-- Existential introduction at a closed witness: from `φ[t]` provable over `T`,
`∃x.φ` is provable over `T`. -/
theorem provable_ex_intro {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : Provable (Const := Const) T (instantiate (Base := Base) t φ)) :
    Provable (Const := Const) T (.ex φ) := by
  rcases h with ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, hΓ, ExtDerivation.exI (Base := Base) t hd⟩

/-- World-level universal elimination: if `∀x.φ ∈ W` then every instance is in `W`. -/
theorem World.all_elim_mem {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : (.all φ : ClosedFormula Const) ∈ W.carrier) :
    instantiate (Base := Base) t φ ∈ W.carrier := by
  apply World.mem_of_provable (W := W)
  exact provable_all_elim (Const := Const) t (provable_of_mem (Const := Const) h)

/-- World-level existential introduction: if some instance `φ[t] ∈ W` then `∃x.φ ∈ W`. -/
theorem World.ex_intro_mem {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : instantiate (Base := Base) t φ ∈ W.carrier) :
    (.ex φ : ClosedFormula Const) ∈ W.carrier := by
  apply World.mem_of_provable (W := W)
  exact provable_ex_intro (Const := Const) t (provable_of_mem (Const := Const) h)

end ClosedTheorySet
end Mettapedia.Logic.HOL
