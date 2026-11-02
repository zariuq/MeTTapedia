import Mettapedia.Logic.FiniteHornClosureCharacterization
import Mettapedia.GSLT.OpenEnded.ClosureSystems

/-! Finite support is precisely preservation of nonempty directed unions.
The proof transports list premises to the existing finite-set Horn theorem;
monotonicity supplies the reverse inclusion. Closure laws alone do not
identify an infinite-carrier response with a finitary implementation. -/

set_option autoImplicit false

namespace Mettapedia.Logic.FiniteHornClosureCharacterization

open Set

variable {A : Type*}

def DirectedContinuous (response : Set A → Set A) : Prop :=
  ∀ family : Set (Set A), family.Nonempty → DirectedOn (· ⊆ ·) family →
    response (⋃₀ family) = ⋃ seed ∈ family, response seed

theorem finite_support_iff_directed_continuous (response : Set A → Set A) (monotone : Monotone response) :
    FinitelySupported response ↔ DirectedContinuous response := by
  classical
  let T : Set A →o Set A := ⟨response, monotone⟩
  open Mettapedia.GSLT.OpenEnded.ClosureSystems in
  have presentation : FinitelySupported response ↔ oneStep (finitaryRulesOf T) ∅ = T := by
    constructor
    · intro support
      ext seed atom
      constructor
      · rintro (impossible | ⟨clause, ⟨_, valid⟩, included, rfl⟩)
        · exact impossible.elim
        · exact monotone included valid
      · intro member
        obtain ⟨premises, included, valid⟩ := support seed atom member
        exact Or.inr ⟨⟨{premise | premise ∈ premises}, atom⟩,
          ⟨Set.Finite.ofFinset premises.toFinset (by simp), valid⟩, included, rfl⟩
    · intro same seed atom member
      have generated : atom ∈ oneStep (finitaryRulesOf T) ∅ seed := by rw [same]; exact member
      rcases generated with impossible | ⟨clause, ⟨finite, valid⟩, included, rfl⟩
      · exact impossible.elim
      · exact ⟨finite.toFinset.toList, by simpa using (fun premise present => included present), by simpa [T] using valid⟩
  rw [presentation, Mettapedia.GSLT.OpenEnded.ClosureSystems.oneStep_finitaryRulesOf_iff]
  constructor
  · intro preserves family nonempty directed
    exact Set.Subset.antisymm (preserves family nonempty directed)
      (Set.iUnion₂_subset fun seed present => monotone (Set.subset_sUnion_of_mem present))
  · intro continuous family nonempty directed
    exact (continuous family nonempty directed).subset

theorem continuous_closure_iff_finitary_rules (response : Set A → Set A) :
    ClosureLaws response ∧ DirectedContinuous response ↔
      ∃ rules : List A → A → Prop, ∀ seed atom,
        atom ∈ response seed ↔ FinitaryClosure.close rules (· ∈ seed) atom := by
  rw [← finitary_horn_characterization]
  exact and_congr_right (fun laws => (finite_support_iff_directed_continuous response laws.2.1).symm)

end Mettapedia.Logic.FiniteHornClosureCharacterization
