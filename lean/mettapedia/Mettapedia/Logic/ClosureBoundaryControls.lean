import Mettapedia.Logic.FiniteHornClosureCharacterization
import Mathlib.Data.Set.Finite.Lattice

/-! Sharp semantic boundaries for closure responses. An infinite-carrier
closure can require genuinely infinite support. Visible absence can also
destroy monotonicity even when every transition only adds facts. -/

set_option autoImplicit false

namespace Mettapedia.Logic.FiniteHornClosureCharacterization

/-- Seeing infinitely many distinct facts licenses every conclusion. -/
noncomputable def infiniteCompletion (seed : Set Nat) : Set Nat := by
  classical
  exact if seed.Finite then seed else Set.univ

theorem infiniteCompletion_laws : ClosureLaws infiniteCompletion := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro seed
    by_cases finite : seed.Finite <;> simp [infiniteCompletion, finite]
  · intro first second included
    by_cases firstFinite : first.Finite
    · rw [infiniteCompletion, if_pos firstFinite]
      by_cases secondFinite : second.Finite
      · simpa [infiniteCompletion, secondFinite] using included
      · simp [infiniteCompletion, secondFinite]
    · have secondInfinite : ¬ second.Finite := fun finite => firstFinite (finite.subset included)
      simp [infiniteCompletion, firstFinite, secondInfinite]
  · intro seed
    by_cases finite : seed.Finite
    · simp [infiniteCompletion, finite]
    · simp [infiniteCompletion, finite, Set.infinite_univ]

theorem infiniteCompletion_not_finitely_supported : ¬ FinitelySupported infiniteCompletion := by
  classical
  intro support
  let positive : Set Nat := {number | 0 < number}
  have infinite : positive.Infinite := by
    have range : Set.range Nat.succ ⊆ positive := by rintro value ⟨number, rfl⟩; exact Nat.zero_lt_succ number
    exact (Set.infinite_range_of_injective Nat.succ_injective).mono range
  have derives : 0 ∈ infiniteCompletion positive := by simp [infiniteCompletion, infinite.not_finite]
  obtain ⟨premises, contained, zero⟩ := support positive 0 derives
  have finite : ({number | number ∈ premises} : Set Nat).Finite := by
    exact Set.Finite.ofFinset premises.toFinset (by simp)
  rw [infiniteCompletion, if_pos finite] at zero
  have impossible : 0 < (0 : Nat) := contained 0 zero
  omega

theorem infiniteCompletion_has_no_finitary_presentation :
    ¬ ∃ rules : List Nat → Nat → Prop, ∀ seed atom,
      atom ∈ infiniteCompletion seed ↔ FinitaryClosure.close rules (· ∈ seed) atom := by
  intro presentation
  exact infiniteCompletion_not_finitely_supported
    ((finitary_horn_characterization infiniteCompletion).mpr presentation).2

/-- Rule: when `false` is absent, insert `true`; retain all input facts. -/
def absenceResponse (seed : Set Bool) : Set Bool :=
  seed ∪ {atom | atom = true ∧ false ∉ seed}

theorem absenceResponse_extensive : ∀ seed, seed ⊆ absenceResponse seed := fun _ _ member => Or.inl member

theorem absenceResponse_not_monotone : ¬ Monotone absenceResponse := by
  intro monotone
  have result := monotone (show (∅ : Set Bool) ⊆ {false} from Set.empty_subset _) (by
    show true ∈ absenceResponse ∅
    exact Or.inr ⟨rfl, by simp⟩)
  simp [absenceResponse] at result

/-- Consume/reinsert changes an occurrence's identity but not its payload set. -/
def payload (_occurrence : Nat) : Bool := true

theorem consumption_need_not_change_value_observation :
    ({0} : Set Nat) ≠ {1} ∧ payload '' ({0} : Set Nat) = payload '' ({1} : Set Nat) := by
  constructor
  · intro same
    have impossible : (0 : Nat) ∈ ({1} : Set Nat) := same ▸ Set.mem_singleton 0
    simp at impossible
  · simp [payload]

end Mettapedia.Logic.FiniteHornClosureCharacterization
