import Mettapedia.GSLT.Core.Web
import Mathlib.Logic.Equiv.Finset

/-! Positive and negative controls for finite-input graph semantics. -/

namespace Mettapedia.GSLT.Core.GraphModel

/-- A genuine infinite web with injective coding, used by concrete controls. -/
def naturalModel : GraphModel where
  web := {
    carrier := Nat
    decEq := inferInstance
    infinite := inferInstance
  }
  coding := {
    code := fun input : Finset Nat × Nat => Encodable.encode input
    injective := @Encodable.encode_injective (Finset Nat × Nat) inferInstance
  }

variable (D : GraphModel)

/-- The encoded identity returns the actual argument set. -/
theorem identity_application (arguments : Set D.Carrier) :
    D.apply (D.abstraction id) arguments = arguments :=
  D.apply_abstraction id ScottContinuous.id arguments

/-- Distinct inputs cannot be replaced by one constant result. -/
theorem identity_distinguishes_inputs (e d : D.Carrier) (h : e ≠ d) :
    D.apply (D.abstraction id) {e} ≠ D.apply (D.abstraction id) {d} := by
  rw [D.identity_application, D.identity_application]
  intro hSets
  exact h (Set.singleton_injective hSets)

/-- The function argument authorizes outputs, even for an empty input. -/
theorem constant_not_empty_function (e : D.Carrier) :
    D.apply (D.abstraction (fun _ => ({e} : Set D.Carrier))) ∅ ≠ D.apply ∅ ∅ := by
  rw [D.apply_abstraction (fun _ => ({e} : Set D.Carrier))
    (ScottContinuous.const _), D.apply_empty]
  exact Set.singleton_ne_empty e

/-- Empty arguments do not forbid a constant graph's output. -/
theorem constant_empty_argument (e : D.Carrier) :
    e ∈ D.apply (D.abstraction (fun _ => ({e} : Set D.Carrier))) ∅ := by
  rw [D.apply_abstraction (fun _ => ({e} : Set D.Carrier)) (ScottContinuous.const _)]
  exact Set.mem_singleton e

/-- A monotone function with no finite witness for its infinite-input output. -/
noncomputable def infiniteOnly (e : D.Carrier)
    (arguments : Set D.Carrier) : Set D.Carrier := by
  classical
  exact if arguments.Finite then ∅ else {e}

theorem infiniteOnly_monotone (e : D.Carrier) : Monotone (D.infiniteOnly e) := by
  classical
  intro A B hSubset
  by_cases hA : A.Finite
  · simp [infiniteOnly, hA]
  · have hB : ¬B.Finite := fun hB => hA (hB.subset hSubset)
    simp only [infiniteOnly, hA, hB, ↓reduceIte]
    exact Set.Subset.rfl

theorem abstraction_infiniteOnly (e : D.Carrier) :
    D.abstraction (D.infiniteOnly e) = ∅ := by
  classical
  ext token
  simp [abstraction, infiniteOnly, Finset.finite_toSet]

/-- Monotonicity is insufficient for F(G(f)) = f. -/
theorem infiniteOnly_retraction_fails (e : D.Carrier) :
    D.apply (D.abstraction (D.infiniteOnly e)) Set.univ ≠ D.infiniteOnly e Set.univ := by
  classical
  rw [D.abstraction_infiniteOnly, D.apply_empty]
  have hInfinite : ¬(Set.univ : Set D.Carrier).Finite := Set.infinite_univ
  simp [infiniteOnly, hInfinite]

theorem infiniteOnly_not_scottContinuous (e : D.Carrier) :
    ¬ScottContinuous (D.infiniteOnly e) := by
  intro h
  exact D.infiniteOnly_retraction_fails e (D.apply_abstraction _ h Set.univ)

/-- The generic distinct-input control has an inhabited concrete instance. -/
theorem naturalModel_distinct_identity_inputs :
    naturalModel.apply (naturalModel.abstraction id) ({0} : Set Nat) ≠
      naturalModel.apply (naturalModel.abstraction id) ({1} : Set Nat) :=
  naturalModel.identity_distinguishes_inputs (0 : Nat) (1 : Nat)
    (show (0 : Nat) ≠ 1 by decide)

/-- A concrete monotone map violates the proposed unconditional retraction. -/
theorem naturalModel_monotone_not_retracting :
    Monotone (naturalModel.infiniteOnly (0 : Nat)) ∧
      naturalModel.apply (naturalModel.abstraction (naturalModel.infiniteOnly (0 : Nat))) Set.univ ≠
        naturalModel.infiniteOnly (0 : Nat) Set.univ :=
  ⟨naturalModel.infiniteOnly_monotone (0 : Nat),
    naturalModel.infiniteOnly_retraction_fails (0 : Nat)⟩

end Mettapedia.GSLT.Core.GraphModel
