import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Representation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.DirectCuts.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-!
This module is the public entry point for the Knuth–Skilling (Appendix A) *representation theorem*.

## Design note (keep the API light)

The grid/induction proof path (`...Additive/Proofs/GridInduction/Main.lean`) is large and may be expensive to
compile. This entrypoint therefore exposes a small, proof-agnostic interface
`HasRepresentationTheorem` whose instances can be provided by different proof paths.

Included here (lightweight):
- Hölder embedding (`...Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean`):
  assumes `NoAnomalousPairs`.
- Dedekind cuts (`...Additive/Proofs/DirectCuts/Main.lean`): assumes `KSSeparationStrict`.

For the full “three-path” comparison (including the grid/induction instance), import:
`Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Comparison`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical
open KSSemigroupBase
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.AnomalousPairs
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding

/-- Hölder proof path: `NoAnomalousPairs` gives a representation via `OrderedSemigroups`. -/
instance holder_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    HasRepresentationTheorem α where
  exists_representation := representation_semigroup (α := α)

/-- Cuts proof path: Dedekind cuts on the `KSSeparationStrict` grid. -/
instance cuts_hasRepresentationTheorem
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [KSSeparationStrict α] :
    HasRepresentationTheorem α where
  exists_representation := by
    obtain ⟨Θ, hΘ_order, _hΘ_ident, hΘ_add⟩ :=
      Alternative.associativity_representation_cuts α
    exact ⟨Θ, hΘ_order, hΘ_add⟩

/-- Unified entry point: any instantiation of `HasRepresentationTheorem α` yields a K&S additive
order representation `Θ : α → ℝ`. -/
theorem exists_Theta_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  simpa using (HasRepresentationTheorem.exists_representation (α := α))

/-- Commutativity follows from any additive order representation. -/
theorem op_comm_of_hasRepresentationTheorem
    (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x := by
  obtain ⟨Θ, hΘ_order, hΘ_add⟩ := HasRepresentationTheorem.exists_representation (α := α)
  intro x y
  have h1 : Θ (op x y) = Θ x + Θ y := hΘ_add x y
  have h2 : Θ (op y x) = Θ y + Θ x := hΘ_add y x
  have h3 : Θ x + Θ y = Θ y + Θ x := add_comm (Θ x) (Θ y)
  have h4 : Θ (op x y) = Θ (op y x) := by rw [h1, h2, h3]
  have hΘ_inj : Function.Injective Θ := by
    intro a b hab
    have ha : a ≤ b := (hΘ_order a b).mpr (le_of_eq hab)
    have hb : b ≤ a := (hΘ_order b a).mpr (le_of_eq hab.symm)
    exact le_antisymm ha hb
  exact hΘ_inj h4

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
