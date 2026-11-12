import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnesses

/-!
# The witnesses at a Σ base type and with two projections, reduced to the compiled run

The kernel run of the base family's first round on `sigmaBaseStore` needs more memory than the checking budget
allows, so stuckness of the base family on it is **not** a kernel statement here. What is proved is the reduction to
the compiled run: if the compiled run of the base family reads `stuck` on the store, then the store is a store of the
fragment, solvable, on which the base family is stuck (`sigmaBase_gap_of_ending`, `nested_gap_of_ending`). The
compiled run does read `stuck` on both stores, at budgets 16, 64 and 256; that reading is an evaluation, not a
theorem.

The witness with a projection below an application is a kernel statement
(`ContextualDependentSweepWitnessesStuck.below_gap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth ContextualDependentEtaDepth.BaseControls

/-- **A projection at a Σ base type**: the store is in the fragment and solvable, and the base family is stuck on it
at every budget and number of rounds at which the compiled run reads `stuck`. -/
theorem sigmaBase_gap_of_ending {fuel rounds : Nat} (read : ending fuel rounds ctxAX sigmaBaseStore = .stuck) :
    InFragmentStore sigmaBaseStore ∧ (frames setting.levels).Solvable sigmaBaseStore ∧
      isStuck (run (baseTower.solver fuel) sigmaBaseStore rounds) = true :=
  ⟨sigmaBase_in_fragment, sigmaBase_solvable, stuck_of_ending read⟩

/-- **Two projections above an application at an applied base type**: the store is in the fragment and solvable, and
the base family is stuck on it at every budget and number of rounds at which the compiled run reads `stuck`. -/
theorem nested_gap_of_ending {fuel rounds : Nat} (read : ending fuel rounds ctxAX nestedStore = .stuck) :
    InFragmentStore nestedStore ∧ (frames setting.levels).Solvable nestedStore ∧
      isStuck (run (baseTower.solver fuel) nestedStore rounds) = true :=
  ⟨nested_in_fragment, nested_solvable, stuck_of_ending read⟩

/-- The same reduction for the witness with a projection below an application, at every budget. -/
theorem below_gap_of_ending {fuel rounds : Nat} (read : ending fuel rounds ctxAX belowStore = .stuck) :
    InFragmentStore belowStore ∧ (frames setting.levels).Solvable belowStore ∧
      isStuck (run (baseTower.solver fuel) belowStore rounds) = true :=
  ⟨below_in_fragment, below_solvable, stuck_of_ending read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
