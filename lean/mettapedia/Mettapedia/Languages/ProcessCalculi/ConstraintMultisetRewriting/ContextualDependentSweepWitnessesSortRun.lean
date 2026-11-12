import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesSort

/-!
# A universe against an unknown of a universe that does not hold it: kernel statements

`sortStore`, `X ≐ U0` at `U1` with `A X : U0`: the family that reads every equation at its least annotation is
stuck on it in its first round (`sort_least_stuck`), and the family with the refutation of a universe refutes it
(`sort_refuted`). Both runs are evaluated by the kernel, at budget 16.

`narrowStore`, `X ≐ Π (y : Y). Y` at `U1` with `A X : U0, Y : U1`: the top family is stuck on it in its first round
(`narrow_stuck`), and the store is solvable (`narrow_gap`).
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

/-- **The family below is stuck in its first round** on `X ≐ U0` at `U1`, at budget 16. -/
theorem sort_least_stuck : isStuck (run (leastTower.solver 16) sortStore 1) = true := by decide +kernel

/-- **The family with the refutation of a universe refutes the store** in its first round, at budget 16. -/
theorem sort_refuted : (run (sortTower.solver 16) sortStore 1).readout = .refuted := by decide +kernel

/-- **A store of the fragment without solution, stuck under the family below, refuted by this family.** -/
theorem sort_repaired : InFragmentStore sortStore ∧ ¬ (frames setting.levels).Solvable sortStore ∧
    isStuck (run (leastTower.solver 16) sortStore 1) = true ∧
    (run (sortTower.solver 16) sortStore 1).readout = .refuted :=
  ⟨sort_in_fragment, sort_unsolvable, sort_least_stuck, sort_refuted⟩

/-- **The top family is stuck in its first round** on `X ≐ Π (y : Y). Y` at `U1`, at budget 16. -/
theorem narrow_stuck : isStuck (run (sortTower.solver 16) narrowStore 1) = true := by decide +kernel

/-- **A store of the fragment, solvable, on which the top family is stuck.** -/
theorem narrow_gap : InFragmentStore narrowStore ∧ (frames setting.levels).Solvable narrowStore ∧
    isStuck (run (sortTower.solver 16) narrowStore 1) = true :=
  ⟨narrow_in_fragment, narrow_solvable, narrow_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
