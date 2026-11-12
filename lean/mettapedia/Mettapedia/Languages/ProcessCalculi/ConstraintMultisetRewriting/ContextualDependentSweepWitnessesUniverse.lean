import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnesses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepBound

/-!
# A stuck family at the second universe: an unknown equated above its own universe

The sweep at `U1` finds stores of the dynamic pattern fragment, with solutions, on which the family with the occurs
rule at a bound variable is stuck. The simplest (`raisedStore`), over `A : U0, X : U0`:

  `X ≐ A`  at  `U1`.

Both sides are types of `U0`, compared at `U1` by cumulativity. The same sides at `U0` commit by `X := A`
(`smallStore`); at `U1` no reader fires. The store is in the fragment (`raised_in_fragment`) and solvable by
`X := A` (`raised_solvable`), and the family is stuck on it wherever its compiled run reads `stuck`
(`raised_gap_of_ending`); the compiled run reads `stuck` at budgets 16, 64 and 256. That reading is an evaluation,
not a theorem; the kernel statement at budget 16 is in `ContextualDependentSweepWitnessesUniverseStuck`.

**A second store** (`raisedPiStore`): `X ≐ Π (_ : A). A` at `U1`. The same sides at `U0` commit by
`X := Π (_ : A). A`. Here only membership in the fragment is stated (`raisedPi_in_fragment`), with the reduction to
the compiled reading (`raisedPi_stuck_of_ending`); its solvability is not proved in this module.

**Control.** `X ≐ A` at `U0` is committed wherever the compiled run reads `committed` (`small_committed_of_ending`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-- `U1`, over `A X`. -/
def largeType : TypeOver ctxAX := formIn ctxAX (.head (.sort (.succ Tower.zero))) (by decide +kernel)

/-- `U0`, over `A X`. -/
def smallType : TypeOver ctxAX := formIn ctxAX u0 (by decide +kernel)

/-- `X ≐ A` at `U1`. -/
def raisedEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX largeType (.var 0) (by decide +kernel), termIn ctxAX largeType (.var 1) (by decide +kernel))
def raisedStore : EquationStore (TotalTerm ctxAX) := [raisedEquation]

/-- The raw problem of the sweep. -/
def raisedProblem : Problem := { unknowns := [.u0, .u0], equations := [(.u1, .var 0, .var 1)] }

theorem raised_in_fragment : InFragmentStore raisedStore := storeInside_sound (by decide +kernel)

theorem raised_solvable : (frames setting.levels).Solvable raisedStore :=
  solvable_of_accepted raisedEquation.1.2 raisedEquation.2.2 (by decide +kernel)

/-- **An unknown equated above its own universe**: the store is in the fragment and solvable, and the family with
the occurs rule at a bound variable is stuck on it at every budget and number of rounds at which its compiled run
reads `stuck`. -/
theorem raised_gap_of_ending {fuel rounds : Nat} (read : endingBound fuel rounds ctxAX raisedStore = .stuck) :
    InFragmentStore raisedStore ∧ (frames setting.levels).Solvable raisedStore ∧
      isStuck (run (boundTower.solver fuel) raisedStore rounds) = true :=
  ⟨raised_in_fragment, raised_solvable, stuck_of_endingBound read⟩

/-! ## A former against the unknown, above its universe -/

/-- `X ≐ Π (_ : A). A` at `U1`. -/
def raisedPiEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX largeType (.var 0) (by decide +kernel),
    termIn ctxAX largeType (.pi (.var 1) (.var 2)) (by decide +kernel))
def raisedPiStore : EquationStore (TotalTerm ctxAX) := [raisedPiEquation]

theorem raisedPi_in_fragment : InFragmentStore raisedPiStore := storeInside_sound (by decide +kernel)

/-- The family is stuck on the store wherever its compiled run reads `stuck`. -/
theorem raisedPi_stuck_of_ending {fuel rounds : Nat} (read : endingBound fuel rounds ctxAX raisedPiStore = .stuck) :
    InFragmentStore raisedPiStore ∧ isStuck (run (boundTower.solver fuel) raisedPiStore rounds) = true :=
  ⟨raisedPi_in_fragment, stuck_of_endingBound read⟩

/-! ## Control: the same sides at their own universe -/

/-- `X ≐ A` at `U0`. -/
def smallEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX smallType (.var 0) (by decide +kernel), termIn ctxAX smallType (.var 1) (by decide +kernel))
def smallStore : EquationStore (TotalTerm ctxAX) := [smallEquation]

theorem small_in_fragment : InFragmentStore smallStore := storeInside_sound (by decide +kernel)

/-- At `U0` the family commits wherever its compiled run reads `committed`. -/
theorem small_committed_of_ending {fuel rounds : Nat} (read : endingBound fuel rounds ctxAX smallStore = .committed) :
    InFragmentStore smallStore ∧ (run (boundTower.solver fuel) smallStore rounds).readout = .commit :=
  ⟨small_in_fragment, committed_of_endingBound read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
