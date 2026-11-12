import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepExact
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesRetyped
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesHigherRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairs

/-!
# Exact arguments: what the definition gives, and its controls

**What an exact argument gives.** Let an unknown have the type `Π (z : D). C` and be applied to a local `x`.

* When `x` is declared at `D` itself, `x` is the generic point of the unknown's argument type. Abstraction over it
  is a term of the unknown's type (`exact_abstraction_typed`), and two values of the unknown that agree at it are
  equal (`exact_agreement_equal`). So `Y x ≐ t` has the solution `Y := λ x. t` and no other: the equation is a
  pattern equation.
* When `x` is declared below `D`, neither holds. Agreement at `x` does not determine the unknown
  (`ContextualDependentSweep.Witnesses.cross_two_answers`, `cross_answers_differ`), and the abstraction need not be
  typed, so there may be no solution (`fixed_unsolvable`, `loop_unsolvable`). What remains true is that the other
  side, in normal form, has to be typed with the local read at `D`
  (`ContextualDependentUniverseInjective.applied_wide_reading`).

That an exact store's equations are the pattern equations of the terms written with the inclusion of one universe
in the next cannot be stated in this development: it has one syntax, in which the inclusion is not written. The
statements above are the ones available without a second syntax.

**Controls** of `ContextualDependentSweep.storeExact`, evaluated by the kernel. Not exact: `crossStore`,
`fixedStore`, `loopStore`, `higherStore`. Exact: `raisedStore`, `narrowStore`, `pairRaisedStore`, `pairSortStore`
(all written at `U1`), `exactHigherStore`, and `wideExactStore`, where an unknown that declares `U1` for its
argument is applied to a local of `U1`; the family that reads through components (`withinTower`) commits on it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExact

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality

variable {Head : Type} {R : Rules Head}

/-- **Abstraction over a local declared at the unknown's argument type is a term of the unknown's type.** -/
theorem exact_abstraction_typed {n : Nat} {Γ : Ctx Head n} {D : Tm Head n} {C side : Tm Head (n + 1)} {u : Head}
    (formed : Typed R Γ (.pi D C) (.head u)) (hu : R.isUniverse u) (typed : Typed R (.snoc Γ D) side C) :
    Typed R Γ (.lam side) (.pi D C) :=
  Derivable.lamIntro formed hu typed

/-- **Two values of an unknown that agree at a local declared at its argument type are equal.** -/
theorem exact_agreement_equal {n : Nat} {Γ : Ctx Head n} {D first second : Tm Head n} {C : Tm Head (n + 1)}
    (typedFirst : Typed R Γ first (.pi D C)) (typedSecond : Typed R Γ second (.pi D C))
    (agree : Equal R (.snoc Γ D) (.app (Presentation.rename wk first) (.var 0))
      (.app (Presentation.rename wk second) (.var 0)) C) :
    Equal R Γ first second (.pi D C) :=
  Derivable.etaPi typedFirst typedSecond agree

end ContextualDependentExact

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-! ## Not exact -/

theorem fixed_not_exact : storeExact fixedStore = false := by decide +kernel

theorem loop_not_exact : storeExact loopStore = false := by decide +kernel

theorem higher_not_exact : storeExact higherStore = false := by decide +kernel

/-! ## Exact -/

theorem raised_exact : storeExact raisedStore = true := by decide +kernel

theorem narrow_exact : storeExact narrowStore = true := by decide +kernel

theorem pairRaised_exact : storeExact pairRaisedStore = true := by decide +kernel

theorem pairSort_exact : storeExact pairSortStore = true := by decide +kernel

theorem exactHigher_exact : storeExact exactHigherStore = true := by decide +kernel

/-- `Π (x : U1). U1`, over `P : U1 → U1`. -/
def wideExactType : TypeOver ctxWide :=
  formIn ctxWide (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `λ x. P x ≐ λ x. x` at `Π (x : U1). U1`: the local is declared at the universe `P` declares. -/
def wideExactEquation : Equation (TotalTerm ctxWide) :=
  (termIn ctxWide wideExactType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxWide wideExactType (.lam (.var 0)) (by decide +kernel))

def wideExactStore : EquationStore (TotalTerm ctxWide) := [wideExactEquation]

theorem wideExact_in_fragment : InFragmentStore wideExactStore := storeInside_sound (by decide +kernel)

/-- **A store that has exact arguments and uses the larger universe.** -/
theorem wideExact_exact : storeExact wideExactStore = true := by decide +kernel

/-- **`withinTower` commits on it**, at budget 16. -/
theorem wideExact_committed : (run (withinTower.solver 16) wideExactStore 2).readout = .commit := by
  decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
