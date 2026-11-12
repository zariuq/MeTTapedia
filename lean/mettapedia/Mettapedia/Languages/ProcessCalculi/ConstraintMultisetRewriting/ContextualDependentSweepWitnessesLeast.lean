import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesUniverse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepLeast

/-!
# The stuck stores of the second universe under the family that reads at the least annotation

`raisedStore`, `X ≐ A` at `U1` with `A X : U0`, has exactly the solutions of `smallStore`, the same sides at `U0`
(`raised_iff_small`): the reading of the equation at `U0` is built by hand (`raisedLowered`) and its solutions are
those of the equation by `Lowered.solves`. This is the injectivity of the inclusion of `U0` in `U1` on these codes.

The family that reads every equation at its least annotation commits on `raisedStore` and on `raisedPiStore`
wherever its compiled run reads `committed` (`raised_least_committed_of_ending`,
`raisedPi_least_committed_of_ending`); the kernel statements are in
`ContextualDependentSweepWitnessesLeastRun`.

**Negative control** (`sortStore`): `X ≐ U0` at `U1`. The right side is not a term of `U0`, and no candidate
universe reads the equation lower (`sort_not_lowered`); the candidate `U0` reads `X ≐ A` lower (`raised_lowered`).
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
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective

/-! ## The raised equation read at `U0` -/

/-- A type formed by the budgeted formation of types has the code it was formed from. -/
theorem formIn_code (Γ : Context setting.R) (code : Tower.Tm Γ.arity)
    (accepted : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 Γ code).isSome) :
    (formIn Γ code accepted).code = code :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 Γ code).get accepted).property

/-- `U0` over `A X` is `U1` over `A X` with its universe lowered. -/
theorem small_lowers_large : Lowers setting.R smallType.code largeType.code := by
  have small : smallType.code = .head (.sort Tower.zero) := formIn_code _ _ _
  have large : largeType.code = .head (.sort (.succ Tower.zero)) := formIn_code _ _ _
  rw [small, large]
  exact .sort (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The reading of `X ≐ A` at `U0`.** -/
def raisedLowered : Lowered (S := setting) raisedEquation where
  small := smallType
  lowers := small_lowers_large
  left := smallEquation.1.2
  right := smallEquation.2.2
  leftCode := rfl
  rightCode := rfl

/-- **`X ≐ A` at `U1` has exactly the solutions of `X ≐ A` at `U0`.** -/
theorem raised_iff_small {Δ : Context setting.R} (σ : Δ ⟶ ctxAX) :
    (frames setting.levels).Solves σ smallEquation ↔ (frames setting.levels).Solves σ raisedEquation :=
  raisedLowered.solves (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete σ rfl

/-- The family commits on `X ≐ A` at `U1` wherever its compiled run reads `committed`. -/
theorem raised_least_committed_of_ending {fuel rounds : Nat}
    (read : endingLeast fuel rounds ctxAX raisedStore = .committed) :
    InFragmentStore raisedStore ∧ (run (leastTower.solver fuel) raisedStore rounds).readout = .commit :=
  ⟨raised_in_fragment, committed_of_endingLeast read⟩

/-- The family commits on `X ≐ Π (_ : A). A` at `U1` wherever its compiled run reads `committed`. -/
theorem raisedPi_least_committed_of_ending {fuel rounds : Nat}
    (read : endingLeast fuel rounds ctxAX raisedPiStore = .committed) :
    InFragmentStore raisedPiStore ∧ (run (leastTower.solver fuel) raisedPiStore rounds).readout = .commit :=
  ⟨raisedPi_in_fragment, committed_of_endingLeast read⟩

/-! ## Negative control: a side that is not a term of the smaller universe -/

/-- `X ≐ U0` at `U1`. -/
def sortEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX largeType (.var 0) (by decide +kernel), termIn ctxAX largeType u0 (by decide +kernel))
def sortStore : EquationStore (TotalTerm ctxAX) := [sortEquation]

theorem sort_in_fragment : InFragmentStore sortStore := storeInside_sound (by decide +kernel)

/-- **No candidate universe reads `X ≐ U0` lower**: the right side is not a term of `U0`. -/
theorem sort_not_lowered :
    (lowerFirst (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 sortEquation towerSorts).isNone = true := by decide +kernel

/-- **Positive control**: the candidate `U0` reads `X ≐ A` lower. -/
theorem raised_lowered :
    (lowerFirst (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 raisedEquation towerSorts).isSome = true := by decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
