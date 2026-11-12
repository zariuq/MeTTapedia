import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowPosition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowUpdateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepExact

/-!
# Controls of the narrowing at a position that is not the newest

`middleStore` is `X ≐ Π (y : Y). Y` at `U1`, over `A : U0, Y : U1, X : U0`: the declaration to lower, `Y`, is
followed by another declaration.

**Positive control** (`middleWitnessAt`): the store meets the conditions of
`ContextualDependentEtaDepth.narrowingAt` at the position of `Y`. The family `pairTower` commits on the narrowed
store (`middle_remaining_committed`, evaluated by the kernel), so the store has a principal answer
(`middle_principal`). The store is in the fragment and has exact arguments, and `pairTower` is stuck on it wherever
its compiled run reads `stuck` (`middle_gap_of_ending`): the narrowing is not yet a rule of a family.

`mirrorWitnessAt`: the store with its sides exchanged meets the conditions of the narrowing from the left side.

**Negative control** (`middle_not_held`): the right side does not hold `X` at a type position, so the conditions
are not met at the newest position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective
open ContextualDependentCumulative

/-- `U1`, over `A`. -/
def largeTypeA : TypeOver ctxA := formIn ctxA (.head (.sort (.succ Tower.zero))) (by decide +kernel)

/-- `A : U0, Y : U1`. -/
abbrev ctxAY := extend ctxA largeTypeA

/-- `U0`, over `A Y`. -/
def smallTypeAY : TypeOver ctxAY := formIn ctxAY (.head (.sort Tower.zero)) (by decide +kernel)

/-- `A : U0, Y : U1, X : U0`: the declaration to lower is not the newest. -/
abbrev ctxAYX := extend ctxAY smallTypeAY

/-- `U1`, over `A Y X`. -/
def largeTypeAYX : TypeOver ctxAYX := formIn ctxAYX (.head (.sort (.succ Tower.zero))) (by decide +kernel)

/-- `U0`, over `A Y X`. -/
def smallTypeAYX : TypeOver ctxAYX := formIn ctxAYX (.head (.sort Tower.zero)) (by decide +kernel)

/-- `X ≐ Π (y : Y). Y` at `U1`. -/
def middleEquation : Equation (TotalTerm ctxAYX) :=
  (termIn ctxAYX largeTypeAYX (.var 0) (by decide +kernel),
    termIn ctxAYX largeTypeAYX (.pi (.var 1) (.var 2)) (by decide +kernel))

def middleStore : EquationStore (TotalTerm ctxAYX) := [middleEquation]

theorem middle_in_fragment : InFragmentStore middleStore := storeInside_sound (by decide +kernel)

theorem middle_exact : storeExact middleStore = true := by decide +kernel

/-- `A : U0, Y : U0, X : U0`. -/
abbrev ctxAyX := extend ctxAX smallType

/-- `A, Y : U1, X : U0` narrows to `A, Y : U0, X : U0`. -/
theorem middle_narrows : CtxNarrows setting.R ctxAYX.raw ctxAyX.raw := by
  change CtxNarrows setting.R (.snoc (.snoc ctxA.raw largeTypeA.code) smallTypeAY.code)
    (.snoc (.snoc ctxA.raw universeA.code) smallType.code)
  have large : largeTypeA.code = .head (.sort (.succ Tower.zero)) := formIn_code _ _ _
  have smallA : universeA.code = .head (.sort Tower.zero) := formIn_code _ _ _
  have smallY : smallTypeAY.code = .head (.sort Tower.zero) := formIn_code _ _ _
  have smallX : smallType.code = .head (.sort Tower.zero) := formIn_code _ _ _
  rw [smallY, smallX, large, smallA]
  exact .same _ (.lower (CtxNarrows.refl ctxA.raw) (by decide +kernel))

/-- **The narrowing of `A, Y : U1, X : U0` that lowers `Y`**, a declaration that is not the newest. -/
def middleNarrowing : Narrowing (S := setting) ctxAYX where
  raw := ctxAyX.raw
  formed := ctxAyX.formed
  narrows := middle_narrows

/-- It lowers the declaration of `Y`, from `U1` to `U0`, and no other. -/
theorem middle_lowered :
    LowersAt (S := setting) middleNarrowing (1 : Fin ctxAYX.arity) (.sort Tower.zero) (.sort (.succ Tower.zero)) where
  wide := by decide +kernel
  small := by decide +kernel
  elsewhere := by decide +kernel
  lower := by decide +kernel
  large := by decide +kernel

/-- The left side of `middleEquation`, the unknown `X`, is a type of `U0`. -/
theorem middle_left_small :
    Typed setting.R ctxAYX.raw middleEquation.1.2.code (.head (.sort Tower.zero)) := by
  have typed := (termIn ctxAYX smallTypeAYX (.var 0) (by decide +kernel)).2.typed
  have code : smallTypeAYX.code = .head (.sort Tower.zero) := formIn_code _ _ _
  rw [code] at typed
  exact typed

/-- **`middleStore` meets the conditions of the narrowing at a position that is not the newest.** -/
def middleWitnessAt : Update setting.levels middleStore :=
  narrowingAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete middleNarrowing middle_lowered
    (by decide +kernel) (a := .sort (.succ Tower.zero)) (by decide +kernel) middleStore
    (equation := middleEquation) List.mem_cons_self (formIn_code _ _ _) middle_left_small (.piDomain .here)

/-- `Π (y : Y). Y ≐ X` at `U1`: `middleEquation` with its sides exchanged. -/
def mirrorEquation : Equation (TotalTerm ctxAYX) := (middleEquation.2, middleEquation.1)

def mirrorStore : EquationStore (TotalTerm ctxAYX) := [mirrorEquation]

/-- **The store with the unknown held on the left meets the conditions of the narrowing from the left side.** -/
def mirrorWitnessAt : Update setting.levels mirrorStore :=
  narrowingAtLeft (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete middleNarrowing middle_lowered
    (by decide +kernel) (a := .sort (.succ Tower.zero)) (by decide +kernel) mirrorStore
    (equation := mirrorEquation) List.mem_cons_self (formIn_code _ _ _) middle_left_small (.piDomain .here)

/-- The right side does not hold `X` at a type position: the conditions are not met at the newest position. -/
theorem middle_not_held :
    ¬ HoldsVar (Head := Tower.Head) (0 : Fin ctxAYX.arity) middleEquation.2.2.code := by
  intro holds
  cases holds with
  | piDomain inner => cases inner

/-- **The family `pairTower` commits on the narrowed store**, at budget 16. -/
theorem middle_remaining_committed :
    (run (pairTower.solver 16) middleWitnessAt.remaining 2).readout = .commit := by decide +kernel

/-- **`middleStore` has a principal answer.** -/
theorem middle_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAYX), (frames setting.levels).Principal middleStore answer := by
  cases outcome : run (pairTower.solver 16) middleWitnessAt.remaining 2 with
  | solved state finished => exact ⟨_, _, (middleWitnessAt.then state).completed finished⟩
  | stuck _ =>
      have committed := middle_remaining_committed
      rw [outcome] at committed
      cases committed
  | refuted _ =>
      have committed := middle_remaining_committed
      rw [outcome] at committed
      cases committed
  | cutoff _ =>
      have committed := middle_remaining_committed
      rw [outcome] at committed
      cases committed

/-- **A store of the fragment with exact arguments and a principal answer on which `pairTower` is stuck** wherever
its compiled run reads `stuck`; the narrowing it needs is at a declaration that is not the newest. -/
theorem middle_gap_of_ending {fuel rounds : Nat} (read : endingPair fuel rounds ctxAYX middleStore = .stuck) :
    InFragmentStore middleStore ∧ storeExact middleStore = true ∧
      (∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAYX), (frames setting.levels).Principal middleStore answer) ∧
      isStuck (run (pairTower.solver fuel) middleStore rounds) = true :=
  ⟨middle_in_fragment, middle_exact, middle_principal, stuck_of_endingPair read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
