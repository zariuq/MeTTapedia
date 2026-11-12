import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowUpdateRank
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativeRun

/-!
# Controls of the narrowing update

**Positive control** (`narrowWitnessAt`): `narrowStore`, `X ≐ Π (y : Y). Y` at `U1` with `X : U0, Y : U1`, meets the
conditions of `ContextualDependentEtaDepth.narrowAt`: its left side is a type of `U0` and its right side holds `Y` at
a domain.

**Negative control** (`wide_not_forced`): `wideStore`, `Y ≐ U0` at `U1` with `Y : U1`. It is solved by `Y := U0`,
and `U0` is not equal to a type of `U0`: the hypothesis of the update fails, and the store over the narrowed context
would lose the solution. So the narrowing is an update only where it is forced.
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

/-- The left side of `narrowEquation`, the unknown `X`, is a type of `U0`. -/
theorem narrow_left_small :
    Typed setting.R ctxAXY.raw narrowEquation.1.2.code (.head (.sort Tower.zero)) := by
  have typed := (termIn ctxAXY smallTypeY (.var 1) (by decide +kernel)).2.typed
  have code : smallTypeY.code = .head (.sort Tower.zero) := formIn_code _ _ _
  rw [code] at typed
  exact typed

/-- **`narrowStore` meets the conditions of the narrowing update at an equation.** -/
def narrowWitnessAt : Update setting.levels narrowStore :=
  narrowAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ctxAX largeType smallType
    (formIn_code _ _ _) (formIn_code _ _ _) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (a := .sort (.succ Tower.zero)) (by decide +kernel) narrowStore (equation := narrowEquation)
    List.mem_cons_self (formIn_code _ _ _) narrow_left_small (.piDomain .here)

/-- `Y ≐ U0` at `U1`, over `A X : U0, Y : U1`. -/
def wideEquation : Equation (TotalTerm ctxAXY) :=
  (termIn ctxAXY largeTypeY (.var 0) (by decide +kernel),
    termIn ctxAXY largeTypeY (.head (.sort Tower.zero)) (by decide +kernel))

def wideStore : EquationStore (TotalTerm ctxAXY) := [wideEquation]

/-- `Y := U0`. -/
def wideAnswer : ctxAX ⟶ ctxAXY :=
  Elimination.instantiate ctxAX (termIn ctxAX largeType (.head (.sort Tower.zero)) (by decide +kernel)).2

/-- `Y := U0` solves `wideStore`. -/
theorem wide_models : (frames setting.levels).Models wideAnswer wideStore :=
  models_by wideAnswer wideEquation.1.2 wideEquation.2.2 (by decide +kernel)

/-- **The narrowing is not forced on `wideStore`**: a solution sends `Y` to `U0`, which is not equal to a type of
`U0`. -/
theorem wide_not_forced :
    ¬ ∀ (Δ : Context setting.R) (σ : Δ ⟶ ctxAXY), (frames setting.levels).Models σ wideStore →
      ∃ value, Typed setting.R Δ.raw value (.head (.sort Tower.zero)) ∧
        TypeEq setting.R Δ.raw value (σ.substitution 0) := by
  intro forced
  obtain ⟨value, typed, equal⟩ := forced ctxAX wideAnswer wide_models
  have code : wideAnswer.substitution 0 = .head (.sort Tower.zero) := by decide +kernel
  rw [code] at equal
  refine sort_not_small (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ctxAX.formed (by decide +kernel) ?_ typed equal
  intro above typing c
  cases typing
  exact absurd c (by decide +kernel)

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
