import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentProjectionInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigmaDiscoveryControls

/-!
# Actual recovery through dependent pair projections

The first projection recovers a selected variable. A whole pair recovers a
pair of variables and reconstructs the original using typed Sigma eta.
Dropping the second component leaves its recovery unresolved. A later
definition can resolve that obligation; failed inversion is not refutation.
An unsuitable restoration map is rejected by the final conversion check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentProjectionInversion.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion ContextualDependentFlex

abbrev setting := ContextualDependentSigma.Controls.setting
abbrev shape := ContextualDependentSigma.Controls.shape

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def firstOnly : Inclusion Wakeup.frame shape.split := withoutNewest Wakeup.frame shape.codomain
def both : Inclusion shape.split shape.split where
  forward := id
  injective := fun _ _ same => same
  typed := (𝟙 shape.split : shape.split ⟶ shape.split).typed

def run (fuel : Nat) {source : Context Tower.rules} (selection : Inclusion source shape.split)
    (type : TypeOver source) (original : TotalTerm shape.packed) :=
  recoverSigma (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer fuel shape selection type original

def firstResult := run 24 firstOnly Wakeup.viewedUniverse ContextualDependentSigma.Controls.packedFirst

theorem first_projection_recovers_variable :
    firstResult.map (fun result => result.body.code) = some (.var 0) := by decide +kernel

def wholeType : TypeOver shape.split := shape.whole.reindex shape.splitBase
def packedValue : TotalTerm shape.packed :=
  ⟨shape.whole.reindex (projectionHom _ shape.whole), newest _ shape.whole⟩
def wholeResult := run 24 both wholeType packedValue

theorem whole_pair_recovers_components :
    wholeResult.map (fun result => result.body.code) = some (.pair (.var 1) (.var 0)) := by decide +kernel

def wholeRecovery := wholeResult.get (by decide +kernel)

theorem whole_reconstruction_uses_eta :
    (frames setting.levels).E
      (TotalTerm.reindex ⟨wholeType, wholeRecovery.body⟩ (shape.unpack ≫ both.hom)) packedValue :=
  wholeRecovery.solves

theorem whole_reconstruction_is_not_raw :
    (TotalTerm.reindex ⟨wholeType, wholeRecovery.body⟩ (shape.unpack ≫ both.hom)).2.code ≠
      packedValue.2.code := by decide +kernel

def packedSecond : TotalTerm shape.packed :=
  ⟨shape.codomain.reindex (pair (projectionHom _ shape.whole)
    (shape.first (projectionHom _ shape.whole) (newest _ shape.whole))),
    shape.second (projectionHom _ shape.whole) (newest _ shape.whole)⟩

theorem missing_second_component_is_unresolved : run 24 firstOnly shape.codomain packedSecond = none := by rfl'

theorem zero_budget_is_unresolved : run 0 both wholeType packedValue = none := by rfl'

def sourceFunctionType : TypeOver Wakeup.frame :=
  Examples.TypedContextualControls.functionType.reindex (toEmpty _)
def targetFunctionType : TypeOver shape.packed :=
  Examples.TypedContextualControls.functionType.reindex (toEmpty _)

def lambdaProjection : TotalTerm shape.packed :=
  ⟨targetFunctionType,
    ⟨.lam (.fst (.var 1)), .lamIntro targetFunctionType.formed targetFunctionType.universeWitness
      (.fstElim (.var 1))⟩⟩

def lambdaLocal : TotalTerm shape.packed :=
  ⟨targetFunctionType,
    ⟨.lam (.var 0), .lamIntro targetFunctionType.formed targetFunctionType.universeWitness (.var 0)⟩⟩

theorem projection_beneath_lambda_recovers_outer_variable :
    (run 24 firstOnly sourceFunctionType lambdaProjection).map (fun result => result.body.code) =
      some (.lam (.var 1)) := by decide +kernel

theorem lambda_local_is_not_captured :
    (run 24 firstOnly sourceFunctionType lambdaLocal).map (fun result => result.body.code) =
      some (.lam (.var 0)) := by decide +kernel

def fixedValue : Term (empty Tower.rules) shape.whole :=
  ⟨.pair (.head .legacyGround) (.refl (.head .legacyGround)),
    .pairIntro shape.whole.formed shape.whole.universeWitness (.headType .legacyGround)
      (.reflIntro (.headType .legacyGround))⟩
def fixedPair : empty Tower.rules ⟶ shape.packed := Elimination.instantiate _ fixedValue
def wrongRestore : shape.packed ⟶ shape.split := toEmpty _ ≫ fixedPair ≫ shape.unpack

def wrongAttempt := recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
  ConversionControls.reducer 24 firstOnly shape.pack wrongRestore Wakeup.viewedUniverse
  ContextualDependentSigma.Controls.packedFirst

theorem final_check_rejects_wrong_restoration : wrongAttempt = none := by rfl'

def reflected : Term Wakeup.frame shape.codomain := ⟨.refl (.var 0), .reflIntro (.var 0)⟩
def proposedProof : TotalTerm shape.packed :=
  TotalTerm.reindex ⟨shape.codomain, reflected⟩ (shape.unpack ≫ firstOnly.hom)

def laterComparison := Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra ConversionControls.reducer 24
    (proposedProof.reindex fixedPair) (packedSecond.reindex fixedPair)

theorem missing_projection_can_resolve_later : laterComparison.isSome = true := by decide +kernel

theorem unresolved_obligation_has_a_closed_solution :
    (frames setting.levels).Models fixedPair [(proposedProof, packedSecond)] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact (laterComparison.get (by decide +kernel)).down

end ContextualDependentProjectionInversion.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
