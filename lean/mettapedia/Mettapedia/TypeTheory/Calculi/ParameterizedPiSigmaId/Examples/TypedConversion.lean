import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticTypedConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticJudgmentalSigmaId
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.JudgmentalSigmaId
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ContextualSections

/-! # Concrete examples of SyntacticTypedConversion -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.JudgmentalEquality
universe uEvidence

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticTypedConversion

open CategoryTheory
open Declaration
open ProofRelevantStructuralComputation
open SyntacticContextual
open SyntacticJudgmentalPi
open SyntacticConversionEnrichment
namespace TowerExamples

open SyntacticContextual.TowerExamples

private abbrev levelOne : LevelExpr Nat := .succ Tower.zero
private abbrev levelTwo : LevelExpr Nat := .succ levelOne
private abbrev retainedTower :=
  SyntacticJudgmentalPi.TowerExamples.retainedTower

/-- The Tower universe U1 displayed as a type in U2. -/
def universeOneDisplay : DisplayedUniverse empty where
  level := .sort levelOne
  upper := .sort levelTwo
  levelIsUniverse := .sort levelOne
  upperIsUniverse := .sort levelTwo
  formation := .sort levelOne

/-- The displayed universe is exactly the existing formed U1 type. -/
theorem universeOneDisplay_type :
    universeOneDisplay.type = universeOne := by
  rfl

/-- The beta source of the native identity function, now regarded as a type
displayed in U1. -/
def betaSource : DisplayedType universeOneDisplay :=
  SyntacticJudgmentalPi.TowerExamples.identityApplication

/-- The corresponding beta target, retained as another displayed type. -/
def betaTarget : DisplayedType universeOneDisplay :=
  SyntacticJudgmentalPi.TowerExamples.identityBetaTarget

/-- Pi beta is a fully typed conversion of types: all conversion
intermediates remain terms of U1. -/
def betaTypedConversion :
    TypedTypeConversion
      SyntacticJudgmentalPi.TowerExamples.retainedTower
      universeOneDisplay betaSource betaTarget := by
  exact
    SyntacticJudgmentalPi.TowerExamples.identityBetaConversion

/-- Forgetting the fully typed beta conversion recovers a formed-endpoint
conversion without claiming that all raw conversions admit such a lift. -/
def betaEndpointConversion :
    TypeConversion SyntacticJudgmentalPi.TowerExamples.retainedTower
      betaSource.toTypeOver betaTarget.toTypeOver :=
  betaTypedConversion.toEndpointConversion

/-- The same beta step admitted from its raw receipt using only local
reversibility at the displayed U1 fibre. -/
def betaPathTyping :
    BidirectionalStepTyping.PathTyping retainedTower empty universeOne
      betaTypedConversion.toStructural :=
  .step
    (SyntacticJudgmentalPi.TowerExamples.identityProduct.betaReceipt
      retainedTower SyntacticJudgmentalPi.TowerExamples.identityBody
      universeZero)
    (fun _sourceTyping => betaTarget.typed)
    (fun _targetTyping => betaSource.typed)

/-- Positive boundary control: a locally certified raw path reconstructs an
intrinsic typed conversion without requiring evaluator-wide subject
expansion. -/
noncomputable def betaLiftedFromRaw :
    TypedTypeConversion retainedTower universeOneDisplay betaSource betaTarget :=
  BidirectionalStepTyping.PathTyping.liftCertified betaPathTyping

/-- The concrete boundary admission retains exactly the authored beta
receipt as one forward primitive event. -/
theorem betaLiftedFromRaw_trace :
    StructuralReceiptTrace.ofTyped betaLiftedFromRaw =
      [OrientedStructuralReceipt.forward
        (StructuralStepReceipt.betaPi
          (computation := retainedTower.computation)
          (headEq := Tower.rules.headEq)
          SyntacticJudgmentalPi.TowerExamples.identityBody.code
          universeZero.code)] := by
  unfold betaLiftedFromRaw
  exact (BidirectionalStepTyping.PathTyping.liftCertified_trace (display := universeOneDisplay)
    (source := betaSource) (target := betaTarget) betaPathTyping).trans rfl

/-- The typed conversion is nontrivial: its displayed endpoint codes are not
equal in the host theory. -/
theorem betaTypedConversion_endpoints_ne :
    betaSource.code ≠ betaTarget.code := by
  simpa only [betaSource, betaTarget, Term.cast_code] using
    SyntacticJudgmentalPi.TowerExamples.identityApplication_code_ne_target

/-- U2 is a distinct judgment fibre from U1. -/
theorem universeOne_ne_universeTwo :
    universeOne ≠ SyntacticJudgmentalPi.TowerExamples.universeTwo :=
  SyntacticJudgmentalPi.TowerExamples.universeOne_ne_universeTwo

/-- Negative control: proof-relevant conversion cannot cross from the U1
term fibre to the U2 term fibre without first carrying equality of the
formed universe indices. -/
theorem noConversionAcrossUniverseFibres :
    IsEmpty
      (TotalConversion
        (termComputation
          SyntacticJudgmentalPi.TowerExamples.retainedTower empty)
        ⟨universeOne, universeZero⟩
        ⟨SyntacticJudgmentalPi.TowerExamples.universeTwo,
          SyntacticJudgmentalPi.TowerExamples.universeOneTerm⟩) := by
  exact noTotalConversionOfIndexNe
    (computation :=
      termComputation
        SyntacticJudgmentalPi.TowerExamples.retainedTower empty)
    universeOne_ne_universeTwo

/-! ## Why raw conversion has no unconditional typed lift -/

/-- A deliberately absent declaration used as an ill-typed beta argument. -/
def missingArgumentName : DeclName := `CumulativeTower.TypedConversion.MissingArgument

/-- The absent constant as a closed raw term. -/
def missingArgument : Tm Tower.Head empty.arity := .const missingArgumentName

/-- A beta redex whose body ignores its argument.  Raw computation can erase
the absent constant even though the application has no typing derivation. -/
def illTypedBetaSource : Tm Tower.Head empty.arity :=
  .app (.lam (rename wk universeZero.code)) missingArgument

/-- The structural beta receipt exists independently of typing. -/
def illTypedBetaStep :
    StructuralStepReceipt retainedTower.computation Tower.rules.headEq
      illTypedBetaSource universeZero.code := by
  simpa only [illTypedBetaSource, missingArgument, inst0_rename_wk] using
    (StructuralStepReceipt.betaPi
      (computation := retainedTower.computation)
      (headEq := Tower.rules.headEq)
      (rename wk universeZero.code) missingArgument)

/-- The redex is not typable at U1: application generation would require a
typing derivation for the deliberately undeclared argument. -/
theorem illTypedBetaSource_not_typed :
    ¬ HasType Tower.rules empty.context illTypedBetaSource universeOne.code := by
  intro sourceTyping
  rcases sourceTyping.appGeneration with
    ⟨_domain, _codomain, _functionTyping, argumentTyping, _adjustment⟩
  exact argumentTyping.constantImpossibleWhenMissing rfl

/-- Negative control: raw structural computation cannot globally provide
subject expansion in a formed type fibre.  Consequently the conditional
lifting interface above must be instantiated only by a genuinely reversible
typed rule fragment; it is not an evaluator-wide law. -/
theorem noGlobalBidirectionalStepTyping :
    IsEmpty
      (BidirectionalStepTyping retainedTower empty universeOne) := by
  constructor
  intro typing
  exact illTypedBetaSource_not_typed
    (typing.backward illTypedBetaStep universeZero.typed)

end TowerExamples

#print axioms TowerExamples.betaTypedConversion
#print axioms TowerExamples.betaPathTyping
#print axioms TowerExamples.betaLiftedFromRaw
#print axioms TowerExamples.betaLiftedFromRaw_trace
#print axioms TowerExamples.betaTypedConversion_endpoints_ne
#print axioms TowerExamples.noConversionAcrossUniverseFibres
#print axioms TowerExamples.illTypedBetaStep
#print axioms TowerExamples.illTypedBetaSource_not_typed
#print axioms TowerExamples.noGlobalBidirectionalStepTyping

end SyntacticTypedConversion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
