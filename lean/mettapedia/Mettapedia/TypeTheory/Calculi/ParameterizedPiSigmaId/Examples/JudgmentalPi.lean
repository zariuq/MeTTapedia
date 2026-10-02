import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticJudgmentalPi
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticNaturalModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NaturalModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ProofRelevantStructuralComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ContextualSections

/-! # Concrete examples of SyntacticJudgmentalPi -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.JudgmentalEquality
universe uEvidence

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticJudgmentalPi

open CategoryTheory
open SyntacticContextual
open SyntacticNaturalModel
open Declaration
open ProofRelevantStructuralComputation
namespace TowerExamples

open SyntacticContextual.TowerExamples

private abbrev levelOne : LevelExpr Nat := .succ Tower.zero
private abbrev levelTwo : LevelExpr Nat := .succ levelOne
private abbrev levelThree : LevelExpr Nat := .succ levelTwo

/-- The dependent constant family `U1` over one `U1` variable. -/
def identityCodomain : TypeOver (extendContext empty universeOne) :=
  universeOne.reindex (projectionHom empty universeOne)

/-- Native formation of `(x : U1) -> U1`, retaining its exact maximum
universe expression. -/
def identityProduct : DependentProduct universeOne identityCodomain where
  level := .sort (.max levelTwo levelTwo)
  isUniverse := .sort (.max levelTwo levelTwo)
  join := .sorts levelTwo levelTwo

/-- The native variable body of the polymorphic identity function. -/
def identityBody : Term (extendContext empty universeOne) identityCodomain :=
  newestVariable empty universeOne

/-- Direct native construction of the identity lambda. -/
def identityFunction : Term empty identityProduct.type :=
  identityProduct.lambda identityBody

/-- Direct native application of identity to the universe `U0`. -/
def identityApplication :
    Term empty (instantiateType identityCodomain universeZero) :=
  identityProduct.application identityFunction universeZero

/-- The canonically instantiated beta target. -/
def identityBetaTarget :
    Term empty (instantiateType identityCodomain universeZero) :=
  instantiateTerm identityBody universeZero

/-- The Tower presentation's root relation lifted without inventing any
declaration-specific witness. -/
def retainedTower : RetainedRoot Tower.rules :=
  RetainedRoot.ofRules Tower.rules

/-- Positive control: native identity application carries a proof-relevant
beta conversion to its target. -/
def identityBetaConversion :
    ConversionEvidence (termComputation retainedTower empty)
      identityApplication identityBetaTarget :=
  identityProduct.betaConversion retainedTower identityBody universeZero

@[simp] theorem identityBetaTarget_code :
    identityBetaTarget.code = universeZero.code := by
  rfl

/-- Negative control: beta conversion is genuinely judgmental.  Its source
and target are not equal raw syntax, so an equality-based model would have to
quotient away precisely the computation receipt retained above. -/
theorem identityApplication_code_ne_target :
    identityApplication.code ≠ identityBetaTarget.code := by
  rw [identityBetaTarget_code]
  change
    Tm.app (Tm.lam (newestVariable empty universeOne).code)
        (sortTm Tower.zero) ≠
      sortTm Tower.zero
  intro equality
  cases equality

/-- `U2` as a formed type over the same empty Tower context. -/
def universeTwo : TypeOver empty where
  code := sortTm levelTwo
  level := .sort levelThree
  isUniverse := .sort levelThree
  formed := .headType (.sort levelTwo)

/-- `U1` is a term of `U2`. -/
def universeOneTerm : Term empty universeTwo where
  code := sortTm levelOne
  typed := .headType (.sort levelOne)

theorem universeOne_ne_universeTwo : universeOne ≠ universeTwo := by
  intro equality
  have codeEquality := congrArg TypeOver.code equality
  have headEquality := Tm.head.inj codeEquality
  have levelEquality := LevelTower.Head.sort.inj headEquality
  cases levelEquality

/-- Negative control: judgmental conversion cannot cross distinct type
fibres even when both states inhabit the same formed context. -/
theorem no_conversion_across_universe_fibres :
    IsEmpty
      (TotalConversion (termComputation retainedTower empty)
        ⟨universeOne, universeZero⟩ ⟨universeTwo, universeOneTerm⟩) := by
  constructor
  intro conversion
  exact universeOne_ne_universeTwo conversion.indexEquality

end TowerExamples

#print axioms TowerExamples.identityBetaConversion
#print axioms TowerExamples.identityApplication_code_ne_target
#print axioms TowerExamples.no_conversion_across_universe_fibres

end SyntacticJudgmentalPi
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
