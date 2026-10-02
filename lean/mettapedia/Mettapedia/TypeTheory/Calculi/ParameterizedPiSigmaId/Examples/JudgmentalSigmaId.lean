import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticJudgmentalSigmaId
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticConversionEnrichment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ContextualSections
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.JudgmentalPi

/-! # Concrete examples of SyntacticJudgmentalSigmaId -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.JudgmentalEquality
universe uEvidence

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticJudgmentalSigmaId

open CategoryTheory
open SyntacticContextual
open SyntacticJudgmentalPi
open SyntacticConversionEnrichment
open ProofRelevantStructuralComputation
namespace TowerExamples

open SyntacticContextual.TowerExamples

private abbrev levelOne : LevelExpr Nat := .succ Tower.zero
private abbrev levelTwo : LevelExpr Nat := .succ levelOne

/-- The genuinely dependent family `x : U1 ⊢ x type`. -/
def dependentCodomain :
    TypeOver (extendContext empty universeOne) where
  code := (newestVariable empty universeOne).code
  level := .sort levelOne
  isUniverse := .sort levelOne
  formed := (newestVariable empty universeOne).typed

/-- Native formation of `Σ (x : U1), x`. -/
def dependentSum : DependentSum universeOne dependentCodomain where
  level := .sort (.max levelTwo levelOne)
  isUniverse := .sort (.max levelTwo levelOne)
  join := .sorts levelTwo levelOne

/-- The opaque ground head is intrinsically a term of the instantiated
family at `U0`. -/
def groundAtUniverseZero :
    Term empty (instantiateType dependentCodomain universeZero) where
  code := .head .legacyGround
  typed := .headType .legacyGround

/-- A nontrivial dependent pair `(U0, legacyGround)`. -/
def dependentPair : Term empty dependentSum.type :=
  dependentSum.pair universeZero groundAtUniverseZero

/-- Retained Tower computation used by the Sigma controls. -/
def retainedTower : RetainedRoot Tower.rules :=
  RetainedRoot.ofRules Tower.rules

/-- Positive control: second beta retains both the type conversion and the
term conversion. -/
def dependentSecondBetaTransport :
    TermTransport retainedTower
      (instantiateType dependentCodomain
        (dependentSum.firstProjection dependentPair))
      (instantiateType dependentCodomain universeZero) :=
  dependentSum.secondBetaTransport retainedTower universeZero
    groundAtUniverseZero

def dependentSecondBetaConversion :
    ConversionEvidence (termComputation retainedTower empty)
      dependentSecondBetaTransport.targetTerm groundAtUniverseZero :=
  dependentSum.secondBetaConversion retainedTower universeZero
    groundAtUniverseZero

/-- The two Sigma-beta type fibres are not equal raw formed types.  Their
connection is exactly the retained conversion above. -/
theorem dependentSecondBetaTypes_ne :
    instantiateType dependentCodomain
        (dependentSum.firstProjection dependentPair) ≠
      instantiateType dependentCodomain universeZero := by
  intro equality
  have codeEquality := congrArg TypeOver.code equality
  change
    Tm.fst (Tm.pair (sortTm Tower.zero) (Tm.head .legacyGround)) =
      sortTm Tower.zero at codeEquality
  cases codeEquality

/-- Equality-based transport is uninhabited at this dependent beta, whereas
the retained conversion transport above is inhabited. -/
@[reducible] def noEqualityTransportForDependentSecondBeta :
    IsEmpty
      (instantiateType dependentCodomain
          (dependentSum.firstProjection dependentPair) =
        instantiateType dependentCodomain universeZero) :=
  ⟨dependentSecondBetaTypes_ne⟩

/-- Strictness of the conversion enrichment: this is not merely a different
presentation of an equality-based CwF law.  The conversion-enriched transport
exists exactly where equality transport cannot be formed. -/
theorem conversionEnrichment_strict_at_dependentSecondBeta :
    Nonempty
        (TermTransport retainedTower
          (instantiateType dependentCodomain
            (dependentSum.firstProjection dependentPair))
          (instantiateType dependentCodomain universeZero)) ∧
      IsEmpty
        (instantiateType dependentCodomain
            (dependentSum.firstProjection dependentPair) =
          instantiateType dependentCodomain universeZero) :=
  ⟨⟨dependentSecondBetaTransport⟩,
    noEqualityTransportForDependentSecondBeta⟩

/-- Term beta is likewise judgmental rather than raw syntactic equality. -/
theorem dependentSecondProjection_code_ne_target :
    dependentSecondBetaTransport.targetTerm.code ≠
      groundAtUniverseZero.code := by
  change
    Tm.snd (Tm.pair (sortTm Tower.zero) (Tm.head .legacyGround)) ≠
      Tm.head .legacyGround
  intro equality
  cases equality

/-- A diagonal identity type and a mixed-endpoint identity type remain
distinct even though both are well formed over `U1`. -/
def diagonalUniverseIdentity : TypeOver empty :=
  identityType universeOne universeZero universeZero

def mixedUniverseIdentity : TypeOver empty :=
  identityType universeOne universeZero legacyGround

/-- Positive control for native identity introduction. -/
def universeZeroReflexivity : Term empty diagonalUniverseIdentity :=
  identityReflexivity universeZero

/-- Negative control: reflexivity cannot masquerade as evidence for a
different right endpoint. -/
theorem diagonalIdentity_ne_mixedIdentity :
    diagonalUniverseIdentity ≠ mixedUniverseIdentity := by
  intro equality
  have codeEquality := congrArg TypeOver.code equality
  have rightEquality := Tm.id.inj codeEquality |>.2.2
  have headEquality :
      LevelTower.Head.sort Tower.zero = LevelTower.Head.legacyGround :=
    Tm.head.inj rightEquality
  cases headEquality

end TowerExamples

#print axioms TowerExamples.dependentSecondBetaConversion
#print axioms TowerExamples.dependentSecondBetaTypes_ne
#print axioms TowerExamples.conversionEnrichment_strict_at_dependentSecondBeta
#print axioms TowerExamples.dependentSecondProjection_code_ne_target
#print axioms TowerExamples.diagonalIdentity_ne_mixedIdentity

end SyntacticJudgmentalSigmaId
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
