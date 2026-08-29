import Mettapedia.Languages.Metamath.InferenceAssertionLeadingProvesReflection
import Mettapedia.Languages.Metamath.InferenceProjectionSideConservativity
import Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

open Mettapedia.GSLT.LanguageDef

/-!
# Reflection of projected assertion side evidence

Once the raw mandatory-hypothesis bodies have been decoded, the remaining
children of a projected assertion application have a rigid shape: canonical
essential checks, the disjoint-variable check, and one final `ApplySubst`
check whose result argument is still raw.

This module restricts that original final child to the standalone side
calculus and uses its derivation to decode the result formula.  It then
reindexes the complete original side-child vector and packages those same
proof artifacts as `AssertionSideEvidence`.  No derivation is regenerated
from proof-irrelevant semantic existence.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

/-! ## Proof-preserving dependent reindexing -/

/-- Reindex one derivation along an equality of its goal.  This changes only
the dependent type index. -/
def castDerivation {target : ValidatedCalculusLanguageDef}
    {sourceGoal targetGoal : Pattern}
    (goal_eq : sourceGoal = targetGoal)
    (derivation : Derivation target sourceGoal) :
    Derivation target targetGoal := by
  subst targetGoal
  exact derivation

/-- Reindexing one derivation preserves its complete raw proof artifact. -/
@[simp] theorem erase_castDerivation
    {target : ValidatedCalculusLanguageDef} {sourceGoal targetGoal : Pattern}
    (goal_eq : sourceGoal = targetGoal)
    (derivation : Derivation target sourceGoal) :
    (castDerivation goal_eq derivation).erase = derivation.erase := by
  subst targetGoal
  rfl

/-- Reindex an ordered derivation vector along an equality of its exact
premise list.  This changes only the dependent type index. -/
def castDerivationList {target : ValidatedCalculusLanguageDef}
    {sourcePremises targetPremises : List Pattern}
    (premises_eq : sourcePremises = targetPremises)
    (derivations : DerivationList target sourcePremises) :
    DerivationList target targetPremises := by
  subst targetPremises
  exact derivations

/-- Reindexing a derivation vector preserves every raw proof artifact in
order. -/
@[simp] theorem erase_castDerivationList
    {target : ValidatedCalculusLanguageDef}
    {sourcePremises targetPremises : List Pattern}
    (premises_eq : sourcePremises = targetPremises)
    (derivations : DerivationList target sourcePremises) :
    (castDerivationList premises_eq derivations).erase = derivations.erase := by
  subst targetPremises
  rfl

/-! ## Public side-judgment interface -/

/-- Every `ApplySubst` judgment is in the standalone side-judgment fragment,
independently of its three arguments. -/
theorem applySubst_isSideJudgment
    (substitution source result : Pattern) :
    IsSideJudgment (applySubst substitution source result) := by
  simp [IsSideJudgment, applySubst, reservedJudgmentHeads]

/-! ## Reflection of the original raw side vector -/

/-- Decode the raw result body from the original final `ApplySubst` child and
package the complete original side-child vector as canonical assertion side
evidence.

The returned erasure equality certifies that the evidence package contains
the original raw proof artifacts.  The standalone restriction is used only
to invoke the verified side-calculus decoder; its exact erasure-preservation
theorem ensures that it does not alter the inspected proof. -/
theorem RawHypothesisBodiesDecode.reflectSideEvidence
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution} {resultBody : Pattern}
    (decoding : RawHypothesisBodiesDecode assertion.hypotheses bodies actuals
      substitution)
    (children : DerivationList target
      (rawAssertionSidePremises projection.callerFrame assertion bodies
        resultBody)) :
    ∃ result : ConstantHeadedFormula,
      resultBody = formulaBodyPattern result ∧
      result.typecode = assertion.formula.typecode ∧
      FormulaSubstitutionSemantics substitution assertion.formula result ∧
      ∃ evidence : AssertionSideEvidence target substitution
        projection.callerFrame assertion actuals result,
        children.erase = evidence.toDerivationList.erase := by
  let rawResultPattern :=
    rawFormulaPattern assertion.formula.typecode resultBody
  let essentialPremises :=
    assertionEssentialPremises substitution assertion.hypotheses actuals
  let dvPremise :=
    dvOK (encodeSubstitution substitution)
      (encodeFrame projection.callerFrame) (encodeFrame assertion.frame)
  let resultPremise :=
    applySubst (encodeSubstitution substitution)
      (encodeFormula assertion.formula) rawResultPattern
  have hrawSidePremises :
      rawAssertionSidePremises projection.callerFrame assertion bodies
          resultBody =
        essentialPremises ++ [dvPremise, resultPremise] := by
    simp only [rawAssertionSidePremises]
    rw [decoding.rawAssertionSubstitution_eq]
    rw [decoding.rawAssertionEssentialPremises_eq_with substitution]
  let indexedChildren : DerivationList target
      (essentialPremises ++ [dvPremise, resultPremise]) :=
    castDerivationList hrawSidePremises children
  let splitChildren := splitDerivationLists essentialPremises
    [dvPremise, resultPremise] indexedChildren
  rcases hsplit : splitChildren with ⟨essentialChildren, suffix⟩
  cases suffix with
  | cons dvChild remaining =>
      cases remaining with
      | cons resultChild remaining =>
          cases remaining with
          | nil =>
              have hsplitActual :
                  splitDerivationLists essentialPremises
                      [dvPremise, resultPremise] indexedChildren =
                    ⟨essentialChildren,
                      .cons dvChild (.cons resultChild .nil)⟩ := by
                simpa [splitChildren] using hsplit
              have happend := appendDerivationLists_split essentialPremises
                [dvPremise, resultPremise] indexedChildren
              rw [hsplitActual] at happend
              have hindexedErase :
                  indexedChildren.erase =
                    essentialChildren.erase ++
                      [dvChild.erase, resultChild.erase] := by
                calc
                  indexedChildren.erase =
                      (appendDerivationLists essentialChildren
                        (.cons dvChild
                          (.cons resultChild .nil))).erase :=
                    congrArg DerivationList.erase happend.symm
                  _ = essentialChildren.erase ++
                      (.cons dvChild
                        (.cons resultChild .nil) :
                          DerivationList target
                            [dvPremise, resultPremise]).erase :=
                    erase_appendDerivationLists _ _
                  _ = essentialChildren.erase ++
                      [dvChild.erase, resultChild.erase] := rfl
              have hresultSide : IsSideJudgment resultPremise := by
                exact applySubst_isSideJudgment _ _ _
              let standaloneResultChild :
                  Derivation validatedSideDefinition resultPremise :=
                restrictSideDerivationFromProjection projection target
                  hprojection hresultSide resultChild
              rcases applySubst_derivation_decodes substitution
                  assertion.formula rawResultPattern standaloneResultChild with
                ⟨result, hresultPattern, hsemantics⟩
              have hcomponents :=
                (rawFormulaPattern_eq_encodeFormula_iff
                  assertion.formula.typecode resultBody result).mp
                  hresultPattern
              rcases hcomponents with ⟨hresultBody, hresultTypecode⟩
              have hresultPattern' :
                  rawFormulaPattern assertion.formula.typecode resultBody =
                    encodeFormula result := by
                simpa [rawResultPattern] using hresultPattern
              have hresultGoal :
                  resultPremise =
                    applySubst (encodeSubstitution substitution)
                      (encodeFormula assertion.formula)
                      (encodeFormula result) := by
                dsimp [resultPremise, rawResultPattern]
                rw [hresultPattern']
              let canonicalResultChild : Derivation target
                  (applySubst (encodeSubstitution substitution)
                    (encodeFormula assertion.formula)
                    (encodeFormula result)) :=
                castDerivation hresultGoal resultChild
              let evidence : AssertionSideEvidence target substitution
                  projection.callerFrame assertion actuals result :=
                ⟨⟨essentialChildren⟩, dvChild, canonicalResultChild⟩
              have hevidenceErase :
                  evidence.toDerivationList.erase =
                    essentialChildren.erase ++
                      [dvChild.erase, resultChild.erase] := by
                change
                  (appendDerivationLists essentialChildren
                    (.cons dvChild
                      (.cons canonicalResultChild .nil))).erase = _
                rw [erase_appendDerivationLists]
                change essentialChildren.erase ++
                    [dvChild.erase,
                      (castDerivation hresultGoal resultChild).erase] = _
                rw [erase_castDerivation]
              refine ⟨result, hresultBody, hresultTypecode, hsemantics,
                evidence, ?_⟩
              calc
                children.erase = indexedChildren.erase :=
                  (erase_castDerivationList hrawSidePremises children).symm
                _ = essentialChildren.erase ++
                    [dvChild.erase, resultChild.erase] := hindexedErase
                _ = evidence.toDerivationList.erase := hevidenceErase.symm

/-! ## Constructive boundaries -/

/-- Positive: any existing canonical side-evidence vector can be reindexed
to its raw-body presentation and reflected without replacing its proof
artifacts. -/
example {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution} {result : ConstantHeadedFormula}
    (decoding : RawHypothesisBodiesDecode assertion.hypotheses bodies actuals
      substitution)
    (hresultTypecode : result.typecode = assertion.formula.typecode)
    (evidence : AssertionSideEvidence target substitution
      projection.callerFrame assertion actuals result) :
    let rawChildren : DerivationList target
        (rawAssertionSidePremises projection.callerFrame assertion bodies
          (formulaBodyPattern result)) :=
      castDerivationList
        (decoding.rawAssertionSidePremises_eq rfl hresultTypecode).symm
        evidence.toDerivationList
    ∃ reflectedResult : ConstantHeadedFormula,
      formulaBodyPattern result = formulaBodyPattern reflectedResult ∧
      reflectedResult.typecode = assertion.formula.typecode ∧
      FormulaSubstitutionSemantics substitution assertion.formula
        reflectedResult ∧
      ∃ reflectedEvidence : AssertionSideEvidence target substitution
        projection.callerFrame assertion actuals reflectedResult,
        rawChildren.erase = reflectedEvidence.toDerivationList.erase := by
  exact decoding.reflectSideEvidence hprojection _

private def boundaryFrame : RuntimeFrame := ⟨#[], #[]⟩

private def boundaryAssertion : AssertionView :=
  { label := "ax-side-boundary"
    formula := ⟨"|-", []⟩
    frame := boundaryFrame
    hypotheses := [] }

/-- Negative: a free variable is not an encoded formula body, so no projected
raw side vector with that result body can be fully derived. -/
example {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1) :
    ¬ Nonempty (DerivationList target
      (rawAssertionSidePremises projection.callerFrame boundaryAssertion []
        (.fvar "not-an-encoded-body"))) := by
  rintro ⟨children⟩
  rcases (RawHypothesisBodiesDecode.nil.reflectSideEvidence hprojection
      children) with
    ⟨result, hresultBody, _hresultTypecode, _hsemantics, _evidence,
      _herasure⟩
  cases hbody : result.body with
  | nil =>
      simp [formulaBodyPattern, encodeListWith, hbody] at hresultBody
  | cons symbol symbols =>
      simp [formulaBodyPattern, encodeListWith, hbody] at hresultBody

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
