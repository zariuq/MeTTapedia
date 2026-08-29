import Mettapedia.Languages.Metamath.InferenceAssertionSideReflection

open Mettapedia.GSLT.LanguageDef

/-!
# Bounded reflection of one projected assertion root

This module closes the nonrecursive assertion-root step.  Its inputs retain
the original raw rule application, the original complete child vector, an
exact erasure split into leading and side children, and recursive reflection
evidence for each leading `Proves` child.  The final side child decodes the
raw result formula through the standalone side calculus.

The canonical local application is rebuilt from the decoded hypothesis
instances, while every recursive child proof artifact comes from the original
derivation.  No arbitrary-derivation recursion or proof regeneration from
mere semantic inhabitation is performed here.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

/-! ## Exact bounded root reflection -/

/-- Reflect one assertion root whose raw child vector has already been split
in erasure into its leading `Proves` children and its side children.

The leading reflection determines the canonical actuals and substitution.
The original final side child determines the canonical result.  The returned
generated node uses a freshly proved canonical local application but retains
the exact original leading and side proof artifacts. -/
theorem assertionRawRoot_reflects
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView} {bodies : List Pattern}
    {resultBody : Pattern} {ruleInstance : RuleInstance}
    (hassertion : assertion ∈ projection.assertions)
    (hruleId : ruleInstance.ruleId = ⟨assertion.label⟩)
    (harguments : ruleInstance.arguments = bodies ++ [resultBody])
    (application : RuleApplication target ruleInstance
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody)
      (rawAssertionConclusion assertion resultBody))
    (children : DerivationList target
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody))
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (leadingChildren : DerivationList target
      (rawAssertionProvesPremises assertion.hypotheses bodies))
    (sideChildren : DerivationList target
      (rawAssertionSidePremises projection.callerFrame assertion bodies
        resultBody))
    (hchildrenErase : children.erase =
      leadingChildren.erase ++ sideChildren.erase)
    (leadingReflection : ReflectedLeadingProvesChildren projection target
      hprojection assertion.hypotheses bodies actuals substitution
      leadingChildren) :
    ∃ result : ConstantHeadedFormula,
      resultBody = formulaBodyPattern result ∧
      result.typecode = assertion.formula.typecode ∧
      rawFormulaPattern assertion.formula.typecode resultBody =
        encodeFormula result ∧
      FormulaSubstitutionSemantics substitution assertion.formula result ∧
      ruleInstance = assertionRuleInstance assertion actuals result ∧
      ∃ node : GeneratedAssertionNode projection target assertion actuals
          result substitution,
        ∃ tree : GeneratedProvesTree projection target result,
          tree = .assertion hassertion node leadingReflection.toForest ∧
          (Derivation.byRule ruleInstance application children).erase =
            (tree.toDerivation hprojection).erase := by
  let decoding := leadingReflection.toRawHypothesisBodiesDecode
  rcases decoding.reflectSideEvidence hprojection sideChildren with
    ⟨result, hresultBody, hresultTypecode, hresultSemantics,
      sideEvidence, hsideErase⟩
  have hresultFormula :
      rawFormulaPattern assertion.formula.typecode resultBody =
        encodeFormula result :=
    rawFormulaPattern_eq_encodeFormula_of_body_typecode
      hresultBody hresultTypecode
  have hargumentsCanonical :
      ruleInstance.arguments = assertionRuleArguments actuals result :=
    harguments.trans (decoding.rawArguments_eq hresultBody)
  have hruleInstance :
      ruleInstance = assertionRuleInstance assertion actuals result := by
    rcases ruleInstance with ⟨ruleId, arguments⟩
    change ruleId = ⟨assertion.label⟩ at hruleId
    change arguments = assertionRuleArguments actuals result at hargumentsCanonical
    subst ruleId
    subst arguments
    rfl
  have canonicalApplication : RuleApplication target
      (assertionRuleInstance assertion actuals result)
      (assertionPremises substitution projection.callerFrame assertion
        actuals result)
      (proves (encodeFormula result)) :=
    assertionRuleApplication_of_instances projection target hprojection
      hassertion decoding.toHypothesisInstances hresultTypecode
  let node : GeneratedAssertionNode projection target assertion actuals
      result substitution :=
    ⟨canonicalApplication, sideEvidence⟩
  let forest : GeneratedProvesForest projection target actuals :=
    leadingReflection.toForest
  let tree : GeneratedProvesTree projection target result :=
    .assertion hassertion node forest
  have hrootErase :
      (Derivation.byRule ruleInstance application children).erase =
        (tree.toDerivation hprojection).erase := by
    calc
      (Derivation.byRule ruleInstance application children).erase =
          .node ruleInstance children.erase := rfl
      _ = .node (assertionRuleInstance assertion actuals result)
          ((forest.toDerivationList hprojection).erase ++
            sideEvidence.toDerivationList.erase) := by
        rw [hruleInstance, hchildrenErase,
          leadingReflection.erase_eq_toForest, hsideErase]
      _ = (node.assemble (forest.toDerivationList hprojection)).erase :=
        (generatedAssertionNode_erase_assemble node
          (forest.toDerivationList hprojection)).symm
      _ = (tree.toDerivation hprojection).erase := by
        rfl
  exact ⟨result, hresultBody, hresultTypecode, hresultFormula,
    hresultSemantics, hruleInstance, node, tree, rfl, hrootErase⟩

/-- Wrapper for the field equations obtained by eliminating an
`AssertionRawApplicationShape`.  It reindexes the original application and
child vector to the raw normal form without changing the child erasure, then
invokes `assertionRawRoot_reflects`. -/
theorem assertionRawShapeFields_reflect
    {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (application : RuleApplication target ruleInstance premises
      (proves formulaPattern))
    (children : DerivationList target premises)
    {assertion : AssertionView} {bodies : List Pattern}
    {resultBody : Pattern}
    (hassertion : assertion ∈ projection.assertions)
    (hruleId : ruleInstance.ruleId = ⟨assertion.label⟩)
    (harguments : ruleInstance.arguments = bodies ++ [resultBody])
    (hpremises : premises = rawAssertionPremises projection.callerFrame
      assertion bodies resultBody)
    (hformula : formulaPattern =
      rawFormulaPattern assertion.formula.typecode resultBody)
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (leadingChildren : DerivationList target
      (rawAssertionProvesPremises assertion.hypotheses bodies))
    (sideChildren : DerivationList target
      (rawAssertionSidePremises projection.callerFrame assertion bodies
        resultBody))
    (hchildrenErase : children.erase =
      leadingChildren.erase ++ sideChildren.erase)
    (leadingReflection : ReflectedLeadingProvesChildren projection target
      hprojection assertion.hypotheses bodies actuals substitution
      leadingChildren) :
    ∃ result : ConstantHeadedFormula,
      formulaPattern = encodeFormula result ∧
      resultBody = formulaBodyPattern result ∧
      result.typecode = assertion.formula.typecode ∧
      FormulaSubstitutionSemantics substitution assertion.formula result ∧
      ruleInstance = assertionRuleInstance assertion actuals result ∧
      ∃ node : GeneratedAssertionNode projection target assertion actuals
          result substitution,
        ∃ tree : GeneratedProvesTree projection target result,
          tree = .assertion hassertion node leadingReflection.toForest ∧
          (Derivation.byRule ruleInstance application children).erase =
            (tree.toDerivation hprojection).erase := by
  have rawApplication : RuleApplication target ruleInstance
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody)
      (rawAssertionConclusion assertion resultBody) := by
    simpa only [hpremises, hformula, rawAssertionConclusion] using application
  let rawChildren : DerivationList target
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody) :=
    castDerivationList hpremises children
  have hcastErase : rawChildren.erase = children.erase := by
    dsimp [rawChildren]
    exact erase_castDerivationList hpremises children
  have hrawChildrenErase : rawChildren.erase =
      leadingChildren.erase ++ sideChildren.erase := by
    exact hcastErase.trans hchildrenErase
  rcases assertionRawRoot_reflects hprojection hassertion hruleId harguments
      rawApplication rawChildren leadingChildren sideChildren
      hrawChildrenErase leadingReflection with
    ⟨result, hresultBody, hresultTypecode, hresultFormula, hsemantics,
      hruleInstance, node, tree, htree, hrawRootErase⟩
  have hformulaCanonical : formulaPattern = encodeFormula result :=
    hformula.trans hresultFormula
  have horiginalRootErase :
      (Derivation.byRule ruleInstance application children).erase =
        (tree.toDerivation hprojection).erase := by
    calc
      (Derivation.byRule ruleInstance application children).erase =
          .node ruleInstance children.erase := rfl
      _ = .node ruleInstance rawChildren.erase := by
        rw [hcastErase]
      _ = (tree.toDerivation hprojection).erase := hrawRootErase
  exact ⟨result, hformulaCanonical, hresultBody, hresultTypecode,
    hsemantics, hruleInstance, node, tree, htree, horiginalRootErase⟩

/-! ## Constructive boundaries -/

/-- Positive boundary: the bounded theorem exposes a canonical generated
assertion tree while retaining exact erasure of the supplied original root. -/
example {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView} {bodies : List Pattern}
    {resultBody : Pattern} {ruleInstance : RuleInstance}
    (hassertion : assertion ∈ projection.assertions)
    (hruleId : ruleInstance.ruleId = ⟨assertion.label⟩)
    (harguments : ruleInstance.arguments = bodies ++ [resultBody])
    (application : RuleApplication target ruleInstance
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody)
      (rawAssertionConclusion assertion resultBody))
    (children : DerivationList target
      (rawAssertionPremises projection.callerFrame assertion bodies
        resultBody))
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (leadingChildren : DerivationList target
      (rawAssertionProvesPremises assertion.hypotheses bodies))
    (sideChildren : DerivationList target
      (rawAssertionSidePremises projection.callerFrame assertion bodies
        resultBody))
    (hchildrenErase : children.erase =
      leadingChildren.erase ++ sideChildren.erase)
    (leadingReflection : ReflectedLeadingProvesChildren projection target
      hprojection assertion.hypotheses bodies actuals substitution
      leadingChildren) :
    ∃ result : ConstantHeadedFormula,
      resultBody = formulaBodyPattern result ∧
      result.typecode = assertion.formula.typecode ∧
      rawFormulaPattern assertion.formula.typecode resultBody =
        encodeFormula result ∧
      FormulaSubstitutionSemantics substitution assertion.formula result ∧
      ruleInstance = assertionRuleInstance assertion actuals result ∧
      ∃ tree : GeneratedProvesTree projection target result,
        (Derivation.byRule ruleInstance application children).erase =
          (tree.toDerivation hprojection).erase := by
  rcases assertionRawRoot_reflects hprojection hassertion hruleId harguments
      application children leadingChildren sideChildren hchildrenErase
      leadingReflection with
    ⟨result, hbody, htypecode, hformula, hsemantics, hruleInstance,
      _node, tree, _htree, herase⟩
  exact ⟨result, hbody, htypecode, hformula, hsemantics, hruleInstance,
    tree, herase⟩

private def unclassifiedGroundResultBody : Pattern :=
  .apply "unclassified-ground-result-body" []

/-- Negative boundary: even though this body is ground syntax, a complete
side vector cannot certify it as an assertion result because it is outside
the canonical encoded-body image. -/
example {projection : PrefixProjection} {target : ValidatedCalculusLanguageDef}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    {assertion : AssertionView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding : RawHypothesisBodiesDecode assertion.hypotheses bodies actuals
      substitution) :
    ¬ Nonempty (DerivationList target
      (rawAssertionSidePremises projection.callerFrame assertion bodies
        unclassifiedGroundResultBody)) := by
  rintro ⟨sideChildren⟩
  rcases decoding.reflectSideEvidence hprojection sideChildren with
    ⟨result, hresultBody, _hresultTypecode, _hsemantics, _evidence,
      _herasure⟩
  cases hbody : result.body with
  | nil =>
      simp [unclassifiedGroundResultBody, formulaBodyPattern,
        encodeListWith, Builder.nil, nilHead, hbody] at hresultBody
  | cons symbol symbols =>
      simp [unclassifiedGroundResultBody, formulaBodyPattern,
        encodeListWith, Builder.cons, consHead, hbody] at hresultBody

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
