import Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification

open Mettapedia.GSLT.LanguageDef

/-!
# Projection-derived canonical Metamath assertion evidence

Successful projection already supplies the declaration partition, source-tag
discipline, distinct floating names, and valid caller/callee DV frames needed
by canonical operational reification.  This file derives those conditions
rather than exposing them as additional inputs.

The operational caller-variable list is fixed here to the projected caller's
authored floating-variable list.  The remaining hypotheses are precisely the
operational assertion checks: floating-image typing and declarative DV
validity.  No erased source label, runtime prefix, or recursive proof of the
leading actual formulas is reconstructed.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification
open Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification

/-! ## Declaration partition -/

/-- A floating hypothesis whose formula passes the global declaration gate
names a globally declared variable. -/
theorem floatingVariable_mem_declaredVariables_of_declarations
    (declaredConstants declaredVariables : List String)
    (hypotheses : List HypothesisView)
    (hdeclared :
      hypotheses.all
        (formulaSymbolsRespectDeclarations declaredConstants
          declaredVariables ∘ HypothesisView.formula) = true)
    {variableName : String}
    (hvariable : variableName ∈ floatingVariableNames hypotheses) :
    variableName ∈ declaredVariables := by
  simp only [floatingVariableNames, List.mem_filterMap] at hvariable
  rcases hvariable with ⟨hypothesis, hhypothesis, hfloating⟩
  have hhypothesisDeclared :=
    List.all_eq_true.mp hdeclared hypothesis hhypothesis
  cases hypothesis with
  | floating label typecode authoredVariable =>
      simp only [HypothesisView.floatingVariable?, Option.some.injEq] at hfloating
      subst variableName
      simp only [Function.comp_apply, HypothesisView.formula,
        formulaSymbolsRespectDeclarations, Bool.and_eq_true,
        List.all_cons, List.all_nil, Bool.and_true] at hhypothesisDeclared
      exact List.contains_iff_mem.mp hhypothesisDeclared.2
  | essential label formula =>
      simp [HypothesisView.floatingVariable?] at hfloating

/-- A declaration-respecting formula's constants avoid every selected caller
name known to lie in the globally disjoint variable declaration list. -/
theorem formulaConstantsAvoid_of_declarationPartition
    (declaredConstants declaredVariables callerActiveNames : List String)
    (formula : ConstantHeadedFormula)
    (hseparate : declaredConstants.all (fun constantName =>
      !(declaredVariables.contains constantName)) = true)
    (hdeclared : formulaSymbolsRespectDeclarations declaredConstants
      declaredVariables formula = true)
    (hcaller : ∀ variableName, variableName ∈ callerActiveNames →
      variableName ∈ declaredVariables) :
    FormulaConstantsAvoid callerActiveNames formula := by
  intro constantName hconstant hcallerMember
  simp only [formulaSymbolsRespectDeclarations, Bool.and_eq_true] at hdeclared
  have hconstantDeclared :=
    List.all_eq_true.mp hdeclared.2 (.const constantName) hconstant
  have hconstantMember : constantName ∈ declaredConstants :=
    List.contains_iff_mem.mp hconstantDeclared
  have hnotVariable :=
    List.all_eq_true.mp hseparate constantName hconstantMember
  have hvariableMember : constantName ∈ declaredVariables :=
    hcaller constantName hcallerMember
  have hcontains : declaredVariables.contains constantName = true :=
    List.contains_iff_mem.mpr hvariableMember
  rw [hcontains] at hnotVariable
  contradiction

/-- Every retained assertion hypothesis satisfies the reverse reifier's
constant-classification boundary for the projected caller frame. -/
theorem projectedAssertion_hypothesis_constantsAvoid
    (projection : PrefixProjection) (assertion : AssertionView)
    (hvalid : prefixProjectionValid projection = true)
    (hmember : assertion ∈ projection.assertions) :
    ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      FormulaConstantsAvoid
        (floatingVariableNames projection.activeHypotheses)
        hypothesis.formula := by
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  have hseparate := hvalid.1.1.1.1.2
  have hactiveDeclared := hvalid.1.1.2
  have hassertionValid := List.all_eq_true.mp hvalid.1.2 assertion hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hassertionValid
  have hhypothesesDeclared := hassertionValid.1.2
  intro hypothesis hhypothesis
  apply formulaConstantsAvoid_of_declarationPartition
    projection.declaredConstants projection.declaredVariables
      (floatingVariableNames projection.activeHypotheses)
      hypothesis.formula hseparate
  · exact List.all_eq_true.mp hhypothesesDeclared hypothesis hhypothesis
  · intro variableName hvariable
    exact floatingVariable_mem_declaredVariables_of_declarations
      projection.declaredConstants projection.declaredVariables
      projection.activeHypotheses hactiveDeclared hvariable

/-- The retained assertion conclusion satisfies the same caller-side
constant-classification boundary. -/
theorem projectedAssertion_result_constantsAvoid
    (projection : PrefixProjection) (assertion : AssertionView)
    (hvalid : prefixProjectionValid projection = true)
    (hmember : assertion ∈ projection.assertions) :
    FormulaConstantsAvoid
      (floatingVariableNames projection.activeHypotheses)
      assertion.formula := by
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  have hseparate := hvalid.1.1.1.1.2
  have hactiveDeclared := hvalid.1.1.2
  have hassertionValid := List.all_eq_true.mp hvalid.1.2 assertion hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hassertionValid
  apply formulaConstantsAvoid_of_declarationPartition
    projection.declaredConstants projection.declaredVariables
      (floatingVariableNames projection.activeHypotheses)
      assertion.formula hseparate hassertionValid.2
  intro variableName hvariable
  exact floatingVariable_mem_declaredVariables_of_declarations
    projection.declaredConstants projection.declaredVariables
    projection.activeHypotheses hactiveDeclared hvariable

/-! ## Projection-specialized local node -/

/-- Successful presentation projection discharges every structural premise of
the canonical local assertion reifier.  The caller names are definitionally
the projected caller's authored floating names, preventing an arbitrary name
list from being conflated with the operational frame used by step soundness. -/
theorem generatedAssertionNode_of_projectedOperational
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (specSubstitution : Metamath.Spec.Subst)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          assertion.hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode)
    (hdv : Metamath.Spec.dvOK
      ((floatingVariableNames projection.activeHypotheses).map
        Metamath.Spec.Variable.mk)
      (ToSpecDVPairs assertion.frame.dj.toList)
      (ToSpecDVPairs projection.callerFrame.dj.toList) specSubstitution) :
    Nonempty
      (GeneratedAssertionNode projection target assertion
        (reifyOperationalActuals
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses) specSubstitution
          assertion.hypotheses)
        (reifyOperationalResult
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses) specSubstitution
          assertion.formula)
        (reifyOperationalSubstitution
          (floatingVariableNames projection.activeHypotheses)
          specSubstitution assertion.hypotheses)) := by
  have hvalid : prefixProjectionValid projection = true :=
    prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
      projection target.1 hprojection
  have hvalidParts := hvalid
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalidParts
  have hassertionValid :=
    List.all_eq_true.mp hvalidParts.1.2 assertion hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hassertionValid
  have hassertionFrameValid := hassertionValid.1.1.1
  simp only [frameProjectionValid, Bool.and_eq_true] at hassertionFrameValid
  have hnames :
      (floatingVariableNames assertion.hypotheses).Nodup :=
    assertion_floatingVariableNames_nodup_of_prefixProjectionValid
      projection assertion hvalid hmember
  have hhypRespect : ∀ hypothesis,
      hypothesis ∈ assertion.hypotheses →
        formulaSymbolsRespectFrame
          (floatingVariableNames assertion.hypotheses)
          hypothesis.formula = true := by
    intro hypothesis hhypothesis
    exact List.all_eq_true.mp hassertionFrameValid.1.2
      hypothesis hhypothesis
  have hresultRespect : formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses)
      assertion.formula = true :=
    hassertionValid.1.1.2
  have hcalleeDV : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true :=
    hassertionFrameValid.2
  exact generatedAssertionNode_of_operational_exact projection target hprojection
    assertion hmember
    (floatingVariableNames projection.activeHypotheses) specSubstitution
    hnames htyped hhypRespect
    (projectedAssertion_hypothesis_constantsAvoid projection assertion hvalid
      hmember)
    hresultRespect
    (projectedAssertion_result_constantsAvoid projection assertion hvalid
      hmember)
    hcalleeDV hdv

section Examples

private def partitionedFormula : ConstantHeadedFormula :=
  ⟨"wff", [.const "c", .var "x"]⟩

/-- Positive boundary: globally declared constants remain constants relative
to a caller list drawn from the disjoint variable declarations. -/
example : FormulaConstantsAvoid ["x"] partitionedFormula := by
  apply formulaConstantsAvoid_of_declarationPartition
    ["wff", "c"] ["x"] ["x"] partitionedFormula <;> decide

/-- Negative boundary: treating a surviving source constant as caller-active
violates exactly the reverse-reification condition. -/
example : ¬FormulaConstantsAvoid ["c"] partitionedFormula := by
  intro havoid
  exact havoid "c" (by simp [partitionedFormula]) (by simp)

end Examples

end Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification
