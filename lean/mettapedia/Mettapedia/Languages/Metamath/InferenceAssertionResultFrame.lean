import Mettapedia.Languages.Metamath.InferenceAssertionStepForward

/-!
# Caller-frame preservation for generated Metamath assertion results

This module proves the stack invariant needed to compose generated assertion
nodes recursively.  An assertion result respects the live caller frame when
its independent substitution semantics is supplied by an exact stack suffix
whose formulas already respect that frame.

The proof uses the projection's global constant/variable partition and the
ordinary `BodySubstitution` relation.  It assumes neither runtime step
success nor caller-frame respect of the result.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionResultFrame

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
open Mettapedia.Languages.Metamath.InferenceAssertionStepForward
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceVariableClassification
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Projection-level separation -/

private theorem floatingVariable_mem_declaredVariables_of_activeDeclarations
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

private theorem assertionConstant_mem_declaredConstants_of_viewValid
    (declaredConstants declaredVariables : List String)
    (assertion : AssertionView)
    (hvalid :
      assertionViewValid declaredConstants declaredVariables assertion = true)
    {constantName : String}
    (hconstant : .const constantName ∈ assertion.formula.body) :
    constantName ∈ declaredConstants := by
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  have hdeclarations := hvalid.2
  simp only [formulaSymbolsRespectDeclarations, Bool.and_eq_true] at hdeclarations
  have hconstantDeclared :=
    List.all_eq_true.mp hdeclarations.2 (.const constantName) hconstant
  exact List.contains_iff_mem.mp hconstantDeclared

/-- A constant occurring in a retained assertion formula cannot be one of the
caller's floating variables.  This is the global declaration partition, not
an extra local side condition. -/
theorem projectedAssertion_constant_not_callerFloating
    (projection : PrefixProjection) (assertion : AssertionView)
    (hvalid : prefixProjectionValid projection = true)
    (hmember : assertion ∈ projection.assertions)
    {constantName : String}
    (hconstant : .const constantName ∈ assertion.formula.body) :
    constantName ∉ floatingVariableNames projection.activeHypotheses := by
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  have hconstantsSeparate := hvalid.1.1.1.1.2
  have hactiveDeclarations := hvalid.1.1.2
  have hassertionValid := List.all_eq_true.mp hvalid.1.2 assertion hmember
  have hconstantDeclared : constantName ∈ projection.declaredConstants :=
    assertionConstant_mem_declaredConstants_of_viewValid
      projection.declaredConstants projection.declaredVariables assertion
      hassertionValid hconstant
  have hnotVariable :=
    List.all_eq_true.mp hconstantsSeparate constantName hconstantDeclared
  intro hcallerFloating
  have hvariableDeclared : constantName ∈ projection.declaredVariables :=
    floatingVariable_mem_declaredVariables_of_activeDeclarations
      projection.declaredConstants projection.declaredVariables
      projection.activeHypotheses hactiveDeclarations hcallerFloating
  have hcontains :
      projection.declaredVariables.contains constantName = true :=
    List.contains_iff_mem.mpr hvariableDeclared
  rw [hcontains] at hnotVariable
  contradiction

/-! ## Structural substitution preservation -/

/-- Body substitution preserves frame-respecting symbol tags when source
constants are outside the active-variable set and every visible replacement
body already respects that set. -/
theorem bodySubstitution_result_all_respects
    (floatingVariables : List String)
    {substitution : FiniteSubstitution}
    {source result : List RuntimeSym}
    (hsubstitution : BodySubstitution substitution source result)
    (hconstants : ∀ constantName,
      .const constantName ∈ source → constantName ∉ floatingVariables)
    (hreplacements : ∀ variableName replacement,
      LookupSemantics substitution variableName replacement →
        formulaSymbolsRespectFrame floatingVariables replacement = true) :
    result.all (symbolRespectsFrame floatingVariables) = true := by
  revert hconstants
  induction hsubstitution with
  | nil =>
      intro _
      rfl
  | @const constantName sourceTail resultTail tail ih =>
      intro hconstants
      simp only [List.all_cons, Bool.and_eq_true]
      constructor
      · simp [symbolRespectsFrame,
          hconstants constantName (by simp)]
      · exact ih
          (fun tailConstant htail =>
            hconstants tailConstant (by simp [htail]))
  | @var variableName replacement sourceTail resultTail binding tail ih =>
      intro hconstants
      have hreplacement := hreplacements variableName replacement binding
      simp only [formulaSymbolsRespectFrame] at hreplacement
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨hreplacement,
        ih
          (fun tailConstant htail =>
            hconstants tailConstant (by simp [htail]))⟩

/-- Formula substitution therefore preserves the caller-frame gate under the
same two independently checkable hypotheses. -/
theorem formulaSubstitutionSemantics_result_respects
    (floatingVariables : List String)
    {substitution : FiniteSubstitution}
    {source result : ConstantHeadedFormula}
    (hsubstitution :
      FormulaSubstitutionSemantics substitution source result)
    (hconstants : ∀ constantName,
      .const constantName ∈ source.body →
        constantName ∉ floatingVariables)
    (hreplacements : ∀ variableName replacement,
      LookupSemantics substitution variableName replacement →
        formulaSymbolsRespectFrame floatingVariables replacement = true) :
    formulaSymbolsRespectFrame floatingVariables result = true := by
  unfold FormulaSubstitutionSemantics at hsubstitution
  unfold formulaSymbolsRespectFrame
  exact bodySubstitution_result_all_respects floatingVariables
    hsubstitution.2 hconstants hreplacements

/-! ## Generated assertion result -/

/-- Independent generated assertion semantics preserves the live caller-frame
symbol invariant.  The exact stack suffix supplies all substitution images;
the incoming stack invariant supplies their frame respect. -/
theorem assertionApplicationSemantics_result_respects_callerFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (stack : Array RuntimeFormula)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result)
    (hwindow :
      stack.extract (stack.size - assertion.frame.hyps.size) stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    db.formulaSymsRespectFrame result.toRuntime db.frame = true := by
  rcases hsemantics with
    ⟨substitution, hinstances, _hessential, _hdv, hresult⟩
  let offset := stack.size - assertion.frame.hyps.size
  have hactualsRespect :=
    actuals_respect_callerFrame_of_stack_window
      db stack offset actuals (by simpa [offset] using hwindow)
        hstackRespects
  have hreplacementsRespect :
      ∀ variableName replacement,
        LookupSemantics substitution variableName replacement →
          formulaSymbolsRespectFrame
            (db.frameFloatVars db.frame) replacement = true := by
    intro variableName replacement hlookup
    exact hactualsRespect replacement
      (hypothesisInstances_lookup_replacement_mem_actuals
        hinstances hlookup)
  have hfields := projectPrefix?_eq_some_fields db projection hproject
  have hcallerFloats :
      db.frameFloatVars db.frame =
        floatingVariableNames projection.activeHypotheses :=
    frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
      db db.frame projection.activeHypotheses hfields.2.2.2.1
  have hprojectionValid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject
  have hconstants : ∀ constantName,
      .const constantName ∈ assertion.formula.body →
        constantName ∉ db.frameFloatVars db.frame := by
    intro constantName hconstant
    rw [hcallerFloats]
    exact projectedAssertion_constant_not_callerFloating
      projection assertion hprojectionValid hmember hconstant
  have hresultRespects :
      formulaSymbolsRespectFrame (db.frameFloatVars db.frame) result = true :=
    formulaSubstitutionSemantics_result_respects
      (db.frameFloatVars db.frame) hresult hconstants hreplacementsRespect
  rw [← formulaSymbolsRespectFrame_eq_runtime db db.frame result]
  exact hresultRespects

/-- Proof-relevant generated assertion evidence has the same preservation
consequence, without assuming execution of `stepNormal`. -/
theorem generatedAssertionNode_result_respects_callerFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (stack : Array RuntimeFormula)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hnode : Nonempty
      (Σ substitution : FiniteSubstitution,
        GeneratedAssertionNode projection target assertion actuals result
          substitution))
    (hwindow :
      stack.extract (stack.size - assertion.frame.hyps.size) stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    db.formulaSymsRespectFrame result.toRuntime db.frame = true := by
  have hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result :=
    (generatedAssertionNode_nonempty_iff_semantics projection target
      hprojection hmember actuals result).mp hnode
  exact assertionApplicationSemantics_result_respects_callerFrame
    db projection assertion stack actuals result hproject hmember
      hsemantics hwindow hstackRespects

/-! ## Positive and negative boundaries -/

namespace Examples

private def replacementX : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

private theorem lookupReplacementX :
    LookupSemantics [⟨"p", replacementX⟩] "p" replacementX := by
  simp [LookupSemantics]

private theorem substitutionExample :
    BodySubstitution [⟨"p", replacementX⟩]
      [.const "K", .var "p"] [.const "K", .var "x"] :=
  .const (.var lookupReplacementX .nil)

/-- Positive boundary: a noncolliding constant and a frame-respecting image
produce a frame-respecting substituted body. -/
example :
    [.const "K", .var "x"].all (symbolRespectsFrame ["x"]) = true := by
  apply bodySubstitution_result_all_respects ["x"] substitutionExample
  · intro constantName hconstant
    simp at hconstant
    subst constantName
    simp
  · intro variableName replacement hlookup
    simp only [LookupSemantics] at hlookup
    simp only [List.mem_singleton] at hlookup
    have hvariable := congrArg FormulaBinding.variableName hlookup
    have hreplacement := congrArg FormulaBinding.replacement hlookup
    simp only at hvariable hreplacement
    subst variableName
    subst replacement
    decide

/-- Negative boundary: copying a source constant whose name is active as a
variable fails the frame gate, so constant separation is indispensable. -/
example :
    BodySubstitution ([] : FiniteSubstitution)
      [.const "x"] [.const "x"] ∧
    [.const "x"].all (symbolRespectsFrame ["x"]) = false := by
  exact ⟨.const .nil, by decide⟩

/-- Negative boundary: a visible substitution image can itself violate the
caller frame, so replacement respect is also indispensable. -/
example :
    BodySubstitution [⟨"p", ⟨"wff", [.const "x"]⟩⟩]
      [.var "p"] [.const "x"] ∧
    [.const "x"].all (symbolRespectsFrame ["x"]) = false := by
  constructor
  · exact BodySubstitution.var
      (name := "p") (replacement := ⟨"wff", [.const "x"]⟩)
      (sourceTail := []) (resultTail := [])
      (by simp [LookupSemantics]) .nil
  · decide

end Examples

end Mettapedia.Languages.Metamath.InferenceAssertionResultFrame
