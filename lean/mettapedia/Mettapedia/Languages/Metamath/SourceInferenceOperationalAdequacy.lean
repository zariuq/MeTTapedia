import Mettapedia.Languages.Metamath.SourceInferenceExecution
import Mettapedia.Languages.Metamath.InferenceAssertionResultFrame
import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
import Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification
import Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification

open Mettapedia.GSLT.LanguageDef

/-!
# Direct operational adequacy of source-owned Metamath inference

This file removes the runtime-database detour from the semantic core of the
source-owned checker.  A finite source prefix determines its operational
caller frame and assertion database directly.  Source proof-occurrence trees
then execute in that source-derived operational database.

The construction is deliberately independent of `mm-lean4` parser or checker
execution.  Agreement with that implementation is a separate refinement
theorem.
-/

namespace Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceAssertionStepForward
open Mettapedia.Languages.Metamath.InferenceAssertionResultFrame
open Mettapedia.Languages.Metamath.InferenceVariableClassification
open Mettapedia.Languages.Metamath.InferenceOperationalExprReification
open Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification
open Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification
open Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceExecution

/-! ## Source-derived operational objects -/

/-- Operational image of one source-owned frame and its authored hypotheses. -/
def sourceOperationalFrame (frame : SourceFrame)
    (hypotheses : List HypothesisView) : Metamath.Spec.Frame :=
  operationalFrame frame.toRuntime hypotheses

/-- Operational assertion payload determined directly by a source assertion. -/
def sourceAssertionOperationalPayload
    (assertion : SourceAssertion) : Metamath.Spec.Frame × Metamath.Spec.Expr :=
  (sourceOperationalFrame assertion.frame assertion.hypotheses,
    operationalExpr assertion.formula)

/-- Source-owned operational assertion database.

The first matching assertion is selected.  Successful source-prefix validation
proves assertion labels unique, so the lookup theorem below is exact. -/
def sourceOperationalDatabase (source : SourcePrefix) :
    Metamath.Spec.Database :=
  fun label =>
    (source.assertions.find? fun assertion =>
      decide (assertion.label = label)).map
      sourceAssertionOperationalPayload

/-- The operational caller frame determined directly by a source prefix. -/
def sourceOperationalCallerFrame
    (source : SourcePrefix) : Metamath.Spec.Frame :=
  sourceOperationalFrame source.callerFrame source.activeHypotheses

private theorem find?_eq_some_of_mem_of_map_nodup
    {alpha beta : Type} [DecidableEq beta]
    (key : alpha → beta) (values : List alpha) (target : alpha)
    (hunique : (values.map key).Nodup)
    (hmem : target ∈ values) :
    values.find? (fun value => decide (key value = key target)) =
      some target := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hunique
      by_cases htarget : target = head
      · subst target
        simp [List.find?]
      · have hmemTail : target ∈ tail := by
          simpa [htarget] using hmem
        have hne : key head ≠ key target := by
          intro heq
          apply hunique.1
          rw [heq]
          exact List.mem_map_of_mem hmemTail
        simp [List.find?, hne, ih hunique.2 hmemTail]

/-- Successful source validation makes the source assertion-label suffix
duplicate-free. -/
theorem sourceAssertionLabels_nodup
    (source : SourcePrefix)
    (hvalid : sourcePrefixValid source = true) :
    (source.assertions.map SourceAssertion.label).Nodup := by
  have hvalid' := hvalid
  simp only [sourcePrefixValid, Bool.and_eq_true] at hvalid'
  have hlabels := hvalid'.2
  simp only [sourceRuleLabelsValid, Bool.and_eq_true, beq_iff_eq] at hlabels
  have hallLabels :
      (sourcePrefixRuleLabels source).Nodup :=
    nodup_of_eraseDups_length_eq _ hlabels.2
  simpa [sourcePrefixRuleLabels] using
    (List.nodup_append.mp hallLabels).2.1

/-- Membership in a valid source prefix determines the exact source-derived
operational lookup. -/
theorem sourceOperationalDatabase_lookup
    (source : SourcePrefix) (assertion : SourceAssertion)
    (hvalid : sourcePrefixValid source = true)
    (hmember : assertion ∈ source.assertions) :
    sourceOperationalDatabase source assertion.label =
      some (sourceAssertionOperationalPayload assertion) := by
  unfold sourceOperationalDatabase
  have hfind :=
    find?_eq_some_of_mem_of_map_nodup
      SourceAssertion.label source.assertions assertion
      (sourceAssertionLabels_nodup source hvalid) hmember
  rw [hfind]
  rfl

/-- Every successful lookup in the source-derived operational database comes
from an authored source assertion. -/
theorem sourceOperationalDatabase_lookup_exists
    (source : SourcePrefix) (label : String)
    (payload : Metamath.Spec.Frame × Metamath.Spec.Expr)
    (hlookup :
      sourceOperationalDatabase source label = some payload) :
    ∃ assertion : SourceAssertion,
      assertion ∈ source.assertions ∧
      assertion.label = label ∧
      sourceAssertionOperationalPayload assertion = payload := by
  unfold sourceOperationalDatabase at hlookup
  cases hfind :
      source.assertions.find?
        (fun assertion => decide (assertion.label = label)) with
  | none =>
      simp [hfind] at hlookup
  | some assertion =>
      have hmember : assertion ∈ source.assertions :=
        List.mem_of_find?_eq_some hfind
      have hlabelBool :
          decide (assertion.label = label) = true :=
        List.find?_some
          (p := fun candidate : SourceAssertion =>
            decide (candidate.label = label))
          hfind
      have hlabel : assertion.label = label :=
        of_decide_eq_true hlabelBool
      simp only [hfind, Option.map_some, Option.some.injEq] at hlookup
      exact ⟨assertion, hmember, hlabel, hlookup⟩

/-- Successful source-presentation generation exposes the source validity
gate without consulting a runtime database. -/
theorem sourcePrefixValid_of_presentationOfSourcePrefix?_eq_some
    (source : SourcePrefix) (target : ValidatedCalculusLanguageDef)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1) :
    sourcePrefixValid source = true := by
  have hruntime :
      calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact hsource
  have hvalid :=
    prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
      source.toProjection target.1 hruntime
  simpa using hvalid

/-! ## Frame-respect invariant of source proof trees -/

mutual

/-- Every result in a source-owned proof tree respects the source caller's
active-variable classification. -/
theorem sourceTree_result_respects
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (tree : SourceGeneratedProvesTree source target formula) :
    formulaSymbolsRespectFrame
      (floatingVariableNames source.activeHypotheses) formula = true := by
  cases tree with
  | active hypothesis hmember =>
      have hvalid :
          prefixProjectionValid source.toProjection = true := by
        exact prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
          source.toProjection target.1
            (calculusLanguageDefOfSourcePrefix?_eq_runtime source ▸ hsource)
      simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
      have hframe :
          frameProjectionValid source.callerFrame.toRuntime
            source.activeHypotheses = true := hvalid.1.1.1.2
      simp only [frameProjectionValid, Bool.and_eq_true] at hframe
      exact List.all_eq_true.mp hframe.1.2 hypothesis hmember
  | @assertion assertion actuals _result substitution hmember node children =>
      have hruntime :
          calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
        rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
        exact hsource
      have hprojectionValid :
          prefixProjectionValid source.toProjection = true :=
        prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
          source.toProjection target.1 hruntime
      have hassertionMember :
          assertion.toProjectionView ∈ source.toProjection.assertions :=
        List.mem_map.mpr ⟨assertion, hmember, rfl⟩
      have hsemantics :
          AssertionApplicationSemantics
            source.toProjection.callerFrame assertion.toProjectionView
            actuals formula :=
        (generatedAssertionNode_nonempty_iff_semantics
          source.toProjection target hruntime hassertionMember actuals
            formula).mp
            ⟨⟨substitution, node⟩⟩
      rcases hsemantics with
        ⟨finiteSubstitution, instances, _essential, _dv, resultSemantics⟩
      have hactualsRespect :
          ∀ actual, actual ∈ actuals →
            formulaSymbolsRespectFrame
              (floatingVariableNames source.activeHypotheses) actual = true :=
        List.all_eq_true.mp (sourceForest_all_respect children hsource)
      have hreplacements :
          ∀ variableName replacement,
            LookupSemantics finiteSubstitution variableName replacement →
              formulaSymbolsRespectFrame
                (floatingVariableNames source.activeHypotheses)
                replacement = true := by
        intro variableName replacement hlookup
        exact hactualsRespect replacement
          (hypothesisInstances_lookup_replacement_mem_actuals
            instances hlookup)
      have hconstants :
          ∀ constantName,
            .const constantName ∈ assertion.formula.body →
              constantName ∉
                floatingVariableNames source.activeHypotheses := by
        intro constantName hconstant
        exact projectedAssertion_constant_not_callerFloating
          source.toProjection assertion.toProjectionView hprojectionValid
          hassertionMember hconstant
      exact formulaSubstitutionSemantics_result_respects
        (floatingVariableNames source.activeHypotheses)
        resultSemantics hconstants hreplacements
termination_by sizeOf tree
decreasing_by
  all_goals subst_vars
  all_goals simp_wf

/-- Every formula in a source-owned proof forest respects the same caller
classification. -/
theorem sourceForest_all_respect
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (forest : SourceGeneratedProvesForest source target formulas)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1) :
    formulas.all (formulaSymbolsRespectFrame
      (floatingVariableNames source.activeHypotheses)) = true := by
  cases forest with
  | nil => rfl
  | cons head tail =>
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨sourceTree_result_respects hsource head,
        sourceForest_all_respect tail hsource⟩
termination_by sizeOf forest
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end

/-! ## Direct source assertion step -/

/-- One proof-relevant source assertion node is exactly an operational
assertion step in the database derived from the same source prefix. -/
theorem sourceGeneratedAssertionNode_toProofValidFrom
    (source : SourcePrefix) (target : ValidatedCalculusLanguageDef)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (assertion : SourceAssertion)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution)
    (hmember : assertion ∈ source.assertions)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr)
    (hactualsRespect : ∀ actual, actual ∈ actuals →
      formulaSymbolsRespectFrame
        (floatingVariableNames source.activeHypotheses) actual = true) :
    Metamath.Spec.ProofValidFrom
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source)
      ((actuals.map operationalExpr).reverse ++ remaining)
      (operationalExpr result :: remaining)
      [Metamath.Spec.ProofStep.useAssertion assertion.label
        (operationalSubstitution fallback substitution)] := by
  let callerSpec := sourceOperationalCallerFrame source
  let calleeSpec :=
    sourceOperationalFrame assertion.frame assertion.hypotheses
  let specSubstitution := operationalSubstitution fallback substitution
  have hruntime :
      calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
    rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
    exact hsource
  have hassertionMember :
      assertion.toProjectionView ∈ source.toProjection.assertions :=
    List.mem_map.mpr ⟨assertion, hmember, rfl⟩
  have hprojectionValid :
      prefixProjectionValid source.toProjection = true :=
    prefixProjectionValid_of_calculusLanguageDefOfProjection?_eq_some
      source.toProjection target.1 hruntime
  have hsourceValid :
      sourcePrefixValid source = true :=
    sourcePrefixValid_of_presentationOfSourcePrefix?_eq_some
      source target hsource
  rcases (assertionRuleApplication_iff_instances
      source.toProjection target hruntime hassertionMember).mp
      node.application with
    ⟨hinstances, _hresultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics
      source.toProjection target hruntime hinstances).mp
      ⟨node.sideEvidence⟩ with
    ⟨hessential, hdv, hresult⟩
  have hinstancesSource :
      HypothesisInstances assertion.hypotheses actuals substitution := by
    simpa [SourceAssertion.toProjectionView] using hinstances
  have hessentialSource :
      EssentialMatches substitution assertion.hypotheses actuals := by
    simpa [SourceAssertion.toProjectionView] using hessential
  have hdvSource :
      DVOKSemantics substitution source.callerFrame.toRuntime
        assertion.frame.toRuntime := by
    simpa [SourcePrefix.toProjection, SourceAssertion.toProjectionView] using
      hdv
  have hresultSource :
      FormulaSubstitutionSemantics substitution assertion.formula result := by
    simpa [SourceAssertion.toProjectionView] using hresult
  have hunique : SubstitutionKeysUnique substitution :=
    hinstances.substitutionKeysUnique_of_generatedAssertion
      source.toProjection target.1 hruntime hassertionMember
  have hassertionValid :
      assertionViewValid source.declaredConstants source.declaredVariables
        assertion.toProjectionView = true := by
    simp only [prefixProjectionValid, Bool.and_eq_true] at hprojectionValid
    exact List.all_eq_true.mp hprojectionValid.1.2
      assertion.toProjectionView hassertionMember
  have hassertionValidParts := hassertionValid
  simp only [assertionViewValid, Bool.and_eq_true] at hassertionValidParts
  have hassertionFrameValid :
      frameProjectionValid assertion.frame.toRuntime
        assertion.hypotheses = true := by
    simpa [SourceAssertion.toProjectionView] using
      hassertionValidParts.1.1.1
  have hhypothesisRespect :
      ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
        formulaSymbolsRespectFrame
          (floatingVariableNames assertion.hypotheses)
          hypothesis.formula = true := by
    simp only [frameProjectionValid, Bool.and_eq_true] at hassertionFrameValid
    exact List.all_eq_true.mp hassertionFrameValid.1.2
  have hsourceRespect :
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        assertion.formula = true := by
    simpa [SourceAssertion.toProjectionView] using
      hassertionValidParts.1.1.2
  have htyped :
      ∀ c v, Metamath.Spec.Hyp.floating c v ∈ calleeSpec.hyps →
        (specSubstitution v).typecode = c := by
    simpa [calleeSpec, specSubstitution, sourceOperationalFrame,
      operationalFrame] using
        hypothesisInstances_operational_typed
          hinstancesSource hunique fallback
  have hneeded :
      Metamath.Bridge.needed calleeSpec.vars calleeSpec specSubstitution =
        actuals.map operationalExpr := by
    simpa [calleeSpec, specSubstitution, sourceOperationalFrame] using
      hypothesisInstances_operational_needed_eq
        (frame := assertion.frame.toRuntime) hinstancesSource hunique fallback
          hessentialSource hhypothesisRespect
  have hresultSpec :
      Metamath.Spec.applySubst calleeSpec.vars specSubstitution
          (operationalExpr assertion.formula) =
        operationalExpr result := by
    simpa [calleeSpec, specSubstitution, sourceOperationalFrame] using
      formulaSubstitutionSemantics_to_spec_applySubst fallback hunique
        (floatingVariableNames assertion.hypotheses) hsourceRespect
          hresultSource
  have hcallerFrameValid :
      frameProjectionValid source.callerFrame.toRuntime
        source.activeHypotheses = true := by
    have hvalidCopy := hprojectionValid
    simp only [prefixProjectionValid, Bool.and_eq_true] at hvalidCopy
    exact hvalidCopy.1.1.1.2
  have hcallerDV :
      frameDVValid source.callerFrame.toRuntime
        (floatingVariableNames source.activeHypotheses) = true := by
    have hframeCopy := hcallerFrameValid
    simp only [frameProjectionValid, Bool.and_eq_true] at hframeCopy
    exact hframeCopy.2
  have hcallerStrict :
      source.callerFrame.distinctVariables.all
        (fun pair => decide (pair.1 < pair.2)) = true := by
    simp only [frameDVValid, SourceFrame.toRuntime] at hcallerDV
    apply List.all_eq_true.mpr
    intro pair hpair
    have hpairValid := List.all_eq_true.mp hcallerDV pair hpair
    simp only [Bool.and_eq_true] at hpairValid
    exact hpairValid.1.1
  have hcallerDistinct :
      DVPairNamesDistinct source.callerFrame.distinctVariables :=
    dvPairNamesDistinct_of_strictOrderAll
      source.callerFrame.distinctVariables hcallerStrict
  have hcallerNames :
      Metamath.Kernel.varNames callerSpec.vars =
        floatingVariableNames source.activeHypotheses := by
    simp [callerSpec, sourceOperationalCallerFrame,
      sourceOperationalFrame, operationalFrame_vars,
      Metamath.Kernel.varNames, Function.comp_def]
  have hsubstitutionImage : ∀ name replacement,
      LookupSemantics substitution name replacement →
        specSubstitution ⟨name⟩ = operationalExpr replacement := by
    intro name replacement hlookup
    exact operationalSubstitution_eq_of_lookup fallback hunique hlookup
  have hreplacementRespect : ∀ name replacement,
      LookupSemantics substitution name replacement →
        formulaSymbolsRespectFrame
          (floatingVariableNames source.activeHypotheses)
          replacement = true := by
    intro name replacement hlookup
    exact hactualsRespect replacement
      (hypothesisInstances_lookup_replacement_mem_actuals
        hinstances hlookup)
  have hclassification : ∀ name replacement,
      LookupSemantics substitution name replacement →
        Metamath.Spec.varsInExpr callerSpec.vars
            (specSubstitution ⟨name⟩) =
          (BodyVariables replacement.body).map
            Metamath.Spec.Variable.mk :=
    lookup_varsInExpr_classification substitution callerSpec.vars
      (floatingVariableNames source.activeHypotheses)
      specSubstitution hcallerNames hsubstitutionImage hreplacementRespect
  have hdvSpec :
      Metamath.Spec.dvOK callerSpec.vars calleeSpec.dv callerSpec.dv
        specSubstitution := by
    simpa [callerSpec, calleeSpec, sourceOperationalCallerFrame,
      sourceOperationalFrame, operationalFrame] using
      dvOKSemantics_implies_spec_dvOK substitution
        source.callerFrame.toRuntime assertion.frame.toRuntime
        callerSpec.vars specSubstitution hcallerDistinct hclassification
          hdvSource
  have hlookup :
      sourceOperationalDatabase source assertion.label =
        some (calleeSpec, operationalExpr assertion.formula) := by
    simpa [calleeSpec, sourceAssertionOperationalPayload,
      sourceOperationalFrame] using
      sourceOperationalDatabase_lookup source assertion hsourceValid hmember
  have hbase := Metamath.Spec.ProofValidFrom.nil
    (Γ := sourceOperationalDatabase source) callerSpec
      ((actuals.map operationalExpr).reverse ++ remaining)
  have hneededConstructor :
      actuals.map operationalExpr =
        calleeSpec.hyps.map (fun hypothesis =>
          match hypothesis with
          | .essential formula =>
              Metamath.Spec.applySubst calleeSpec.vars specSubstitution formula
          | .floating _ v => specSubstitution v) := by
    convert hneeded.symm using 1
    apply List.map_congr_left
    intro hypothesis _hmember
    cases hypothesis <;> rfl
  have hstep := Metamath.Spec.ProofValidFrom.useAxiom
    (Γ := sourceOperationalDatabase source)
    (fr := callerSpec)
    (stk := (actuals.map operationalExpr).reverse ++ remaining)
    (stack := (actuals.map operationalExpr).reverse ++ remaining)
    (steps := []) (l := assertion.label) (fr' := calleeSpec)
    (e := operationalExpr assertion.formula) (σ := specSubstitution)
    hlookup hdvSpec htyped hbase
    (actuals.map operationalExpr) hneededConstructor remaining rfl
  rw [hresultSpec] at hstep
  simpa [callerSpec, calleeSpec, specSubstitution] using hstep

/-! ## Exact source occurrence execution -/

/-- One source-owned active hypothesis is one direct operational hypothesis
step in the source-derived caller frame. -/
theorem sourceActiveHypothesis_toProofValidFrom
    (source : SourcePrefix) (hypothesis : HypothesisView)
    (hmember : hypothesis ∈ source.activeHypotheses)
    (remaining : List Metamath.Spec.Expr) :
    Metamath.Spec.ProofValidFrom
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source)
      remaining (operationalExpr hypothesis.formula :: remaining)
      [Metamath.Spec.ProofStep.useHyp (operationalHyp hypothesis)] := by
  cases hypothesis with
  | floating label typecode variableName =>
      have hin :
          Metamath.Spec.Hyp.floating ⟨typecode⟩ ⟨variableName⟩ ∈
            (sourceOperationalCallerFrame source).hyps := by
        apply List.mem_map.mpr
        exact ⟨.floating label typecode variableName, hmember, rfl⟩
      have hnil := Metamath.Spec.ProofValidFrom.nil
        (Γ := sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source) remaining
      have hstep := Metamath.Spec.ProofValidFrom.useFloating
        (Γ := sourceOperationalDatabase source)
        (fr := sourceOperationalCallerFrame source)
        (stk := remaining) (stack := remaining) (steps := [])
        (c := Metamath.Spec.Constant.mk typecode)
        (v := Metamath.Spec.Variable.mk variableName) hin hnil
      simpa [HypothesisView.formula, operationalHyp, operationalExpr,
        ConstantHeadedFormula.toRuntime, Metamath.Kernel.toExpr,
        Metamath.Kernel.toSym, Metamath.Verify.Sym.value] using hstep
  | essential label formula =>
      have hin :
          Metamath.Spec.Hyp.essential (operationalExpr formula) ∈
            (sourceOperationalCallerFrame source).hyps := by
        apply List.mem_map.mpr
        exact ⟨.essential label formula, hmember, rfl⟩
      exact Metamath.Spec.ProofValidFrom.useEssential
        (Γ := sourceOperationalDatabase source)
        (fr := sourceOperationalCallerFrame source)
        (stk := remaining) (stack := remaining) (steps := [])
        (e := operationalExpr formula) hin
        (Metamath.Spec.ProofValidFrom.nil
          (Γ := sourceOperationalDatabase source)
          (sourceOperationalCallerFrame source) remaining)

mutual

/-- Reverse-chronological operational steps carried by a source proof tree.
This order is the native order of `Metamath.Spec.ProofValidFrom`. -/
def sourceTreeOperationalSteps
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (fallback : Metamath.Spec.Subst) :
    SourceGeneratedProvesTree source target formula →
      List Metamath.Spec.ProofStep
  | .active hypothesis _ =>
      [.useHyp (operationalHyp hypothesis)]
  | .assertion (assertion := assertion) (substitution := substitution)
      _ _ children =>
      .useAssertion assertion.label
          (operationalSubstitution fallback substitution) ::
        sourceForestOperationalSteps fallback children

/-- Reverse-chronological operational steps for a forest whose trees execute
from head to tail. -/
def sourceForestOperationalSteps
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (fallback : Metamath.Spec.Subst) :
    SourceGeneratedProvesForest source target formulas →
      List Metamath.Spec.ProofStep
  | .nil => []
  | .cons head tail =>
      sourceForestOperationalSteps fallback tail ++
        sourceTreeOperationalSteps fallback head

end

mutual

/-- Exact direct operational execution of a source-owned proof tree. -/
theorem sourceTree_toProofValidFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (tree : SourceGeneratedProvesTree source target formula)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr) :
    Metamath.Spec.ProofValidFrom
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source)
      remaining (operationalExpr formula :: remaining)
      (sourceTreeOperationalSteps fallback tree) := by
  cases tree with
  | active hypothesis hmember =>
      exact sourceActiveHypothesis_toProofValidFrom
        source hypothesis hmember remaining
  | @assertion assertion actuals _result substitution hmember node children =>
      have hchildren :=
        sourceForest_toProofValidFrom hsource children fallback remaining
      have hactualsRespect :
          ∀ actual, actual ∈ actuals →
            formulaSymbolsRespectFrame
              (floatingVariableNames source.activeHypotheses) actual = true :=
        List.all_eq_true.mp (sourceForest_all_respect children hsource)
      have hassertion :=
        sourceGeneratedAssertionNode_toProofValidFrom
          source target hsource assertion actuals formula substitution node
          hmember fallback remaining hactualsRespect
      exact Metamath.Spec.ProofValidFrom.trans hchildren hassertion
termination_by sizeOf tree
decreasing_by
  all_goals subst_vars
  all_goals simp_wf

/-- Exact direct execution of an ordered source-owned proof forest. -/
theorem sourceForest_toProofValidFrom
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formulas : List ConstantHeadedFormula}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (forest : SourceGeneratedProvesForest source target formulas)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr) :
    Metamath.Spec.ProofValidFrom
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source)
      remaining
      ((formulas.map operationalExpr).reverse ++ remaining)
      (sourceForestOperationalSteps fallback forest) := by
  cases forest with
  | nil =>
      simpa [sourceForestOperationalSteps] using
        Metamath.Spec.ProofValidFrom.nil
        (Γ := sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source) remaining
  | @cons formula formulas head tail =>
      have hhead :=
        sourceTree_toProofValidFrom hsource head fallback remaining
      have htail :=
        sourceForest_toProofValidFrom hsource tail fallback
          (operationalExpr formula :: remaining)
      simpa [sourceForestOperationalSteps, List.reverse_cons,
        List.append_assoc] using
          Metamath.Spec.ProofValidFrom.trans hhead htail
termination_by sizeOf forest
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end

/-- A source proof-occurrence tree proves its conclusion in the operational
Metamath semantics derived from the same source prefix. -/
theorem sourceTree_to_sourceOperationalProvable
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {formula : ConstantHeadedFormula}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (tree : SourceGeneratedProvesTree source target formula)
    (fallback : Metamath.Spec.Subst) :
    Metamath.Spec.Provable
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source)
      (operationalExpr formula) := by
  have hfrom :=
    sourceTree_toProofValidFrom hsource tree fallback []
  have hvalid :
      Metamath.Spec.ProofValid
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        [operationalExpr formula]
        (sourceTreeOperationalSteps fallback tree) := by
    apply Metamath.Spec.ProofValidFrom.toProofValid
    simpa using hfrom
  exact Metamath.Spec.ProofValid.toProvable hvalid

/-! ## Source proof stacks for operational reflection -/

/-- One source proof tree together with its dependent conclusion formula. -/
structure SourceProofItem (source : SourcePrefix)
    (target : ValidatedCalculusLanguageDef) where
  formula : ConstantHeadedFormula
  tree : SourceGeneratedProvesTree source target formula

/-- Erase a stack of source proof occurrences to the operational expression
stack. -/
def sourceProofStackImage
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (items : List (SourceProofItem source target)) :
    List Metamath.Spec.Expr :=
  items.map (operationalExpr ∘ SourceProofItem.formula)

/-- Reassemble a list of dependent source proof items as an ordered source
proof forest. -/
def sourceProofItemsToForest
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef} :
    (items : List (SourceProofItem source target)) →
      SourceGeneratedProvesForest source target
        (items.map SourceProofItem.formula)
  | [] => .nil
  | item :: items =>
      .cons item.tree (sourceProofItemsToForest items)

/-- Every formula carried by a source proof stack has the unique canonical
tagging determined by its operational erasure and the source caller frame. -/
theorem sourceProofItems_formulas_eq_reify_image
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (items : List (SourceProofItem source target)) :
    items.map SourceProofItem.formula =
      (sourceProofStackImage items).map
        (reifyOperationalExpr
          (floatingVariableNames source.activeHypotheses)) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.map_cons, sourceProofStackImage, Function.comp_apply]
      rw [reifyOperationalExpr_operationalExpr_of_respectsFrame
        (floatingVariableNames source.activeHypotheses) item.formula
        (sourceTree_result_respects hsource item.tree)]
      exact congrArg (List.cons item.formula) ih

/-- Image equality therefore determines the exact source formula list. -/
theorem sourceProofItems_formulas_eq_reify
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (items : List (SourceProofItem source target))
    (expressions : List Metamath.Spec.Expr)
    (himage : sourceProofStackImage items = expressions) :
    items.map SourceProofItem.formula =
      expressions.map
        (reifyOperationalExpr
          (floatingVariableNames source.activeHypotheses)) := by
  rw [sourceProofItems_formulas_eq_reify_image hsource items, himage]

/-- Canonical operational actuals are pointwise reification of the
operational mandatory-hypothesis vector. -/
def sourceOperationalHypInstance
    (calleeVariables : List Metamath.Spec.Variable)
    (specSubstitution : Metamath.Spec.Subst) :
    Metamath.Spec.Hyp → Metamath.Spec.Expr
  | .floating _ variableName => specSubstitution variableName
  | .essential expression =>
      Metamath.Spec.applySubst calleeVariables specSubstitution expression

theorem reifyOperationalActuals_eq_map_reifyNeeded
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView) :
    reifyOperationalActuals callerActiveNames calleeActiveNames
        specSubstitution hypotheses =
      ((hypotheses.map operationalHyp).map
        (sourceOperationalHypInstance
          (calleeActiveNames.map Metamath.Spec.Variable.mk)
          specSubstitution)).map
        (reifyOperationalExpr callerActiveNames) := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [reifyOperationalActuals, sourceOperationalHypInstance,
          operationalHyp, ih]

/-! ## Operational reflection into source proof stacks -/

/-- Every operational proof over the source-derived database has a stack of
source-owned proof occurrences with exactly the same expression image. -/
theorem proofValid_exists_sourceProofStack
    (source : SourcePrefix) (target : ValidatedCalculusLanguageDef)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    {stack : List Metamath.Spec.Expr}
    {steps : List Metamath.Spec.ProofStep}
    (proof : Metamath.Spec.ProofValid
      (sourceOperationalDatabase source)
      (sourceOperationalCallerFrame source) stack steps) :
    ∃ items : List (SourceProofItem source target),
      sourceProofStackImage items = stack := by
  induction proof with
  | nil =>
      exact ⟨[], rfl⟩
  | useEssential stack steps expression hmember _prior ih =>
      change Metamath.Spec.Hyp.essential expression ∈
        source.activeHypotheses.map operationalHyp at hmember
      rcases List.mem_map.mp hmember with
        ⟨hypothesis, hsourceMember, hhypothesis⟩
      cases hypothesis with
      | floating label typecode variableName =>
          simp [operationalHyp] at hhypothesis
      | essential label formula =>
          simp only [operationalHyp, Metamath.Spec.Hyp.essential.injEq]
            at hhypothesis
          rcases ih with ⟨items, hitems⟩
          refine
            ⟨{ formula := formula
               tree := .active (.essential label formula) hsourceMember } ::
                items,
              ?_⟩
          change operationalExpr formula :: sourceProofStackImage items =
            expression :: stack
          rw [hhypothesis, hitems]
  | useFloating stack steps typecode variableName hmember _prior ih =>
      change Metamath.Spec.Hyp.floating typecode variableName ∈
        source.activeHypotheses.map operationalHyp at hmember
      rcases List.mem_map.mp hmember with
        ⟨hypothesis, hsourceMember, hhypothesis⟩
      cases hypothesis with
      | floating label authoredTypecode authoredVariable =>
          simp only [operationalHyp, Metamath.Spec.Hyp.floating.injEq]
            at hhypothesis
          rcases hhypothesis with ⟨htypecode, hvariable⟩
          rcases ih with ⟨items, hitems⟩
          refine
            ⟨{ formula :=
                (HypothesisView.floating label authoredTypecode
                  authoredVariable).formula
               tree :=
                .active
                  (.floating label authoredTypecode authoredVariable)
                  hsourceMember } :: items,
              ?_⟩
          subst typecode
          subst variableName
          change
            operationalExpr
                (HypothesisView.floating label authoredTypecode
                  authoredVariable).formula ::
                sourceProofStackImage items =
              { typecode := ⟨authoredTypecode⟩
                syms := [authoredVariable] } :: stack
          rw [hitems]
          rfl
      | essential label formula =>
          simp [operationalHyp] at hhypothesis
  | @useAxiom priorStack priorSteps label assertionFrame assertionExpression
      specSubstitution hlookup hdv htyped _prior needed hneeded remaining
      hstack ih =>
      rcases sourceOperationalDatabase_lookup_exists source label
          (assertionFrame, assertionExpression) hlookup with
        ⟨assertion, hassertionMember, hlabel, hpayload⟩
      subst label
      have hframe :
          sourceOperationalFrame assertion.frame assertion.hypotheses =
            assertionFrame :=
        congrArg Prod.fst hpayload
      have hexpression :
          operationalExpr assertion.formula = assertionExpression :=
        congrArg Prod.snd hpayload
      subst assertionFrame
      subst assertionExpression
      rcases ih with ⟨items, hitems⟩
      have hstackImage :
          sourceProofStackImage items = needed.reverse ++ remaining :=
        hitems.trans hstack
      let consumed := items.take needed.length
      let rest := items.drop needed.length
      have hconsumedImage :
          sourceProofStackImage consumed = needed.reverse := by
        have htaken :=
          congrArg (List.take needed.length) hstackImage
        simpa [consumed, sourceProofStackImage] using htaken
      have hrestImage :
          sourceProofStackImage rest = remaining := by
        have hdropped :=
          congrArg (List.drop needed.length) hstackImage
        simpa [rest, sourceProofStackImage] using hdropped
      let actualItems := consumed.reverse
      have hactualImage :
          sourceProofStackImage actualItems = needed := by
        calc
          sourceProofStackImage actualItems =
              (sourceProofStackImage consumed).reverse := by
                simp [actualItems, sourceProofStackImage]
          _ = (needed.reverse).reverse :=
            congrArg List.reverse hconsumedImage
          _ = needed := List.reverse_reverse needed
      let callerNames :=
        floatingVariableNames source.activeHypotheses
      let calleeNames :=
        floatingVariableNames assertion.hypotheses
      let canonicalActuals :=
        reifyOperationalActuals callerNames calleeNames
          specSubstitution assertion.hypotheses
      let canonicalResult :=
        reifyOperationalResult callerNames calleeNames
          specSubstitution assertion.formula
      have hneededCanonical :
          needed =
            (assertion.hypotheses.map operationalHyp).map
              (sourceOperationalHypInstance
                (calleeNames.map Metamath.Spec.Variable.mk)
                specSubstitution) := by
        rw [hneeded]
        apply List.map_congr_left
        intro hypothesis _hmember
        cases hypothesis <;>
          simp [sourceOperationalHypInstance, sourceOperationalFrame,
            calleeNames]
      have hcanonicalActuals :
          canonicalActuals =
            needed.map (reifyOperationalExpr callerNames) := by
        rw [show canonicalActuals =
            reifyOperationalActuals callerNames calleeNames
              specSubstitution assertion.hypotheses by rfl]
        rw [reifyOperationalActuals_eq_map_reifyNeeded]
        rw [← hneededCanonical]
      have hactualFormulas :
          actualItems.map SourceProofItem.formula = canonicalActuals := by
        exact
          (sourceProofItems_formulas_eq_reify hsource actualItems needed
            hactualImage).trans hcanonicalActuals.symm
      let children :
          SourceGeneratedProvesForest source target canonicalActuals :=
        hactualFormulas ▸ sourceProofItemsToForest actualItems
      have hruntime :
          calculusLanguageDefOfProjection? source.toProjection = some target.1 := by
        rw [← calculusLanguageDefOfSourcePrefix?_eq_runtime]
        exact hsource
      have hassertionProjectionMember :
          assertion.toProjectionView ∈ source.toProjection.assertions :=
        List.mem_map.mpr ⟨assertion, hassertionMember, rfl⟩
      have htypedSource :
          ∀ typecode variableName,
            Metamath.Spec.Hyp.floating typecode variableName ∈
                assertion.hypotheses.map operationalHyp →
              (specSubstitution variableName).typecode = typecode := by
        simpa [sourceOperationalFrame, operationalFrame] using htyped
      have hdvSource :
          Metamath.Spec.dvOK
            (callerNames.map Metamath.Spec.Variable.mk)
            (ToSpecDVPairs assertion.frame.distinctVariables)
            (ToSpecDVPairs source.callerFrame.distinctVariables)
            specSubstitution := by
        have hcallerVars :
            (sourceOperationalCallerFrame source).vars =
              callerNames.map Metamath.Spec.Variable.mk := by
          change
            (operationalFrame source.callerFrame.toRuntime
              source.activeHypotheses).vars =
                (floatingVariableNames source.activeHypotheses).map
                  Metamath.Spec.Variable.mk
          exact operationalFrame_vars source.callerFrame.toRuntime
            source.activeHypotheses
        rw [← hcallerVars]
        simpa [sourceOperationalCallerFrame, sourceOperationalFrame,
          operationalFrame, SourceFrame.toRuntime] using hdv
      rcases generatedAssertionNode_of_projectedOperational
          source.toProjection target hruntime assertion.toProjectionView
          hassertionProjectionMember specSubstitution htypedSource
          hdvSource with
        ⟨node⟩
      let tree :
          SourceGeneratedProvesTree source target canonicalResult :=
        .assertion hassertionMember node children
      have hresultImage :
          operationalExpr canonicalResult =
            Metamath.Spec.applySubst
              (sourceOperationalFrame assertion.frame
                assertion.hypotheses).vars
              specSubstitution (operationalExpr assertion.formula) := by
        simp [canonicalResult, calleeNames, sourceOperationalFrame]
      refine
        ⟨{ formula := canonicalResult
           tree := tree } :: rest,
          ?_⟩
      change operationalExpr canonicalResult ::
          sourceProofStackImage rest =
        Metamath.Spec.applySubst
            (sourceOperationalFrame assertion.frame
              assertion.hypotheses).vars
            specSubstitution (operationalExpr assertion.formula) ::
          remaining
      rw [hresultImage, hrestImage]

/-! ## Direct operational equivalence -/

/-- Operational provability in the source-derived database reconstructs one
canonical source-owned proof-occurrence tree.  The conclusion is reified with
the source caller frame because operational expressions erase source
variable/constant tags. -/
theorem sourceOperationalProvable_to_sourceTree
    (source : SourcePrefix) (target : ValidatedCalculusLanguageDef)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    {expression : Metamath.Spec.Expr}
    (hprovable :
      Metamath.Spec.Provable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        expression) :
    Nonempty
      (SourceGeneratedProvesTree source target
        (reifyOperationalExpr
          (floatingVariableNames source.activeHypotheses)
          expression)) := by
  rcases hprovable with ⟨steps, finalStack, hvalid, hfinal⟩
  rcases proofValid_exists_sourceProofStack source target hsource hvalid with
    ⟨items, himage⟩
  have himageSingleton :
      sourceProofStackImage items = [expression] :=
    himage.trans hfinal
  cases items with
  | nil =>
      simp [sourceProofStackImage] at himageSingleton
  | cons item items =>
      cases items with
      | nil =>
          have herasure :
              operationalExpr item.formula = expression := by
            simpa [sourceProofStackImage] using himageSingleton
          have hformula :
              item.formula =
                reifyOperationalExpr
                  (floatingVariableNames source.activeHypotheses)
                  expression :=
            eq_reifyOperationalExpr_of_respectsFrame
              (floatingVariableNames source.activeHypotheses)
              item.formula expression
              (sourceTree_result_respects hsource item.tree)
              herasure
          exact ⟨hformula ▸ item.tree⟩
      | cons second rest =>
          simp [sourceProofStackImage] at himageSingleton

/-- Source-owned proof-occurrence derivations and source-derived operational
Metamath provability define the same proof language on frame-respecting source
formulas. -/
theorem sourceGeneratedProvesTree_nonempty_iff_sourceOperationalProvable
    (source : SourcePrefix) (target : ValidatedCalculusLanguageDef)
    (hsource : calculusLanguageDefOfSourcePrefix? source = some target.1)
    (formula : ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame
        (floatingVariableNames source.activeHypotheses) formula = true) :
    Nonempty (SourceGeneratedProvesTree source target formula) ↔
      Metamath.Spec.Provable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        (operationalExpr formula) := by
  constructor
  · rintro ⟨tree⟩
    exact sourceTree_to_sourceOperationalProvable hsource tree
      (fun _ => ⟨⟨""⟩, []⟩)
  · intro hprovable
    have htree :=
      sourceOperationalProvable_to_sourceTree source target hsource hprovable
    rw [reifyOperationalExpr_operationalExpr_of_respectsFrame
      (floatingVariableNames source.activeHypotheses) formula hrespect] at htree
    exact htree

/-! ## Executable boundaries -/

private def exampleAssertion : SourceAssertion :=
  { label := "ax-ph"
    formula := ⟨"wff", [.var "ph"]⟩
    frame :=
      { distinctVariables := []
        hypothesisLabels := ["wph"] }
    hypotheses := [.floating "wph" "wff" "ph"] }

private def exampleAssertionPrefix : SourcePrefix :=
  { declaredConstants := ["wff"]
    declaredVariables := ["ph"]
    callerFrame :=
      { distinctVariables := []
        hypothesisLabels := ["wph"] }
    activeHypotheses := [.floating "wph" "wff" "ph"]
    assertions := [exampleAssertion] }

/-- Positive: a source assertion is materialized as its operational entry. -/
example :
    sourceOperationalDatabase exampleAssertionPrefix "ax-ph" =
      some (sourceAssertionOperationalPayload exampleAssertion) := by
  rfl

/-- Negative: a label absent from the authored prefix has no operational
entry. -/
example :
    sourceOperationalDatabase exampleAssertionPrefix "missing" = none := by
  rfl

end Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
