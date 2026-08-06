import Mettapedia.Languages.Metamath.InferenceCheckHypForward
import Mettapedia.Languages.Metamath.InferenceDVRuntimeBridge
import Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph

/-!
# Forward agreement for one projected Metamath assertion step

This module composes the independent assertion-application semantics with the
live verifier's assertion-step graph.  The stack boundary remains explicit:
the mandatory actuals must be the exact consumed suffix, and the current stack
must satisfy the verifier's caller-frame symbol invariant.  No successful
`checkHyp`, `dvCheck`, or runtime substitution is assumed.

The generated-node corollary still concerns only one local assertion node.
Its leading `Proves` derivations and the proof-execution invariant supplying
the live stack window remain separate recursive-proof obligations.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionStepForward

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
open Mettapedia.Languages.Metamath.InferenceCheckHypForward
open Mettapedia.Languages.Metamath.InferenceDVRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceVariableClassification

/-! ## Stack-window and projection consequences -/

/-- Every visible substitution replacement constructed by ordered mandatory
hypothesis instantiation is one of the corresponding actual formulas. -/
theorem hypothesisInstances_lookup_replacement_mem_actuals
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    {name : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics substitution name replacement) :
    replacement ∈ actuals := by
  induction instances with
  | nil => simp [LookupSemantics] at hlookup
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      change ({ variableName := name, replacement } : FormulaBinding) ∈
        { variableName := variableName, replacement := actual } :: substitution
        at hlookup
      rcases List.mem_cons.mp hlookup with hhead | htail
      · have hreplacement : replacement = actual :=
          congrArg FormulaBinding.replacement hhead
        subst replacement
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem actual (ih htail)
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      exact List.mem_cons_of_mem actual (ih hlookup)

/-- Pointwise access to a list of actual formulas represented by an exact
runtime stack suffix. -/
theorem stack_get_of_exact_actual_window
    (stack : Array RuntimeFormula) (offset : Nat)
    (actuals : List ConstantHeadedFormula)
    (hwindow :
      stack.extract offset stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    {index : Nat} (hindex : index < actuals.length) :
    stack[offset + index]! =
      (actuals.get ⟨index, hindex⟩).toRuntime := by
  have hwindowIndex :=
    congrArg (fun formulas : Array RuntimeFormula => formulas[index]!) hwindow
  have hbound : index < stack.size - offset := by
    have hsize : stack.size - offset = actuals.length := by
      simpa using congrArg Array.size hwindow
    omega
  rw [Metamath.Kernel.getElem!_extract_lt stack offset stack.size index
      hbound (Nat.le_refl _)] at hwindowIndex
  simpa [hindex] using hwindowIndex

/-- The frame-respect invariant normally carried by a reachable proof stack
transfers through an exact suffix window to every visible actual formula,
using the runtime's own active-variable classification. -/
theorem actuals_respect_callerFrame_of_stack_window
    (db : RuntimeDB) (stack : Array RuntimeFormula) (offset : Nat)
    (actuals : List ConstantHeadedFormula)
    (hwindow :
      stack.extract offset stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstack : Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    ∀ actual ∈ actuals,
      formulaSymbolsRespectFrame (db.frameFloatVars db.frame) actual = true := by
  intro actual hactual
  obtain ⟨⟨index, hindex⟩, hget⟩ := List.mem_iff_get.mp hactual
  have hsize : stack.size - offset = actuals.length := by
    simpa using congrArg Array.size hwindow
  have hstackIndex : offset + index < stack.size := by omega
  have hruntime := hstack (offset + index) hstackIndex
  have hstackGet := stack_get_of_exact_actual_window
    stack offset actuals hwindow hindex
  rw [hstackGet, hget] at hruntime
  rw [formulaSymbolsRespectFrame_eq_runtime]
  exact hruntime

/-- Revalidation of a retained assertion is available as an ordinary
proposition to downstream runtime bridges. -/
theorem projectedAssertion_viewValid
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    assertionViewValid projection.declaredConstants
      projection.declaredVariables assertion = true := by
  have hvalid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  exact List.all_eq_true.mp hvalid.1.2 assertion hmember

/-- The caller frame retained by a successful projection has strictly
canonical DV-pair orientation, as required by the exact runtime DV bridge. -/
theorem projectedCallerFrame_dvStrict
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    projection.callerFrame.dj.toList.all
      (fun pair => decide (pair.1 < pair.2)) = true := by
  have hvalid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  have hframe :
      frameProjectionValid projection.callerFrame
        projection.activeHypotheses = true := hvalid.1.1.1.2
  simp only [frameProjectionValid, Bool.and_eq_true] at hframe
  have hdv := hframe.2
  simp only [frameDVValid] at hdv
  apply List.all_eq_true.mpr
  intro pair hpair
  have hpairValid := List.all_eq_true.mp hdv pair hpair
  simp only [Bool.and_eq_true] at hpairValid
  exact hpairValid.1.1

/-! ## Representation boundaries -/

private def boundaryActualX : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

private def boundaryActualY : ConstantHeadedFormula :=
  ⟨"wff", [.var "y"]⟩

private theorem boundaryInstances :
    HypothesisInstances
      [.floating "wx" "wff" "x"] [boundaryActualX]
      [⟨"x", boundaryActualX⟩] :=
  .floating rfl .nil

/-- Positive boundary: a visible floating binding originates in the ordered
actual-formula list. -/
example : boundaryActualX ∈ [boundaryActualX] := by
  exact hypothesisInstances_lookup_replacement_mem_actuals boundaryInstances
    (name := "x") (replacement := boundaryActualX)
      (by simp [LookupSemantics])

/-- Negative boundary: changing the replacement does not create a visible
binding with the same variable name. -/
example :
    ¬ LookupSemantics [⟨"x", boundaryActualX⟩] "x" boundaryActualY := by
  simp [LookupSemantics, boundaryActualX, boundaryActualY]

/-! ## Exact forward composition -/

/-- Independent assertion application, an exact mandatory stack suffix, and
the proof-execution frame invariant construct the full live assertion-step
graph.  Runtime checker success is a conclusion, never a premise. -/
theorem assertionApplicationSemantics_to_stepGraph
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result)
    (hstackEnough : assertion.frame.hyps.size ≤ pr.stack.size)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    AssertionLabelStepGraph db pr assertion.label
      { pr with
        stack :=
          (pr.stack.shrink
            (pr.stack.size - assertion.frame.hyps.size)).push
              result.toRuntime } := by
  rcases hsemantics with
    ⟨substitution, hinstances, hessential, hdvSemantics, hresultSemantics⟩
  let offset := pr.stack.size - assertion.frame.hyps.size
  have hoffset : offset + assertion.frame.hyps.size = pr.stack.size :=
    Nat.sub_add_cancel hstackEnough
  let off : { offset : Nat //
      offset + assertion.frame.hyps.size = pr.stack.size } :=
    ⟨offset, hoffset⟩
  have hwindow' :
      pr.stack.extract off.1 pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    simpa [off, offset] using hwindow
  obtain ⟨hcheckHyp, hcorrespondence⟩ :=
    checkHyp_ok_of_projectedAssertion db projection assertion pr.stack off
      actuals substitution hproject hmember hinstances hessential hwindow'
  have hunique : SubstitutionKeysUnique substitution :=
    hinstances.substitutionKeysUnique_of_projectedAssertion
      db projection hproject hmember
  have hactualsRespect :=
    actuals_respect_callerFrame_of_stack_window
      db pr.stack off.1 actuals hwindow' hstackRespects
  have hreplacementsRespect :
      ∀ name replacement,
        LookupSemantics substitution name replacement →
          formulaSymbolsRespectFrame
            (db.frameFloatVars db.frame) replacement = true := by
    intro name replacement hlookup
    exact hactualsRespect replacement
      (hypothesisInstances_lookup_replacement_mem_actuals hinstances hlookup)
  have hcallerFrame :
      projection.callerFrame = proofFacingCallerFrame db :=
    (projectPrefix?_eq_some_fields db projection hproject).2.2.1
  have hdvSemanticsFiltered :
      DVOKSemantics substitution (proofFacingCallerFrame db)
        assertion.frame := by
    simpa [hcallerFrame] using hdvSemantics
  have hdvSemantics' :
      DVOKSemantics substitution db.frame assertion.frame :=
    hdvSemanticsFiltered.caller_mono
      (proofFacingCallerFrame_dj_subset db)
  have hcallerDV :
      db.frame.dj.toList.all
        (fun pair => decide (pair.1 < pair.2)) = true := by
    exact rawCallerDVStrict_of_projectPrefix?_eq_some db projection hproject
  have hdvCheck :
      Metamath.Verify.DB.dvCheck (db.frameFloatVars db.frame)
          db.frame.dj assertion.frame.dj
          (Metamath.Kernel.sigmaFromHypsPrefix db assertion.frame.hyps
            pr.stack off assertion.frame.hyps.size) = .ok () :=
    (dvOKSemantics_iff_dvCheck_of_correspondence
      hcorrespondence hcallerDV hreplacementsRespect).mp hdvSemantics'
  have hformulaSubst :
      assertion.formula.toRuntime.subst
          (Metamath.Kernel.sigmaFromHypsPrefix db assertion.frame.hyps
            pr.stack off assertion.frame.hyps.size) =
        .ok result.toRuntime :=
    (formulaSubstitutionSemantics_iff_runtime_subst_of_correspondence
      hunique hcorrespondence assertion.formula result).mp hresultSemantics
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hassertionValid := projectedAssertion_viewValid
    db projection assertion hproject hmember
  have hassertionSymbols :
      db.formulaSymsRespectFrame assertion.formula.toRuntime
        assertion.frame = true :=
    assertionFormula_runtimeGate_of_viewValid db assertion
      projection.declaredConstants projection.declaredVariables
      hfidelity.2.1 hassertionValid
  refine ⟨⟨
    assertion.formula.toRuntime,
    assertion.frame,
    assertion.label,
    hfidelity.1,
    hstackEnough,
    ConstantHeadedFormula.hasConstHead_toRuntime assertion.formula,
    hassertionSymbols,
    off.1,
    off.2,
    ?_,
    pr.stack.shrink off.1,
    rfl,
    pr.stack.extract off.1 pr.stack.size,
    rfl,
    ?_,
    Metamath.Kernel.sigmaFromHypsPrefix db assertion.frame.hyps
      pr.stack off assertion.frame.hyps.size,
    hcheckHyp,
    db.frameFloatVars db.frame,
    rfl,
    hdvCheck,
    result.toRuntime,
    hformulaSubst,
    ?_
  ⟩⟩
  · simp [off, offset]
  · rw [hwindow']
    simp only [List.size_toArray, List.length_map]
    have hlabels := congrArg List.length hfidelity.2.2.1
    simp only [List.length_map, Array.length_toList] at hlabels
    have hlengths := hinstances.lengths
    omega
  · simp [off, offset]

/-- The previous graph theorem immediately yields success of the executable
`stepNormal` assertion branch with the same complete proof-state update. -/
theorem assertionApplicationSemantics_to_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result)
    (hstackEnough : assertion.frame.hyps.size ≤ pr.stack.size)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    db.stepNormal pr assertion.label = .ok
      { pr with
        stack :=
          (pr.stack.shrink
            (pr.stack.size - assertion.frame.hyps.size)).push
              result.toRuntime } := by
  rcases assertionApplicationSemantics_to_stepGraph
      db projection assertion pr actuals result hproject hmember hsemantics
      hstackEnough hwindow hstackRespects with ⟨witness⟩
  exact witness.stepNormal_ok

/-- A proof-relevant generated assertion node has the same forward runtime
consequence once the independent stack-window obligations are supplied. -/
theorem generatedAssertionNode_to_stepGraph
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hnode : Nonempty
      (Σ substitution : FiniteSubstitution,
        GeneratedAssertionNode projection target assertion actuals result
          substitution))
    (hstackEnough : assertion.frame.hyps.size ≤ pr.stack.size)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    AssertionLabelStepGraph db pr assertion.label
      { pr with
        stack :=
          (pr.stack.shrink
            (pr.stack.size - assertion.frame.hyps.size)).push
              result.toRuntime } := by
  have hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result :=
    (generatedAssertionNode_nonempty_iff_semantics projection target
      hprojection hmember actuals result).mp hnode
  exact assertionApplicationSemantics_to_stepGraph
    db projection assertion pr actuals result hproject hmember hsemantics
      hstackEnough hwindow hstackRespects

end Mettapedia.Languages.Metamath.InferenceAssertionStepForward
