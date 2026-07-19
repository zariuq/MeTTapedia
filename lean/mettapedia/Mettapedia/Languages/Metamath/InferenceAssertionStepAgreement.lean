import Mettapedia.Languages.Metamath.InferenceAssertionStepForward
import Mettapedia.Languages.Metamath.InferenceCheckHypReverse

/-!
# Exact agreement for one projected Metamath assertion step

This module closes the local bidirectional bridge between independent
assertion-application semantics, a proof-relevant generated assertion node,
and the live verifier's assertion branch.  The consumed mandatory hypotheses
remain an exact stack suffix, and caller-frame symbol respect remains an
explicit proof-execution invariant.

The generated-node statements concern one local rule node.  They do not
manufacture the leading `Proves` derivations or a runtime proof history that
establishes the stack premises.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceAssertionStepForward
open Mettapedia.Languages.Metamath.InferenceCheckHypReverse
open Mettapedia.Languages.Metamath.InferenceDVRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

/-! ## Capacity recovered from semantics and the exact window -/

/-- Independent ordered instances and an exact canonical stack suffix already
exclude runtime stack underflow.  Capacity is therefore a theorem at the
agreement boundary, not an additional premise. -/
theorem stackEnough_of_assertionApplicationSemantics_window
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
        (actuals.map ConstantHeadedFormula.toRuntime).toArray) :
    assertion.frame.hyps.size ≤ stack.size := by
  rcases hsemantics with
    ⟨substitution, hinstances, _hessential, _hdv, _hresult⟩
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hlabelLengths := congrArg List.length hfidelity.2.2.1
  simp only [List.length_map, Array.length_toList] at hlabelLengths
  by_contra hunderflow
  have hstackLt : stack.size < assertion.frame.hyps.size := by omega
  have hoffsetZero : stack.size - assertion.frame.hyps.size = 0 := by
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt hstackLt)
  have hwindowSizes := congrArg Array.size hwindow
  simp [hoffsetZero] at hwindowSizes
  have hinstanceLengths := hinstances.lengths
  omega

/-! ## Reflection from the live graph -/

/-- A successful live assertion graph with the exact canonical result state
reflects the independent assertion-application semantics.  In particular, the
declared result is recovered from equality of complete proof states rather
than supplied as a formula-substitution premise. -/
theorem stepGraph_to_assertionApplicationSemantics
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack)
    (hgraph :
      AssertionLabelStepGraph db pr assertion.label
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime }) :
    AssertionApplicationSemantics projection.callerFrame assertion
      actuals result := by
  rcases hgraph with ⟨⟨
    runtimeFormula,
    runtimeFrame,
    embeddedLabel,
    hlookup,
    hwitnessStackEnough,
    _hruntimeHead,
    _hruntimeSymbols,
    runtimeOffset,
    hruntimeOffset,
    hruntimeCanonical,
    stackPrefix,
    hstackPrefix,
    runtimeWindow,
    _hruntimeWindow,
    _hruntimeWindowSize,
    runtimeSubstitution,
    hcheckHyp,
    callerVariables,
    hcallerVariables,
    hdvCheck,
    conclusion,
    hformulaSubst,
    hresultState
  ⟩⟩
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hobjects :
      some (Metamath.Verify.Object.assert
        runtimeFormula runtimeFrame embeddedLabel) =
        some (Metamath.Verify.Object.assert
          assertion.formula.toRuntime assertion.frame
          assertion.label) := by
    rw [← hlookup, ← hfidelity.1]
  injection hobjects with hobject
  injection hobject with hformula hframe hembedded
  subst runtimeFormula
  subst runtimeFrame
  subst embeddedLabel
  let offset := pr.stack.size - assertion.frame.hyps.size
  have hoffset : offset + assertion.frame.hyps.size = pr.stack.size :=
    Nat.sub_add_cancel hwitnessStackEnough
  let off : { offset : Nat //
      offset + assertion.frame.hyps.size = pr.stack.size } :=
    ⟨offset, hoffset⟩
  have hruntimeOffsetEq : runtimeOffset = offset := by
    simpa [offset] using hruntimeCanonical
  subst runtimeOffset
  have hcheckHyp' :
      db.checkHyp assertion.frame.hyps pr.stack off 0 ∅ =
        .ok runtimeSubstitution := by
    simpa [off, offset] using hcheckHyp
  have hwindow' :
      pr.stack.extract off.1 pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    simpa [off, offset] using hwindow
  have hreverse := projectedAssertion_instances_of_checkHyp_ok
    db projection assertion pr.stack off actuals runtimeSubstitution
      hproject hmember hwindow' hcheckHyp'
  let substitution := canonicalSubstitution assertion.hypotheses actuals
  have hinstances :
      HypothesisInstances assertion.hypotheses actuals substitution := by
    simpa [substitution] using hreverse.1
  have hessential :
      EssentialMatches substitution assertion.hypotheses actuals := by
    simpa [substitution] using hreverse.2.1
  have hcorrespondence :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution := by
    simpa [substitution] using hreverse.2.2
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
    intro name replacement hreplacement
    exact hactualsRespect replacement
      (hypothesisInstances_lookup_replacement_mem_actuals
        hinstances hreplacement)
  have hcallerFrame : projection.callerFrame = db.frame :=
    (projectPrefix?_eq_some_fields db projection hproject).2.2.1
  have hcallerDV :
      db.frame.dj.toList.all
        (fun pair => decide (pair.1 < pair.2)) = true := by
    simpa [hcallerFrame] using
      projectedCallerFrame_dvStrict db projection hproject
  have hdvCheck' :
      Metamath.Verify.DB.dvCheck (db.frameFloatVars db.frame)
          db.frame.dj assertion.frame.dj runtimeSubstitution = .ok () := by
    simpa [hcallerVariables] using hdvCheck
  have hdvSemantics :
      DVOKSemantics substitution db.frame assertion.frame :=
    (dvOKSemantics_iff_dvCheck_of_correspondence
      hcorrespondence hcallerDV hreplacementsRespect).mpr hdvCheck'
  have hprefixCanonical :
      stackPrefix = pr.stack.shrink offset := by
    simpa [offset] using hstackPrefix
  have hstateStacks :
      (pr.stack.shrink offset).push result.toRuntime =
        stackPrefix.push conclusion := by
    simpa [offset] using
      congrArg (fun state : RuntimeProofState => state.stack) hresultState
  rw [hprefixCanonical] at hstateStacks
  have hconclusion :=
    congrArg
      (fun formulas : Array RuntimeFormula =>
        formulas[(pr.stack.shrink offset).size]!) hstateStacks
  have hconclusionEq : conclusion = result.toRuntime := by
    simpa only [Metamath.Kernel.Array.getElem!_push_eq] using
      hconclusion.symm
  have hformulaSubst' :
      assertion.formula.toRuntime.subst runtimeSubstitution =
        .ok result.toRuntime := by
    simpa [hconclusionEq] using hformulaSubst
  have hresultSemantics :
      FormulaSubstitutionSemantics substitution assertion.formula result :=
    (formulaSubstitutionSemantics_iff_runtime_subst_of_correspondence
      hunique hcorrespondence assertion.formula result).mpr hformulaSubst'
  refine ⟨substitution, hinstances, hessential, ?_, hresultSemantics⟩
  simpa [hcallerFrame] using hdvSemantics

/-! ## Exact local equivalences -/

/-- Independent assertion semantics is exactly the live assertion-step graph
at the canonical complete proof-state result. -/
theorem assertionApplicationSemantics_iff_stepGraph
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    AssertionApplicationSemantics projection.callerFrame assertion
        actuals result ↔
      AssertionLabelStepGraph db pr assertion.label
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime } := by
  constructor
  · intro hsemantics
    have hstackEnough :=
      stackEnough_of_assertionApplicationSemantics_window
        db projection assertion pr.stack actuals result hproject hmember
          hsemantics hwindow
    exact assertionApplicationSemantics_to_stepGraph
      db projection assertion pr actuals result hproject hmember hsemantics
        hstackEnough hwindow hstackRespects
  · exact stepGraph_to_assertionApplicationSemantics
      db projection assertion pr actuals result hproject hmember
        hwindow hstackRespects

/-- The same independent semantics is exactly successful execution of the
live `stepNormal` assertion branch. -/
theorem assertionApplicationSemantics_iff_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    AssertionApplicationSemantics projection.callerFrame assertion
        actuals result ↔
      db.stepNormal pr assertion.label = .ok
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime } := by
  rw [assertionApplicationSemantics_iff_stepGraph
    db projection assertion pr actuals result hproject hmember
      hwindow hstackRespects]
  exact assertionLabelStepGraph_iff_stepNormal_ok_of_lookup
    db pr _ assertion.label assertion.formula.toRuntime assertion.frame
      assertion.label
      (projectedAssertion_database_fidelity
        db projection assertion hproject hmember).1

/-- A proof-relevant generated local assertion node exists exactly when the
live assertion-step graph has the canonical result.  Leading `Proves`
derivations remain outside this local-node equivalence. -/
theorem generatedAssertionNode_nonempty_iff_stepGraph
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    Nonempty
        (Σ substitution : FiniteSubstitution,
          GeneratedAssertionNode projection target assertion actuals result
            substitution) ↔
      AssertionLabelStepGraph db pr assertion.label
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime } := by
  rw [generatedAssertionNode_nonempty_iff_semantics projection target
    hprojection hmember actuals result]
  exact assertionApplicationSemantics_iff_stepGraph
    db projection assertion pr actuals result hproject hmember
      hwindow hstackRespects

/-- Strongest local endpoint: generated native-type evidence exists exactly
when the live verifier accepts the corresponding assertion label and produces
the canonical complete proof-state result. -/
theorem generatedAssertionNode_nonempty_iff_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    Nonempty
        (Σ substitution : FiniteSubstitution,
          GeneratedAssertionNode projection target assertion actuals result
            substitution) ↔
      db.stepNormal pr assertion.label = .ok
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime } := by
  rw [generatedAssertionNode_nonempty_iff_semantics projection target
    hprojection hmember actuals result]
  exact assertionApplicationSemantics_iff_stepNormal
    db projection assertion pr actuals result hproject hmember
      hwindow hstackRespects

end Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
