import Mettapedia.Languages.Metamath.InferenceAssertionProjectionInvariants
import Mettapedia.Languages.Metamath.InferenceCheckHypGraph
import Mettapedia.Languages.Metamath.InferenceFormulaLookupAgreement
import Mettapedia.Languages.Metamath.InferenceProjectionFidelity
import Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
import Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
import Mathlib.Data.List.Forall2

/-!
# Forward bridge from projected assertion semantics to `DB.checkHyp`

This module proves that the independent ordered hypothesis-instance and
essential-matching semantics of a successfully projected assertion construct
the exact successful graph of the live Metamath hypothesis checker.  The live
substitution is the verifier's source-order insertion fold; it is related to
the visible finite substitution extensionally, rather than by structural
`HashMap` equality.
-/

namespace Mettapedia.Languages.Metamath.InferenceCheckHypForward

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
open Mettapedia.Languages.Metamath.InferenceFormulaLookupAgreement
open Mettapedia.Languages.Metamath.InferenceCheckHypGraph
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation

/-! ## Pointwise consequences of the independent relations -/

private def HypothesisInstanceAt (substitution : FiniteSubstitution)
    (hypothesis : HypothesisView) (actual : ConstantHeadedFormula) : Prop :=
  match hypothesis with
  | .floating _ typecode variableName =>
      actual.typecode = typecode ∧
        LookupSemantics substitution variableName actual
  | .essential _ formula => actual.typecode = formula.typecode

private theorem HypothesisInstanceAt.cons_binding
    {substitution : FiniteSubstitution} {hypothesis : HypothesisView}
    {actual : ConstantHeadedFormula} (binding : FormulaBinding)
    (hinstance : HypothesisInstanceAt substitution hypothesis actual) :
    HypothesisInstanceAt (binding :: substitution) hypothesis actual := by
  cases hypothesis with
  | floating label typecode variableName =>
      exact ⟨hinstance.1, List.mem_cons_of_mem binding hinstance.2⟩
  | essential label formula => exact hinstance

private theorem HypothesisInstanceAt.forall₂_cons_binding
    (binding : FormulaBinding) :
    ∀ {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution},
      List.Forall₂ (HypothesisInstanceAt substitution)
          hypotheses actuals →
        List.Forall₂ (HypothesisInstanceAt (binding :: substitution))
          hypotheses actuals
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, _, .cons hinstance tail =>
      .cons (hinstance.cons_binding binding)
        (HypothesisInstanceAt.forall₂_cons_binding binding tail)

private theorem hypothesisInstances_forall₂_instanceAt
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution) :
    List.Forall₂ (HypothesisInstanceAt substitution) hypotheses actuals := by
  induction instances with
  | nil => exact .nil
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      apply List.Forall₂.cons
      · exact ⟨typecode_eq, by simp [LookupSemantics]⟩
      · exact HypothesisInstanceAt.forall₂_cons_binding
          ⟨variableName, actual⟩ ih
  | essential typecode_eq tail ih =>
      exact .cons typecode_eq ih

private def EssentialInstanceAt (substitution : FiniteSubstitution)
    (hypothesis : HypothesisView) (actual : ConstantHeadedFormula) : Prop :=
  match hypothesis with
  | .floating _ _ _ => True
  | .essential _ formula =>
      FormulaSubstitutionSemantics substitution formula actual

private theorem essentialMatches_forall₂
    (substitution : FiniteSubstitution) :
    ∀ {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula},
      EssentialMatches substitution hypotheses actuals →
        List.Forall₂ (EssentialInstanceAt substitution)
          hypotheses actuals
  | [], [], _ => .nil
  | .floating _ _ _ :: hypotheses, _ :: actuals, hmatches =>
      .cons trivial
        (essentialMatches_forall₂ substitution
          (by simpa [EssentialMatches] using hmatches))
  | .essential _ _ :: hypotheses, _ :: actuals, hmatches =>
      .cons hmatches.1
        (essentialMatches_forall₂ substitution hmatches.2)

private theorem hypothesisInstances_binding_origin
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    {name : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics substitution name replacement) :
    ∃ (index : Nat)
        (hhypothesis : index < hypotheses.length)
        (hactual : index < actuals.length)
        (label typecode : String),
      hypotheses.get ⟨index, hhypothesis⟩ =
          .floating label typecode name ∧
        actuals.get ⟨index, hactual⟩ = replacement := by
  induction instances with
  | nil => simp [LookupSemantics] at hlookup
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      change ({ variableName := name, replacement } : FormulaBinding) ∈
        { variableName := variableName, replacement := actual } :: substitution
        at hlookup
      rcases List.mem_cons.mp hlookup with hhead | htail
      · have hname : name = variableName :=
          congrArg FormulaBinding.variableName hhead
        have hreplacement : replacement = actual :=
          congrArg FormulaBinding.replacement hhead
        subst name
        subst replacement
        exact ⟨0, by simp, by simp, label, typecode, rfl, rfl⟩
      · obtain ⟨index, hhypothesis, hactual, sourceLabel,
          sourceTypecode, hview, hvalue⟩ := ih htail
        exact ⟨index + 1, by simp [hhypothesis], by simp [hactual],
          sourceLabel, sourceTypecode, by simpa using hview,
          by simpa using hvalue⟩
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      obtain ⟨index, hhypothesis, hactual, sourceLabel,
          sourceTypecode, hview, hvalue⟩ := ih hlookup
      exact ⟨index + 1, by simp [hhypothesis], by simp [hactual],
        sourceLabel, sourceTypecode, by simpa using hview,
        by simpa using hvalue⟩

/-! ## Prefix scope and exact stack-window access -/

private theorem earlier_floating_of_hypothesesPrefixScopedFrom
    {available : List String} {hypotheses : List HypothesisView}
    (hscope : hypothesesPrefixScopedFrom available hypotheses = true)
    {index : Nat} (hindex : index < hypotheses.length)
    {label : String} {formula : ConstantHeadedFormula}
    (hget : hypotheses.get ⟨index, hindex⟩ = .essential label formula)
    {name : String} (hname : .var name ∈ formula.body) :
    name ∈ available ∨
      ∃ (earlier : Nat)
          (_ : earlier < index)
          (hearlierBound : earlier < hypotheses.length)
          (sourceLabel typecode : String),
        hypotheses.get ⟨earlier, hearlierBound⟩ =
          .floating sourceLabel typecode name := by
  induction hypotheses generalizing available index with
  | nil => simp at hindex
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | floating sourceLabel typecode variableName =>
          cases index with
          | zero => simp at hget
          | succ index =>
              have hindexTail : index < hypotheses.length := by
                simpa using hindex
              have htailScope :
                  hypothesesPrefixScopedFrom (variableName :: available)
                      hypotheses = true := by
                simpa [hypothesesPrefixScopedFrom] using hscope
              have htailGet :
                  hypotheses.get ⟨index, hindexTail⟩ =
                    .essential label formula := by
                simpa using hget
              rcases ih htailScope hindexTail htailGet with
                havailable | ⟨earlier, hearlier, hearlierBound,
                  earlierLabel, earlierTypecode, hearlierView⟩
              · rcases List.mem_cons.mp havailable with hcurrent | havailable
                · right
                  subst name
                  exact ⟨0, by omega, by simp, sourceLabel, typecode, rfl⟩
                · exact Or.inl havailable
              · right
                exact ⟨earlier + 1, by omega, by simp [hearlierBound],
                  earlierLabel, earlierTypecode, by simpa using hearlierView⟩
      | essential sourceLabel sourceFormula =>
          simp only [hypothesesPrefixScopedFrom, Bool.and_eq_true] at hscope
          cases index with
          | zero =>
              cases hget
              have hknown :=
                List.all_eq_true.mp hscope.1 (.var name) hname
              left
              exact List.contains_iff_mem.mp (by simpa using hknown)
          | succ index =>
              have hindexTail : index < hypotheses.length := by
                simpa using hindex
              have htailGet :
                  hypotheses.get ⟨index, hindexTail⟩ =
                    .essential label formula := by
                simpa using hget
              rcases ih hscope.2 hindexTail htailGet with
                havailable | ⟨earlier, hearlier, hearlierBound,
                  earlierLabel, earlierTypecode, hearlierView⟩
              · exact Or.inl havailable
              · right
                exact ⟨earlier + 1, by omega, by simp [hearlierBound],
                  earlierLabel, earlierTypecode, by simpa using hearlierView⟩

private theorem stack_get_of_exact_window
    (stack : Array RuntimeFormula)
    (off : Nat)
    (actuals : List ConstantHeadedFormula)
    (hwindow :
      stack.extract off stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    {index : Nat} (hindex : index < actuals.length) :
    stack[off + index]! =
      (actuals.get ⟨index, hindex⟩).toRuntime := by
  have hwindowIndex :=
    congrArg (fun formulas : Array RuntimeFormula => formulas[index]!) hwindow
  have hbound : index < stack.size - off := by
    have hsize : stack.size - off = actuals.length := by
      simpa using congrArg Array.size hwindow
    omega
  rw [Metamath.Kernel.getElem!_extract_lt stack off stack.size index
      hbound (Nat.le_refl _)] at hwindowIndex
  simpa [hindex] using hwindowIndex

/-! ## Facts retained by successful live projection -/

private theorem runtime_fidelity_of_projectHypothesis
    (db : RuntimeDB) (label : String) (hypothesis : HypothesisView)
    (hproject : projectHypothesis? db label = some hypothesis) :
    db.find? label = some (.hyp (hypothesisEssentialBit hypothesis)
      hypothesis.formula.toRuntime label) := by
  obtain ⟨runtimeFormula, hfind, hdecode, _hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hproject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  simpa [hruntime] using hfind

private theorem projected_hypothesis_at
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    {index : Nat} (hindex : index < frame.hyps.size)
    (hhypothesis : index < hypotheses.length) :
    projectHypothesis? db frame.hyps[index]! =
      some (hypotheses.get ⟨index, hhypothesis⟩) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hpoint := hordered.get (by simpa using hindex) hhypothesis
  simpa [hindex] using hpoint

private theorem wellFormed_of_projectPrefix
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    db.wellFormed? = true := by
  unfold projectPrefix? at hproject
  simp only [bind, Option.bind_eq_some_iff] at hproject
  obtain ⟨_guardError, _herror, _guardWellFormed, hwellFormed,
    _guardDV, _hdv, _guardEmbedded, _hembedded, _guardDeclarations,
    _hdeclarations, activeHypotheses, _hactive, _guardFrame, _hframe,
    assertions, _hassertions, _guardProjection, _hprojectionValid,
    hprojection⟩ := hproject
  cases hprojection
  unfold guard at hwellFormed
  split at hwellFormed
  · assumption
  · simp at hwellFormed

private theorem assertionViewValid_of_projectPrefix
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

private theorem frameProjectionValid_of_projectedAssertion
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    frameProjectionValid assertion.frame assertion.hypotheses = true := by
  have hvalid := assertionViewValid_of_projectPrefix
    db projection assertion hproject hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1

private theorem hypothesesPrefixScoped_of_projectedAssertion
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    hypothesesPrefixScopedFrom [] assertion.hypotheses = true := by
  have hvalid := frameProjectionValid_of_projectedAssertion
    db projection assertion hproject hmember
  simp only [frameProjectionValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1.2

private theorem wellFormedAssertionFrame_of_projectPrefix
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    Metamath.WF.WellFormedFrame db assertion.frame := by
  have hdatabase := Metamath.WF.wellFormedDB_of_wellFormed?
    (wellFormed_of_projectPrefix db projection hproject)
  have hfind :=
    (projectedAssertion_database_fidelity
      db projection assertion hproject hmember).1
  exact (hdatabase.2 assertion.label
    (.assert assertion.formula.toRuntime assertion.frame assertion.label)
    hfind).2

/-! ## Extensional identification of the live completed substitution -/

private theorem runtimeCorrespondence_sigmaFromHypsPrefix
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + frame.hyps.size = stack.size})
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hinstances : HypothesisInstances hypotheses actuals substitution)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hwellFormed :
      Metamath.WF.WellFormedFrame db
        (Metamath.Verify.Frame.mk #[] frame.hyps)) :
    RuntimeSubstitutionCorrespondence substitution
      (Metamath.Kernel.sigmaFromHypsPrefix
        db frame.hyps stack off frame.hyps.size) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hhypothesesLength : hypotheses.length = frame.hyps.size := by
    simpa using hordered.length_eq.symm
  have hactualsLength : actuals.length = frame.hyps.size := by
    rw [← hinstances.lengths]
    exact hhypothesesLength
  have hpointInstances := hypothesisInstances_forall₂_instanceAt hinstances
  have hprefix := Metamath.Kernel.sigmaFromHypsPrefix_prefix
    db frame.hyps stack off hwellFormed frame.hyps.size (Nat.le_refl _)
  have hcovers := Metamath.Kernel.sigmaFromHypsPrefix_covers
    db frame.hyps stack off hwellFormed frame.hyps.size (Nat.le_refl _)
  intro name runtimeFormula
  constructor
  · intro hlookup
    obtain ⟨index, hindex, runtimeSource, sourceLabel, hfind,
        _hsize, hkey, hvalue⟩ :=
      hprefix name runtimeFormula hlookup
    have hhypothesis : index < hypotheses.length := by omega
    have hactual : index < actuals.length := by omega
    let hypothesis := hypotheses.get ⟨index, hhypothesis⟩
    have hprojectAt :
        projectHypothesis? db frame.hyps[index]! = some hypothesis :=
      projected_hypothesis_at db frame hypotheses hproject
        hindex hhypothesis
    have hfindAt := runtime_fidelity_of_projectHypothesis
      db frame.hyps[index]! hypothesis hprojectAt
    have hobjects :
        some (Metamath.Verify.Object.hyp false runtimeSource sourceLabel) =
          some (Metamath.Verify.Object.hyp
            (hypothesisEssentialBit hypothesis)
            hypothesis.formula.toRuntime frame.hyps[index]!) := by
      rw [← hfind, ← hfindAt]
    have hinstance := hpointInstances.get hhypothesis hactual
    change HypothesisInstanceAt substitution hypothesis
      (actuals.get ⟨index, hactual⟩) at hinstance
    have hstack := stack_get_of_exact_window
      stack off.1 actuals hwindow hactual
    cases hview : hypothesis with
    | essential label formula =>
        simp [hview, hypothesisEssentialBit] at hobjects
    | floating label typecode variableName =>
        simp only [hview, hypothesisEssentialBit, HypothesisView.formula]
          at hobjects hinstance
        injection hobjects with hobject
        injection hobject with hformula hlabel
        subst runtimeSource
        subst sourceLabel
        have hname : variableName = name := by
          simpa [ConstantHeadedFormula.toRuntime] using hkey
        subst variableName
        refine ⟨actuals.get ⟨index, hactual⟩, ?_, ?_⟩
        · exact hinstance.2
        · exact hvalue.trans hstack
  · rintro ⟨replacement, hlookup, rfl⟩
    obtain ⟨index, hhypothesis, hactual, sourceLabel, typecode,
        hview, hreplacement⟩ :=
      hypothesisInstances_binding_origin hinstances hlookup
    have hindex : index < frame.hyps.size := by omega
    have hprojectAt := projected_hypothesis_at
      db frame hypotheses hproject hindex hhypothesis
    rw [hview] at hprojectAt
    have hfindAt := runtime_fidelity_of_projectHypothesis
      db frame.hyps[index]!
        (.floating sourceLabel typecode name) hprojectAt
    have hfind :
        db.find? frame.hyps[index]! =
          some (.hyp false
            (ConstantHeadedFormula.mk typecode [.var name]).toRuntime
            frame.hyps[index]!) := by
      simpa [hypothesisEssentialBit, HypothesisView.formula] using hfindAt
    have hshape :
        (ConstantHeadedFormula.mk typecode [.var name]).toRuntime.isFloatShape =
          true := by
      simp [ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Formula.isFloatShape]
    have hcovered := hcovers index hindex
      (ConstantHeadedFormula.mk typecode [.var name]).toRuntime
      frame.hyps[index]! hfind hshape
    have hstack := stack_get_of_exact_window
      stack off.1 actuals hwindow hactual
    have hcovered' :
        (Metamath.Kernel.sigmaFromHypsPrefix
          db frame.hyps stack off frame.hyps.size)[name]? =
            some (stack[off.1 + index]!) := by
      simpa [ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Sym.value] using hcovered
    rw [hstack, hreplacement] at hcovered'
    exact hcovered'

private theorem formulaSymsRespectFrame_hypsOnly
    (db : RuntimeDB) (formula : RuntimeFormula) (frame : RuntimeFrame) :
    db.formulaSymsRespectFrame formula
        (Metamath.Verify.Frame.mk #[] frame.hyps) =
      db.formulaSymsRespectFrame formula frame := by
  cases frame
  rfl

/-! ## Construction of the exact successful checker graph -/

private theorem checkHypOK_sigmaFromHypsPrefix
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + frame.hyps.size = stack.size})
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hframeValid : frameProjectionValid frame hypotheses = true)
    (hscope : hypothesesPrefixScopedFrom [] hypotheses = true)
    (hinstances : HypothesisInstances hypotheses actuals substitution)
    (hessential : EssentialMatches substitution hypotheses actuals)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hwellFormed :
      Metamath.WF.WellFormedFrame db
        (Metamath.Verify.Frame.mk #[] frame.hyps)) :
    Metamath.Kernel.CheckHypOK db frame.hyps stack off 0 ∅
      (Metamath.Kernel.sigmaFromHypsPrefix
        db frame.hyps stack off frame.hyps.size) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hhypothesesLength : hypotheses.length = frame.hyps.size := by
    simpa using hordered.length_eq.symm
  have hactualsLength : actuals.length = frame.hyps.size := by
    rw [← hinstances.lengths]
    exact hhypothesesLength
  have hpointInstances := hypothesisInstances_forall₂_instanceAt hinstances
  have hpointEssential := essentialMatches_forall₂ substitution hessential
  have hunique : SubstitutionKeysUnique substitution :=
    hinstances.substitutionKeysUnique
      (floatingVariableNames_nodup_of_frameProjectionValid
        frame hypotheses hframeValid)
  have loop : ∀ (index : Nat), index ≤ frame.hyps.size →
      Metamath.Kernel.CheckHypOK db frame.hyps stack off index
        (Metamath.Kernel.sigmaFromHypsPrefix
          db frame.hyps stack off index)
        (Metamath.Kernel.sigmaFromHypsPrefix
          db frame.hyps stack off frame.hyps.size) := by
    intro index hindexLe
    generalize hfuel : frame.hyps.size - index = fuel
    induction fuel generalizing index with
    | zero =>
        have hindexEq : index = frame.hyps.size := by omega
        subst index
        unfold Metamath.Kernel.CheckHypOK
        simp
    | succ fuel ih =>
        have hindex : index < frame.hyps.size := by omega
        have hhypothesis : index < hypotheses.length := by omega
        have hactual : index < actuals.length := by omega
        let hypothesis := hypotheses.get ⟨index, hhypothesis⟩
        let actual := actuals.get ⟨index, hactual⟩
        have hprojectAt :
            projectHypothesis? db frame.hyps[index]! = some hypothesis :=
          projected_hypothesis_at db frame hypotheses hproject
            hindex hhypothesis
        have hfindAt := runtime_fidelity_of_projectHypothesis
          db frame.hyps[index]! hypothesis hprojectAt
        have hinstance := hpointInstances.get hhypothesis hactual
        change HypothesisInstanceAt substitution hypothesis actual at hinstance
        have hessentialAt := hpointEssential.get hhypothesis hactual
        change EssentialInstanceAt substitution hypothesis actual at hessentialAt
        have hstack : stack[off.1 + index]! = actual.toRuntime := by
          exact stack_get_of_exact_window
            stack off.1 actuals hwindow hactual
        have hstackHead : stack[off.1 + index]!.hasConstHead = true := by
          rw [hstack]
          exact ConstantHeadedFormula.hasConstHead_toRuntime actual
        have hmember : hypothesis ∈ hypotheses := by
          exact List.get_mem hypotheses ⟨index, hhypothesis⟩
        have hsymbolsAt :=
          projectedHypothesisFormula_runtimeGate_of_frameValid
            db frame hypotheses hproject hframeValid hypothesis hmember
        have hnextBase := ih (index + 1) (by omega) (by omega)
        cases hview : hypothesis with
        | floating sourceLabel typecode variableName =>
            simp only [hview, HypothesisInstanceAt] at hinstance
            have hfind :
                db.find? frame.hyps[index]! =
                  some (.hyp false
                    (ConstantHeadedFormula.mk typecode
                      [.var variableName]).toRuntime
                    frame.hyps[index]!) := by
              simpa [hview, hypothesisEssentialBit, HypothesisView.formula]
                using hfindAt
            have htypecode : actual.typecode = typecode := by
              simpa [hview, HypothesisInstanceAt] using hinstance.1
            have hshape :
                (ConstantHeadedFormula.mk typecode
                    [.var variableName]).toRuntime.isFloatShape = true := by
              simp [ConstantHeadedFormula.toRuntime,
                Metamath.Verify.Formula.isFloatShape]
            have hheadEq :
                (((ConstantHeadedFormula.mk typecode
                    [.var variableName]).toRuntime)[0]! ==
                  stack[off.1 + index]![0]!) = true := by
              rw [hstack]
              simp [ConstantHeadedFormula.toRuntime, htypecode]
            have hheadEq' :
                ((ConstantHeadedFormula.mk typecode
                    [.var variableName]).toRuntime)[0]! =
                  stack[off.1 + index]![0]! :=
              LawfulBEq.eq_of_beq hheadEq
            have hprefix := Metamath.Kernel.sigmaFromHypsPrefix_prefix
              db frame.hyps stack off hwellFormed index hindexLe
            have hduplicate :
                ¬ variableName ∈
                  Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index := by
              classical
              intro hmem
              cases hlookup :
                  (Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index)[variableName]? with
              | none =>
                  have hisSome :=
                    (Std.HashMap.mem_iff_isSome_getElem?).1 hmem
                  rw [hlookup] at hisSome
                  exact (Bool.false_ne_true hisSome).elim
              | some value =>
                  obtain ⟨earlier, hearlier, earlierFormula, earlierLabel,
                      hearlierFind, hearlierSize, hearlierKey, _hearlierValue⟩ :=
                    hprefix variableName value hlookup
                  have hearlierBound : earlier < frame.hyps.size := by omega
                  have hcurrentFind :
                      db.find? frame.hyps[index] =
                        some (.hyp false
                          (ConstantHeadedFormula.mk typecode
                            [.var variableName]).toRuntime
                          frame.hyps[index]) := by
                    simpa [hindex] using hfind
                  have hearlierFind' :
                      db.find? frame.hyps[earlier] =
                        some (.hyp false earlierFormula earlierLabel) := by
                    simpa [hearlierBound] using hearlierFind
                  have hcurrentSize :
                      (ConstantHeadedFormula.mk typecode
                        [.var variableName]).toRuntime.size ≥ 2 := by
                    simp [ConstantHeadedFormula.toRuntime]
                  have hdistinct := hwellFormed.2 index earlier
                    hindex hearlierBound (Nat.ne_of_lt hearlier).symm
                    (ConstantHeadedFormula.mk typecode
                      [.var variableName]).toRuntime
                    earlierFormula frame.hyps[index] earlierLabel
                    hcurrentFind hearlierFind' hcurrentSize hearlierSize
                  have hcurrentKey :
                      (match (ConstantHeadedFormula.mk typecode
                          [.var variableName]).toRuntime[1]! with
                        | .var name => name
                        | .const _ => "") = variableName := by
                    simp [ConstantHeadedFormula.toRuntime]
                  exact hdistinct (hcurrentKey.trans hearlierKey.symm)
            have hsigmaSucc :
                Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off (index + 1) =
                  (Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index).insert variableName
                      (stack[off.1 + index]!) := by
              simp [Metamath.Kernel.sigmaFromHypsPrefix_succ,
                hfind, ConstantHeadedFormula.toRuntime,
                Metamath.Verify.Sym.value]
            have hnext :
                Metamath.Kernel.CheckHypOK db frame.hyps stack off
                  (index + 1)
                  ((Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index).insert variableName
                      (stack[off.1 + index]!))
                  (Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off frame.hyps.size) := by
              simpa [hsigmaSucc] using hnextBase
            have hfindSafe :
                db.find? frame.hyps[index] =
                  some (.hyp false
                    (ConstantHeadedFormula.mk typecode
                      [.var variableName]).toRuntime
                    frame.hyps[index]) := by
              simpa [hindex] using hfind
            unfold Metamath.Kernel.CheckHypOK
            simp [hindex, hfindSafe]
            exact ⟨hstackHead, hshape, hheadEq', hduplicate, hnext⟩
        | essential sourceLabel sourceFormula =>
            simp only [hview, HypothesisInstanceAt, EssentialInstanceAt]
              at hinstance hessentialAt
            have hfind :
                db.find? frame.hyps[index]! =
                  some (.hyp true sourceFormula.toRuntime
                    frame.hyps[index]!) := by
              simpa [hview, hypothesisEssentialBit, HypothesisView.formula]
                using hfindAt
            have htypecode : actual.typecode = sourceFormula.typecode := by
              simpa [hview, HypothesisInstanceAt] using hinstance
            have hsemantics :
                FormulaSubstitutionSemantics substitution
                  sourceFormula actual := by
              simpa [hview, EssentialInstanceAt] using hessentialAt
            have hformulaHead : sourceFormula.toRuntime.hasConstHead = true :=
              ConstantHeadedFormula.hasConstHead_toRuntime sourceFormula
            have hsymbols :
                db.formulaSymsRespectFrame sourceFormula.toRuntime
                    (Metamath.Verify.Frame.mk #[] frame.hyps) = true := by
              rw [formulaSymsRespectFrame_hypsOnly]
              simpa [hview, HypothesisView.formula] using hsymbolsAt
            have hheadEq :
                (sourceFormula.toRuntime[0]! ==
                  stack[off.1 + index]![0]!) = true := by
              rw [hstack]
              simp [ConstantHeadedFormula.toRuntime, htypecode]
            have hheadEq' : sourceFormula.toRuntime[0]! =
                stack[off.1 + index]![0]! :=
              LawfulBEq.eq_of_beq hheadEq
            have hcanonical :
                sourceFormula.toRuntime.subst
                    (RuntimeSubstitutionMap substitution) =
                  .ok actual.toRuntime :=
              runtime_subst_of_formulaSubstitutionSemantics
                hunique hsemantics
            have hcurrentCovers :=
              Metamath.Kernel.sigmaFromHypsPrefix_covers
                db frame.hyps stack off hwellFormed index hindexLe
            have hviewAt :
                hypotheses.get ⟨index, hhypothesis⟩ =
                  .essential sourceLabel sourceFormula := by
              simpa [hypothesis] using hview
            have hlocal :
                sourceFormula.toRuntime.subst
                    (Metamath.Kernel.sigmaFromHypsPrefix
                      db frame.hyps stack off index) =
                  sourceFormula.toRuntime.subst
                    (RuntimeSubstitutionMap substitution) := by
              apply formula_subst_eq_of_body_lookup_agreement
              intro name hname
              rcases earlier_floating_of_hypothesesPrefixScopedFrom
                  hscope hhypothesis hviewAt hname with
                hempty | ⟨earlier, hearlier, hearlierBound,
                  earlierLabel, earlierTypecode, hearlierView⟩
              · simp at hempty
              · have hearlierFrame : earlier < frame.hyps.size := by omega
                have hearlierActual : earlier < actuals.length := by omega
                have hearlierProject := projected_hypothesis_at
                  db frame hypotheses hproject hearlierFrame hearlierBound
                rw [hearlierView] at hearlierProject
                have hearlierFind := runtime_fidelity_of_projectHypothesis
                  db frame.hyps[earlier]!
                    (.floating earlierLabel earlierTypecode name)
                    hearlierProject
                have hearlierFind' :
                    db.find? frame.hyps[earlier]! =
                      some (.hyp false
                        (ConstantHeadedFormula.mk earlierTypecode
                          [.var name]).toRuntime frame.hyps[earlier]!) := by
                  simpa [hypothesisEssentialBit, HypothesisView.formula]
                    using hearlierFind
                have hearlierShape :
                    (ConstantHeadedFormula.mk earlierTypecode
                      [.var name]).toRuntime.isFloatShape = true := by
                  simp [ConstantHeadedFormula.toRuntime,
                    Metamath.Verify.Formula.isFloatShape]
                have hlive := hcurrentCovers earlier hearlier
                  (ConstantHeadedFormula.mk earlierTypecode
                    [.var name]).toRuntime frame.hyps[earlier]!
                  hearlierFind' hearlierShape
                have hearlierInstance :=
                  hpointInstances.get hearlierBound hearlierActual
                simp only [hearlierView, HypothesisInstanceAt]
                  at hearlierInstance
                have hcanonicalLookup :=
                  runtimeSubstitutionMap_lookup_of_semantics
                    hunique hearlierInstance.2
                have hearlierStack := stack_get_of_exact_window
                  stack off.1 actuals hwindow hearlierActual
                calc
                  (Metamath.Kernel.sigmaFromHypsPrefix
                      db frame.hyps stack off index)[name]? =
                      some (stack[off.1 + earlier]!) := by
                        simpa [ConstantHeadedFormula.toRuntime,
                          Metamath.Verify.Sym.value] using hlive
                  _ = some (actuals.get ⟨earlier, hearlierActual⟩).toRuntime :=
                        congrArg some hearlierStack
                  _ = (RuntimeSubstitutionMap substitution)[name]? :=
                        hcanonicalLookup.symm
            have hsubstitution :
                sourceFormula.toRuntime.subst
                    (Metamath.Kernel.sigmaFromHypsPrefix
                      db frame.hyps stack off index) =
                  .ok (stack[off.1 + index]!) := by
              rw [hlocal, hcanonical, hstack]
            have hsigmaSucc :
                Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off (index + 1) =
                  Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index := by
              simp [Metamath.Kernel.sigmaFromHypsPrefix_succ, hfind]
            have hnext :
                Metamath.Kernel.CheckHypOK db frame.hyps stack off
                  (index + 1)
                  (Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off index)
                  (Metamath.Kernel.sigmaFromHypsPrefix
                    db frame.hyps stack off frame.hyps.size) := by
              simpa [hsigmaSucc] using hnextBase
            have hfindSafe :
                db.find? frame.hyps[index] =
                  some (.hyp true sourceFormula.toRuntime
                    frame.hyps[index]) := by
              simpa [hindex] using hfind
            unfold Metamath.Kernel.CheckHypOK
            simp [hindex, hfindSafe]
            exact ⟨hstackHead, hsymbols, hheadEq',
              hsubstitution, hnext⟩
  simpa [Metamath.Kernel.sigmaFromHypsPrefix] using loop 0 (Nat.zero_le _)

/-! ## Public forward bridge -/

/-- Successful projection and the independent ordered hypothesis semantics
entail success of the live verifier's actual hypothesis checker.  The returned
map is the verifier's own source-order fold and corresponds extensionally to
the visible finite substitution. -/
theorem checkHyp_ok_of_projectedAssertion
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat //
      offset + assertion.frame.hyps.size = stack.size})
    (actuals : List ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hinstances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hessential :
      EssentialMatches substitution assertion.hypotheses actuals)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray) :
    let runtimeSubstitution :=
      Metamath.Kernel.sigmaFromHypsPrefix
        db assertion.frame.hyps stack off assertion.frame.hyps.size
    db.checkHyp assertion.frame.hyps stack off 0 ∅ =
        .ok runtimeSubstitution ∧
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution := by
  dsimp only
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hhypotheses := hfidelity.2.1
  have hframeValid := frameProjectionValid_of_projectedAssertion
    db projection assertion hproject hmember
  have hscope := hypothesesPrefixScoped_of_projectedAssertion
    db projection assertion hproject hmember
  have hwellFormed := wellFormedAssertionFrame_of_projectPrefix
    db projection assertion hproject hmember
  have hwellFormedHyps := Metamath.Kernel.wellFormedFrame_hyps_only
    db assertion.frame hwellFormed
  have hgraph := checkHypOK_sigmaFromHypsPrefix
    db assertion.frame assertion.hypotheses actuals substitution stack off
    hhypotheses hframeValid hscope hinstances hessential hwindow
    hwellFormedHyps
  have hsuccess :=
    (checkHypOK_iff_checkHyp_ok db assertion.frame.hyps stack off 0 ∅
      (Metamath.Kernel.sigmaFromHypsPrefix
        db assertion.frame.hyps stack off assertion.frame.hyps.size)).1 hgraph
  have hcorrespondence := runtimeCorrespondence_sigmaFromHypsPrefix
    db assertion.frame assertion.hypotheses actuals substitution stack off
    hhypotheses hinstances hwindow hwellFormedHyps
  exact ⟨hsuccess, hcorrespondence⟩

end Mettapedia.Languages.Metamath.InferenceCheckHypForward
