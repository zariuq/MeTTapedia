import Mettapedia.Languages.Metamath.InferenceProjectionFidelity
import Mettapedia.Languages.Metamath.InferenceVariableClassification

/-!
# Runtime variable classification of projected Metamath frames

Successful hypothesis projection retains enough information to recover the
live verifier's floating-variable classification in the original frame order.
This module connects that fact to the projection and runtime formula-symbol
gates.  It makes no claim about `checkHyp` or proof-step adequacy.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceVariableClassification

/-- The per-label classifier used inside the live `DB.frameFloatVars` fold. -/
private def runtimeFloatingVariable? (db : RuntimeDB) (label : String) :
    Option String :=
  match db.find? label with
  | some (.hyp false formula _) =>
      if formula.isFloatShape then
        match formula[1]! with
        | .var variableName => some variableName
        | .const _ => none
      else
        none
  | _ => none

private theorem frameFloatVars_eq_filterMap
    (db : RuntimeDB) (frame : RuntimeFrame) :
    db.frameFloatVars frame =
      frame.hyps.toList.filterMap (runtimeFloatingVariable? db) := by
  unfold Metamath.Verify.DB.frameFloatVars
  congr 1
  funext label
  unfold runtimeFloatingVariable?
  cases hfind : db.find? label with
  | none => rfl
  | some object =>
      cases object with
      | const name => rfl
      | var name => rfl
      | assert formula assertionFrame storedLabel => rfl
      | hyp essential formula storedLabel =>
          cases essential with
          | true => rfl
          | false =>
              dsimp
              split
              · cases formula[1]! <;> rfl
              · rfl

/-- A successfully projected hypothesis has exactly the same floating-name
classification as the live database object at that label. -/
private theorem runtimeFloatingVariable?_eq_of_projectHypothesis
    (db : RuntimeDB) (label : String) (hypothesis : HypothesisView)
    (hproject : projectHypothesis? db label = some hypothesis) :
    runtimeFloatingVariable? db label = hypothesis.floatingVariable? := by
  obtain ⟨runtimeFormula, hfind, hdecode, hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hproject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  cases hypothesis with
  | floating viewLabel typecode variableName =>
      simp only [hypothesisEssentialBit, HypothesisView.formula] at hfind hruntime
      subst runtimeFormula
      simp [runtimeFloatingVariable?, hfind,
        HypothesisView.floatingVariable?, ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Formula.isFloatShape]
  | essential viewLabel formula =>
      simp only [hypothesisEssentialBit] at hfind
      simp [runtimeFloatingVariable?, hfind, HypothesisView.floatingVariable?]

private theorem filterMap_runtimeFloatingVariable?_eq_of_forall₂
    (db : RuntimeDB) {labels : List String}
    {hypotheses : List HypothesisView}
    (hordered : List.Forall₂
      (fun label hypothesis =>
        projectHypothesis? db label = some hypothesis)
      labels hypotheses) :
    labels.filterMap (runtimeFloatingVariable? db) =
      floatingVariableNames hypotheses := by
  induction hordered with
  | nil => rfl
  | cons hhead _htail ih =>
      simp only [List.filterMap_cons, floatingVariableNames] at ih ⊢
      rw [runtimeFloatingVariable?_eq_of_projectHypothesis _ _ _ hhead, ih]

/-- Successful list projection preserves the live floating-variable names
exactly and in source-frame order. -/
theorem frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses) :
    db.frameFloatVars frame = floatingVariableNames hypotheses := by
  rw [frameFloatVars_eq_filterMap]
  exact filterMap_runtimeFloatingVariable?_eq_of_forall₂ db
    (projectHypotheses?_forall₂
      db frame.hyps.toList hypotheses hproject)

/-! ## Exact formula-symbol gates -/

/-- Once a hypothesis list is projected from the same live frame, the
projection and runtime formula-symbol gates are the same Boolean. -/
theorem formulaSymbolsRespectFrame_eq_runtime_of_projectHypotheses
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (formula : ConstantHeadedFormula) :
    formulaSymbolsRespectFrame (floatingVariableNames hypotheses) formula =
      db.formulaSymsRespectFrame formula.toRuntime frame := by
  rw [← frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
    db frame hypotheses hproject]
  exact formulaSymbolsRespectFrame_eq_runtime db frame formula

/-- The assertion formula's revalidated projection gate is exactly the live
runtime gate on the same assertion frame. -/
theorem assertionFormula_runtimeGate_of_viewValid
    (db : RuntimeDB) (assertion : AssertionView)
    (declaredConstants declaredVariables : List String)
    (hproject :
      projectHypotheses? db assertion.frame.hyps.toList =
        some assertion.hypotheses)
    (hvalid :
      assertionViewValid declaredConstants declaredVariables assertion = true) :
    db.formulaSymsRespectFrame assertion.formula.toRuntime assertion.frame =
      true := by
  have hprojectionGate :
      formulaSymbolsRespectFrame
          (floatingVariableNames assertion.hypotheses) assertion.formula =
        true := by
    simp only [assertionViewValid, Bool.and_eq_true] at hvalid
    exact hvalid.1.1.2
  rw [← formulaSymbolsRespectFrame_eq_runtime_of_projectHypotheses
    db assertion.frame assertion.hypotheses hproject assertion.formula]
  exact hprojectionGate

/-- Every projected mandatory-hypothesis formula passing the frame-view gate
passes the exact live runtime gate on that frame. -/
theorem projectedHypothesisFormula_runtimeGate_of_frameValid
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hvalid : frameProjectionValid frame hypotheses = true)
    (hypothesis : HypothesisView) (hmember : hypothesis ∈ hypotheses) :
    db.formulaSymsRespectFrame hypothesis.formula.toRuntime frame = true := by
  have hall :
      hypotheses.all
          (formulaSymbolsRespectFrame (floatingVariableNames hypotheses) ∘
            HypothesisView.formula) =
        true := by
    simp only [frameProjectionValid, Bool.and_eq_true] at hvalid
    exact hvalid.1.2
  have hprojectionGate :=
    List.all_eq_true.mp hall hypothesis hmember
  change formulaSymbolsRespectFrame
      (floatingVariableNames hypotheses) hypothesis.formula = true at hprojectionGate
  rw [← formulaSymbolsRespectFrame_eq_runtime_of_projectHypotheses
    db frame hypotheses hproject hypothesis.formula]
  exact hprojectionGate

/-! ## Positive and negative boundaries -/

/-- Any claimed projected floating-name order differing from the live frame
classification is impossible. -/
theorem projectHypotheses?_ne_of_floatingVariableNames_ne
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hne :
      db.frameFloatVars frame ≠ floatingVariableNames hypotheses) :
    projectHypotheses? db frame.hyps.toList ≠ some hypotheses := by
  intro hproject
  exact hne
    (frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
      db frame hypotheses hproject)

private def classificationFloatXView : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

private def classificationEssentialView : ConstantHeadedFormula :=
  ⟨"|-", [.var "x"]⟩

private def classificationFloatYView : ConstantHeadedFormula :=
  ⟨"wff", [.var "y"]⟩

private def classificationFloatX : RuntimeFormula :=
  classificationFloatXView.toRuntime

private def classificationEssential : RuntimeFormula :=
  classificationEssentialView.toRuntime

private def classificationFloatY : RuntimeFormula :=
  classificationFloatYView.toRuntime

private def classificationFrame : RuntimeFrame :=
  ⟨#[], #["wx", "ess", "wy"]⟩

private def classificationDB : RuntimeDB :=
  let objects :=
    (default : RuntimeDB).objects
      |>.insert "wx" (.hyp false classificationFloatX "wx")
      |>.insert "ess" (.hyp true classificationEssential "ess")
      |>.insert "wy" (.hyp false classificationFloatY "wy")
  { (default : RuntimeDB) with
    frame := classificationFrame
    objects := objects }

private def classificationViews : List HypothesisView :=
  [ .floating "wx" "wff" "x"
  , .essential "ess" ⟨"|-", [.var "x"]⟩
  , .floating "wy" "wff" "y" ]

private theorem classificationDB_find_wx :
    classificationDB.find? "wx" =
      some (.hyp false classificationFloatX "wx") := by
  unfold classificationDB Metamath.Verify.DB.find?
  rw [KernelExtras.HashMap.find?_insert_ne _ (by decide)]
  rw [KernelExtras.HashMap.find?_insert_ne _ (by decide)]
  exact KernelExtras.HashMap.find?_insert_self _ _ _

private theorem classificationDB_find_ess :
    classificationDB.find? "ess" =
      some (.hyp true classificationEssential "ess") := by
  unfold classificationDB Metamath.Verify.DB.find?
  rw [KernelExtras.HashMap.find?_insert_ne _ (by decide)]
  exact KernelExtras.HashMap.find?_insert_self _ _ _

private theorem classificationDB_find_wy :
    classificationDB.find? "wy" =
      some (.hyp false classificationFloatY "wy") := by
  unfold classificationDB Metamath.Verify.DB.find?
  exact KernelExtras.HashMap.find?_insert_self _ _ _

private theorem classificationDB_project_wx :
    projectHypothesis? classificationDB "wx" =
      some (.floating "wx" "wff" "x") := by
  simp [projectHypothesis?, classificationDB_find_wx, classificationFloatX,
    classificationFloatXView]
  exact ⟨(), rfl⟩

private theorem classificationDB_project_ess :
    projectHypothesis? classificationDB "ess" =
      some (.essential "ess" classificationEssentialView) := by
  simp [projectHypothesis?, classificationDB_find_ess,
    classificationEssential, classificationEssentialView]
  exact ⟨(), rfl⟩

private theorem classificationDB_project_wy :
    projectHypothesis? classificationDB "wy" =
      some (.floating "wy" "wff" "y") := by
  simp [projectHypothesis?, classificationDB_find_wy, classificationFloatY,
    classificationFloatYView]
  exact ⟨(), rfl⟩

/-- Positive boundary: essential hypotheses are skipped while the two floating
variables retain their source-frame order. -/
theorem classificationDB_preserves_floating_order :
    projectHypotheses? classificationDB
        classificationDB.frame.hyps.toList = some classificationViews ∧
      classificationDB.frameFloatVars classificationDB.frame = ["x", "y"] ∧
      floatingVariableNames classificationViews = ["x", "y"] := by
  have hproject :
      projectHypotheses? classificationDB ["wx", "ess", "wy"] =
        some classificationViews := by
    simp [projectHypotheses?, classificationViews,
      classificationDB_project_wx, classificationDB_project_ess,
      classificationDB_project_wy, classificationEssentialView]
  have hprojectFrame :
      projectHypotheses? classificationDB
          classificationDB.frame.hyps.toList =
        some classificationViews := by
    simpa [classificationDB, classificationFrame] using hproject
  refine ⟨hprojectFrame, ?_, rfl⟩
  exact frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
    classificationDB classificationDB.frame classificationViews hprojectFrame

/-- Negative boundary: the same live frame cannot project to a view claiming
the reverse floating-variable order. -/
theorem classificationDB_reversed_floating_order_rejected :
    projectHypotheses? classificationDB
        classificationDB.frame.hyps.toList ≠
      some
        [ .floating "wy" "wff" "y"
        , .essential "ess" ⟨"|-", [.var "x"]⟩
        , .floating "wx" "wff" "x" ] := by
  apply projectHypotheses?_ne_of_floatingVariableNames_ne
  change classificationDB.frameFloatVars classificationDB.frame ≠ ["y", "x"]
  rw [classificationDB_preserves_floating_order.2.1]
  decide

end Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
