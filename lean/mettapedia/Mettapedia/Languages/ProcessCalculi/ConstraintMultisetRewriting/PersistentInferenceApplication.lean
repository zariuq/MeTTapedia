import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceRealization

/-! # Exact replay of an admitted source rule at physical premise positions -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

theorem origin_instance {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (instance_ : InferenceChecker.RuleInstance)
    (source : firing.source = .inl instance_.ruleId)
    (inputs : firing.inputs = .inl instance_.arguments) : origin.instance_ = instance_ := by
  have ruleEq := Sum.inl.inj (origin.source_eq.symm.trans source)
  have argumentsEq := Sum.inl.inj (origin.inputs_eq.symm.trans inputs)
  exact congrArg₂ InferenceChecker.RuleInstance.mk ruleEq argumentsEq

theorem origin_judgments {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication definition origin.instance_ premises conclusion) :
    origin.premises = premises ∧ origin.conclusion = conclusion := by
  have computed := instantiateRule?_eq_some_iff_application.mpr application
  have same := Option.some.inj (origin.instantiated.symm.trans computed)
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem picks_prescribed_positions {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (prior : Board before) (selection : ContextMap prior.judgments origin.premises)
    (reads : firing.picked.read = selectedReads prior selection) :
    origin.picked prior = selection.interpret definition := by
  rw [← origin.premiseMap_interpret]
  apply congrArg (ContextMap.interpret definition)
  apply ContextMap.ext
  funext port
  have physical : origin.readOccurrence port =
      prior.occurrenceAt (prior.entryIndex (selection.position port)) := by
    simp only [SelectedFiring.KernelOrigin.readOccurrence, reads, selectedReads,
      List.get_eq_getElem, List.getElem_ofFn]
  have position := prior.occurrenceAt_injective
    ((origin.position_reads_actual_occurrence prior port).trans physical)
  change prior.premiseIndex (origin.readPosition prior port) = selection.position port
  rw [position, prior.premise_entry]

noncomputable def outputSelection {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (prior : Board before) : ContextMap (origin.board prior).judgments [origin.conclusion] :=
  (ContextMap.right prior.judgments [origin.conclusion]).transport
    (origin.board_judgments prior).symm rfl

theorem outputSelection_interpret {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (prior : Board before) :
    (outputSelection origin prior).interpret definition =
      eqToHom (origin.board_context prior) ≫
        ClassifyingContext.sndProjection (prior.context definition) ⟨[origin.conclusion]⟩ := by
  dsimp only [Board.context]
  rw [outputSelection, ContextMap.interpret_transport, ContextMap.interpret_right]
  simp only [eqToHom_refl]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

/-- Executing the admitted application reads the prescribed positions and
replays exactly the original primitive proof node. The physical execution
still contains the client post and server request consumption. -/
theorem application_realizes (definition : ValidatedCalculusLanguageDef)
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (application : RuleApplication definition instance_ premises conclusion)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (prior : Board before) (selection : ContextMap prior.judgments premises) :
    ∃ execution : Execution (definition := definition) before prior [conclusion],
      execution.actors = [false, true] ∧
      execution.observe = .cons (.byRule instance_ application (selection.interpret definition)) .nil := by
  classical
  obtain ⟨middle, after, client, server, source, inputs, reads, _kept, _output⟩ :=
    InferenceSelectedApplication.application_runs_with_reads definition application before background
      (selectedReads prior selection) (selectedReads_present prior selection)
      (selectedReads_labels prior selection)
  let origin := Classical.choice server.kernel_origin
  have instanceEq : origin.instance_ = instance_ := origin_instance origin instance_ source inputs
  subst instance_
  obtain ⟨premisesEq, conclusionEq⟩ := origin_judgments origin application
  subst premises
  subst conclusion
  let middleBoard := (projectFiring client prior).1
  let trace : SelectedRun definition before [false, true] after :=
    .cons client (.cons server (.nil after))
  let outputs : ContextMap (trace.project prior).1.judgments [origin.conclusion] :=
    outputSelection origin middleBoard
  let execution : Execution (definition := definition) before prior [origin.conclusion] :=
    ⟨after, [false, true], trace, (trace.project prior).1, outputs⟩
  refine ⟨execution, rfl, ?_⟩
  have selected : origin.picked middleBoard = selection.interpret definition :=
    picks_prescribed_positions origin middleBoard selection reads
  have published := origin.publishes_actual_rule middleBoard
  rw [selected] at published
  have reconstructed : origin.arrow middleBoard ≫ outputs.interpret definition =
      .cons (.byRule origin.instance_ application (selection.interpret definition)) .nil :=
    (congrArg (fun selectedOutput => origin.arrow middleBoard ≫ selectedOutput)
      (outputSelection_interpret origin middleBoard)).trans published
  change ((trace.project prior).2 ≫
    InferencePathFunctor.changeBoard (trace.project prior).1 (trace.project prior).1) ≫
      outputs.interpret definition = _
  rw [InferencePathFunctor.changeBoard_self]
  have cleanTerminal := Category.comp_id (trace.project prior).2
  apply (congrArg (fun arrow => arrow ≫ outputs.interpret definition) cleanTerminal).trans
  change (𝟙 (prior.context definition) ≫ (origin.arrow middleBoard ≫ 𝟙 _)) ≫
    outputs.interpret definition = _
  have clean : 𝟙 (middleBoard.context definition) ≫ (origin.arrow middleBoard ≫ 𝟙 _) =
      origin.arrow middleBoard := (Category.id_comp _).trans (Category.comp_id _)
  exact (congrArg (fun arrow => arrow ≫ outputs.interpret definition) clean).trans reconstructed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
