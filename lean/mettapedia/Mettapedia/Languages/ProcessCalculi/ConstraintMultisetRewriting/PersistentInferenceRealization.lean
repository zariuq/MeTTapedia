import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctor
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication

/-!
# Persistent theorem outputs of actual inference traces

Every selected trace preserves its earlier protected premise positions.
The structural retraction below is computed from the actual client/server
origins: a client changes only request data, while a server appends one
protected conclusion. This is a projection of the existing physical run,
not a replacement transition relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

noncomputable def kernelRetraction {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (prior : Board before) : ContextMap (origin.board prior).judgments prior.judgments :=
  (ContextMap.left prior.judgments [origin.conclusion]).transport
    (origin.board_judgments prior).symm rfl

theorem kernelRetraction_interpret {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (prior : Board before) :
    (kernelRetraction origin prior).interpret definition =
      eqToHom (origin.board_context prior) ≫
        ClassifyingContext.fstProjection (prior.context definition) ⟨[origin.conclusion]⟩ := by
  dsimp only [Board.context]
  rw [kernelRetraction, ContextMap.interpret_transport, ContextMap.interpret_left]
  simp only [eqToHom_refl]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

noncomputable def firingRetraction {before after : Configuration Value Occurrence} {actor : Bool}
    (firing : SelectedFiring definition actor before after) (prior : Board before) :
    ContextMap (projectFiring firing prior).1.judgments prior.judgments := by
  cases actor with
  | false => exact ContextMap.id prior.judgments
  | true => exact kernelRetraction (Classical.choice firing.kernel_origin) prior

theorem firing_keeps_positions {before after : Configuration Value Occurrence} {actor : Bool}
    (firing : SelectedFiring definition actor before after) (prior : Board before) :
    (projectFiring firing prior).2 ≫ (firingRetraction firing prior).interpret definition =
      𝟙 (prior.context definition) := by
  cases actor with
  | false => exact Category.id_comp _
  | true =>
      change (Classical.choice firing.kernel_origin).arrow prior ≫
        (kernelRetraction (Classical.choice firing.kernel_origin) prior).interpret definition = _
      rw [kernelRetraction_interpret]
      exact (Classical.choice firing.kernel_origin).keeps_old_positions prior

private theorem paste_retractions {C : Type*} [Category* C] {a b c : C}
    (first : a ⟶ b) (second : b ⟶ c) (backFirst : b ⟶ a) (backSecond : c ⟶ b)
    (left : first ≫ backFirst = 𝟙 a) (right : second ≫ backSecond = 𝟙 b) :
    (first ≫ second) ≫ (backSecond ≫ backFirst) = 𝟙 a := by
  rw [Category.assoc, ← Category.assoc second, right, Category.id_comp, left]

noncomputable def retraction : {before after : Configuration Value Occurrence} →
    {actors : List Bool} → (trace : SelectedRun definition before actors after) →
    (prior : Board before) → ContextMap (trace.project prior).1.judgments prior.judgments
  | _, _, _, .nil _, prior => ContextMap.id prior.judgments
  | _, _, _, .cons firing rest, prior =>
      (retraction rest (projectFiring firing prior).1).comp (firingRetraction firing prior)

theorem trace_keeps_positions {before after : Configuration Value Occurrence} {actors : List Bool}
    (trace : SelectedRun definition before actors after) (prior : Board before) :
    (trace.project prior).2 ≫ (retraction trace prior).interpret definition =
      𝟙 (prior.context definition) := by
  induction trace with
  | nil => exact Category.id_comp _
  | cons firing rest earlier =>
      simp only [SelectedRun.project, retraction, ContextMap.interpret_comp]
      exact paste_retractions _ _ _ _ (firing_keeps_positions firing prior) (earlier _)

/-- A structural output selection may repeat a theorem occurrence. It does
not manufacture derivations or forget which premise position was selected. -/
structure Execution (before : Configuration Value Occurrence) (prior : Board before)
    (goals : List Pattern) where
  after : Configuration Value Occurrence
  actors : List Bool
  trace : SelectedRun definition before actors after
  board : Board after
  outputs : ContextMap board.judgments goals

noncomputable def Execution.observe {before : Configuration Value Occurrence} {prior : Board before}
    {goals : List Pattern} (execution : Execution (definition := definition) before prior goals) :
    OpenDerivationList definition prior.judgments goals :=
  InferencePathFunctor.toBoard execution.trace prior execution.board ≫
    execution.outputs.interpret definition

theorem Execution.ordinary {before : Configuration Value Occurrence} {prior : Board before}
    {goals : List Pattern} (execution : Execution (definition := definition) before prior goals) :
    (system definition).Run payload before execution.actors execution.after :=
  execution.trace.ordinary

def identityExecution {before : Configuration Value Occurrence} (prior : Board before)
    {goals : List Pattern} (outputs : ContextMap prior.judgments goals) :
    Execution (definition := definition) before prior goals :=
  ⟨before, [], .nil before, prior, outputs⟩

theorem identityExecution_observe {before : Configuration Value Occurrence} (prior : Board before)
    {goals : List Pattern} (outputs : ContextMap prior.judgments goals) :
    (identityExecution (definition := definition) prior outputs).observe = outputs.interpret definition := by
  change InferencePathFunctor.toBoard (.nil before) prior prior ≫ outputs.interpret definition = _
  rw [InferencePathFunctor.toBoard_nil, InferencePathFunctor.changeBoard_self]
  exact Category.id_comp _

def selectedReads {state : Configuration Value Occurrence} (board : Board state)
    {premises : List Pattern} (selection : ContextMap board.judgments premises) : List Occurrence :=
  List.ofFn fun index => board.occurrenceAt (board.entryIndex (selection.position index))

theorem selectedReads_present {state : Configuration Value Occurrence} (board : Board state)
    {premises : List Pattern} (selection : ContextMap board.judgments premises) :
    ∀ occurrence ∈ selectedReads board selection, occurrence ∈ state.present := by
  intro occurrence member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact (board.at_occupied _).1

theorem selectedReads_labels {state : Configuration Value Occurrence} (board : Board state)
    {premises : List Pattern} (selection : ContextMap board.judgments premises) :
    (selectedReads board selection).map label = premises.map (fun p => (Space.judgments, judgment p)) := by
  rw [selectedReads, List.map_ofFn]
  conv_rhs => rw [← List.ofFn_get premises, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  simp only [Function.comp_apply]
  rw [board.at_readback, board.entry_get, selection.judgment]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
