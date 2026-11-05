import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedInstructionObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineEntryControls

/-!
# Concrete instruction observations and raw-step separation

One actual memo edit takes five ordinary firings and exactly one instruction
episode. Whole source-entry programs also instantiate native fixed-point
reachability, with the same complete ordered result observations as the
ordinary machine. Shared resampling is refuted in that modal semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedInstructionObservation.Controls

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice (Store Comp Outcome)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open NeedMachine.Controls

def initialState : RunningState :=
  ⟨initial,1,(fun _ => oldStore),intent.plan.input,NeedMachine.EntryControls.retained_example_running⟩

theorem actual_copy_path : NeedMachine.CopyPath 1 intent.plan.input intent.plan.reads 0
    (.memo 0 (.done (.sym 42))) resume started finished := by
  apply (Relation.ReflTransGen.single (show ∃ event : SnapshotCopy.Event CallTimeChoice.Suspension,
    Step NeedMachine.action NeedMachine.label (NeedMachine.copyRule 1 intent.plan.input intent.plan.reads 0
      (.memo 0 (.done (.sym 42))) resume event) started prepared from
    ⟨.begin 1 [3],prepareSelection,prepare_valid,rfl⟩)).trans
  apply (Relation.ReflTransGen.single (show ∃ event : SnapshotCopy.Event CallTimeChoice.Suspension,
    Step NeedMachine.action NeedMachine.label (NeedMachine.copyRule 1 intent.plan.input intent.plan.reads 0
      (.memo 0 (.done (.sym 42))) resume event) prepared copied from
    ⟨.copy 0 0 cached,copyCellSelection,copy_valid,rfl⟩)).trans
  exact Relation.ReflTransGen.single ⟨.finish 1 [3],finishSelection,finish_valid,rfl⟩

theorem actual_edit_episode : NeedMachine.Episode [] initial resumed :=
  .edit 1 intent 0 (.memo 0 (.done (.sym 42))) resume (.memo 0 cached (.done (.sym 42))) rfl
    ⟨beginSelection,begin_valid,rfl⟩ actual_copy_path rfl ⟨updateSelection,update_valid,rfl⟩

theorem resumed_running : NeedMachine.Running resumed 2 (Function.update (fun _ => oldStore) 1 newStore)
    (NeedControl.resumeAt 1 resume) := by
  have waiting := initialState.valid.edit intent (.memo 0 (.done (.sym 42))) resume rfl
    ⟨beginSelection,begin_valid,rfl⟩
  obtain ⟨rank,ready⟩ := waiting.copy_path actual_copy_path
  exact (ready.commit (.memo 0 cached (.done (.sym 42))) rfl ⟨updateSelection,update_valid,rfl⟩).2

def resumedState : RunningState :=
  ⟨resumed,2,Function.update (fun _ => oldStore) 1 newStore,NeedControl.resumeAt 1 resume,resumed_running⟩

def actualEdge : EpisodeEdge [] := ⟨initialState,resumedState,actual_edit_episode⟩

theorem actual_episode_is_one_source_instruction :
    CallTimeChoiceInstructions.Instruction [] initialState.decode resumedState.decode := actualEdge.instruction

theorem completed_edit_is_not_one_raw_firing : ¬ NeedMachine.Executes [] initial resumed := by
  intro execution
  apply initialState.valid.no_new_frontier_after_one execution (NeedControl.resumeAt 1 resume)
  exact ⟨(14,.control 2 (NeedControl.resumeAt 1 resume)),by decide +kernel,rfl⟩

theorem an_episode_reaches_the_published_control :
    derivedDiamond (episodeSpan []) (fun state => state.decode = resumedState.decode) initialState :=
  ⟨actualEdge,rfl,rfl⟩

def programState (code : Comp) : RunningState :=
  ⟨NeedMachine.entry Store.empty [] code,1,(fun _ => Store.empty),.task (.eval 0 [] code) [],
    NeedMachine.entry_running Store.empty [] code⟩

def Returns (answers : List (Outcome × List Nat)) : CallTimeChoiceInstructions.Control → Prop
  | .returned results [] => results.map (fun result => (result.1,result.2.trace)) = answers
  | _ => False

def answerEnvironment (answers : List (Outcome × List Nat)) : Env CallTimeChoiceInstructions.Control 1 :=
  fun _ => {state | Returns answers state}

theorem native_reachability_iff_observes (program : CallTimeChoice.Program) (code : Comp)
    (answers : List (Outcome × List Nat)) :
    satisfies (transitionSystem (episodeSpan program))
      (pullEnvironment (projection program).states (answerEnvironment answers)) reachFormula (programState code) ↔
        NeedMachine.EntryControls.Observes program code answers := by
  refine (reachability_iff_physical_path program (Returns answers) (programState code)).trans ?_
  constructor
  · rintro ⟨after,next,stores,control,path,running,returned⟩
    cases decoded : control.decode stores with
    | task goal stack => simp [Returns,decoded] at returned
    | returned results stack =>
        cases stack with
        | cons frame rest => simp [Returns,decoded] at returned
        | nil =>
            exact ⟨results,after,next,stores,control,path,running,decoded,
              by simpa [Returns,decoded] using returned⟩
  · rintro ⟨results,after,next,stores,control,path,running,decoded,observed⟩
    exact ⟨after,next,stores,control,path,running,by simpa [Returns,decoded] using observed⟩

theorem shared_program_has_native_reachability :
    satisfies (transitionSystem (episodeSpan []))
      (pullEnvironment (projection []).states (answerEnvironment
        [(.ok (CallTimeChoiceInstructions.Controls.pair (.sym 1) (.sym 1)),[]),
         (.ok (CallTimeChoiceInstructions.Controls.pair (.sym 2) (.sym 2)),[])]))
      reachFormula (programState CallTimeChoiceInstructions.Controls.shared) :=
  (native_reachability_iff_observes _ _ _).mpr ((NeedMachine.EntryControls.shared_program_exact _).mpr rfl)

theorem shared_resampling_is_modally_refuted :
    ¬ satisfies (transitionSystem (episodeSpan []))
      (pullEnvironment (projection []).states (answerEnvironment
        [(.ok (CallTimeChoiceInstructions.Controls.pair (.sym 1) (.sym 1)),[]),
         (.ok (CallTimeChoiceInstructions.Controls.pair (.sym 1) (.sym 2)),[]),
         (.ok (CallTimeChoiceInstructions.Controls.pair (.sym 2) (.sym 1)),[]),
         (.ok (CallTimeChoiceInstructions.Controls.pair (.sym 2) (.sym 2)),[])]))
      reachFormula (programState CallTimeChoiceInstructions.Controls.shared) := by
  intro holds
  exact NeedMachine.EntryControls.shared_program_cannot_resample
    ((native_reachability_iff_observes _ _ _).mp holds)

def callingProgram : CallTimeChoice.Program := [⟨4,0,.ret (.sym 8)⟩]
def bodyEntry : RunningState := programState (.ret (.sym 8))
def incomingCall : SourceEdge callingProgram :=
  ⟨.task (.eval Store.empty [] (.callRule 0 [])) [],bodyEntry.decode,
    .callRule Store.empty [] 0 [] ⟨4,0,.ret (.sym 8)⟩ rfl rfl []⟩

theorem entry_has_no_physical_predecessor (edge : EpisodeEdge callingProgram) : edge.after ≠ bodyEntry := by
  intro same
  have recorded := edge.episode.records_equations
  have empty : edge.after.world.equations = [] := by rw [same]; rfl
  exact recorded empty

/-- The logical body has a possible calling predecessor, while its fresh
physical entry has no matching-equation history. Future coverage alone
therefore cannot preserve the incoming OSLF box. -/
theorem incoming_box_is_not_preserved :
    derivedBox (episodeSpan callingProgram) (fun _ => False) bodyEntry ∧
      ¬ derivedBox (sourceSpan callingProgram) (fun _ => False) bodyEntry.decode := by
  refine ⟨?_,?_⟩
  · intro edge ends
    exact entry_has_no_physical_predecessor edge ends
  · intro everyPredecessor
    exact everyPredecessor incomingCall rfl

theorem projection_does_not_lift_all_predecessors : ¬ (projection callingProgram).TargetLifts := by
  intro lifts
  obtain ⟨edge,ends,_⟩ := lifts bodyEntry incomingCall rfl
  exact entry_has_no_physical_predecessor edge ends

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedInstructionObservation.Controls
