import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControlReferences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineControls
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructionControls

/-!
# Controlled-block and finite-support instances

Every independent source store has a finite physical waiting configuration
to which the general block-completion theorem applies. The concrete retained
episode also checks equation projection. A colliding snapshot interpretation
changes the saved branch's actual source result, separating fresh resumption
from accidental capture.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.ProjectionControls

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Store)
open Controls (intent resume cached changed oldStore newStore)

def canonicalWaiting (store : Store) : World :=
  ⟨[],insert (store.cells.length+4,.waiting 1 intent.plan)
    ((NeedSnapshots.encode 1 0 store).present.image embedHeap)⟩

theorem canonical_heap (store : Store) : heapWorld (canonicalWaiting store) = NeedSnapshots.encode 1 0 store := by
  apply congrArg₂ Configuration.mk rfl
  ext occurrence
  simp only [canonicalWaiting,mem_heapPresent,Finset.mem_insert]
  constructor
  · rintro (same | present)
    · have impossible := congrArg label same
      cases impossible
    · obtain ⟨original,member,same⟩ := Finset.mem_image.mp present
      have equal := embedHeap_injective same
      exact equal ▸ member
  · intro member
    exact Or.inr (Finset.mem_image.mpr ⟨occurrence,member,rfl⟩)

/-- An arbitrary store, not only the displayed three- or one-cell examples,
provides an inhabited instance of the controlled block theorem. -/
theorem every_store_has_a_controlled_edit (store : Store) :
    ∃ after, Path [] (canonicalWaiting store) after ∧
      SnapshotCopy.Snapshot (heapWorld after).present 0 store.cells store.trace ∧
      SnapshotCopy.Snapshot (heapWorld after).present 1 (store.setMemo 0 (.done (.sym 42))).cells store.trace ∧
      Has after.present (.control 2 (resumeAt 1 resume)) ∧ ¬ Has after.present (.heap (.reply 1 1)) := by
  have consistent : action.Consistent (canonicalWaiting store).equations := ⟨(),by simp [canonicalWaiting,SubstitutionAction.Models]⟩
  have snapshot : SnapshotCopy.Snapshot (heapWorld (canonicalWaiting store)).present 0 store.cells store.trace := by
    rw [canonical_heap]
    exact NeedSnapshots.encoded_snapshot 1 0 store
  have fresh : SnapshotCopy.Fresh (heapWorld (canonicalWaiting store)).present 1 := by
    rw [canonical_heap]
    exact NeedSnapshots.encoded_fresh store (by decide : 0 ≠ 1)
  have request : Has (canonicalWaiting store).present (.heap (.request 1 0)) := by
    refine ⟨embedHeap (store.cells.length+3,.request 1 0),?_,rfl⟩
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨_,by simp [NeedSnapshots.encode],rfl⟩
  have waiting : Has (canonicalWaiting store).present (.waiting 1 intent.plan) :=
    ⟨(store.cells.length+4,.waiting 1 intent.plan),Finset.mem_insert_self ..,rfl⟩
  obtain ⟨after,path,parent,child,active,noReply,_⟩ := edit_block_completes [] (canonicalWaiting store) 1 0
    intent.plan.input intent.plan.reads (.memo 0 (.done (.sym 42))) resume store consistent snapshot fresh request waiting
  exact ⟨after,path,parent,child,active,noReply⟩

theorem actual_preparation_projects :
    Step SnapshotCopy.action SnapshotCopy.label (SnapshotCopy.beginRule 1 0 1 1 [3])
      (heapWorld Controls.started) (heapWorld Controls.prepared) :=
  copy_projects 1 intent.plan.input intent.plan.reads 0 (.memo 0 (.done (.sym 42))) resume (.begin 1 [3])
    ⟨Controls.prepareSelection,Controls.prepare_valid,rfl⟩

theorem actual_commit_projects_without_reissuing_reply :
    Step SnapshotCopy.action SnapshotCopy.label
      ((NeedStoreOperations.Event.memo 0 cached (.done (.sym 42))).publishedRule 1 1)
      (heapWorld Controls.finished) (heapWorld Controls.resumed) :=
  commit_projects 1 intent.plan.input intent.plan.reads 0 resume (.memo 0 cached (.done (.sym 42)))
    ⟨Controls.updateSelection,Controls.update_valid,rfl⟩

theorem projected_equations_retain_their_prefix :
    (heapWorld Controls.started).equations.IsPrefix (heapWorld Controls.terminal).equations ∧
      (heapWorld Controls.resumed).equations.length = 14 ∧ (heapWorld Controls.terminal).equations.length = 16 := by
  decide +kernel

def originalStores : Nat → Store := fun _ => oldStore
def goodControl := (resumeAt 1 resume).decode (Function.update originalStores 1 newStore)
def capturedControl := (resumeAt 0 resume).decode (Function.update originalStores 0 newStore)

theorem actual_resume_uses_the_support_theorem :
    goodControl = intent.plan.action.decode originalStores := by
  apply Intent.resume_interpretation intent originalStores 1 0 (.memo 0 (.done (.sym 42))) resume rfl
  simp [Controls.intent,Controls.saved,Intent.plan,Control.names,Goal.names,Frame.names]

def runSource (control : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control) :=
  Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Controls.observations
    (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.runFuel [] 50 control)

theorem fresh_resumption_retains_the_saved_result : runSource goodControl =
    some [(.ok (.sym 42),[3]),(.ok (.sym 7),[3])] := by decide +kernel

theorem colliding_resumption_changes_the_saved_result : runSource capturedControl =
    some [(.ok (.sym 42),[3]),(.ok (.sym 42),[3])] := by decide +kernel

def shared : Intent [] := .choose 0 [] (.ret (.sym 1)) (.ret (.sym 2)) []

theorem reference_sharing_is_allowed : shared.plan.input.names = [0] ∧ shared.plan.action.oldNames = [0,0] := by
  decide +kernel

theorem saved_branch_reference_is_retained_separately :
    intent.plan.reads = [.ready 0] ∧ intent.plan.input.names = [0,0] ∧
      resume.names = [none,some 0] := by decide +kernel

def distantSaved : Intent [] := .commitOk 0 (.sym 42) 0 [] [.later (.forceVal 3 (.need 0))]

theorem current_reads_do_not_cover_all_saved_references :
    distantSaved.plan.input.names = [0,3] ∧ distantSaved.plan.action.oldNames = [3] ∧
      ∀ row ∈ distantSaved.plan.reads, 3 ∉ row.mentions := by decide +kernel

theorem actual_path_retains_one_controller : controllerCount Controls.terminal = 1 :=
  Controls.actual_complete_controlled_execution.single_controller (by decide +kernel)

def duplicateController : World :=
  {Controls.initial with present := insert (100,.control 1 intent.plan.input) Controls.initial.present}

theorem equal_control_labels_do_not_identify_occurrences : controllerCount duplicateController = 2 := by
  decide +kernel

theorem duplicated_control_fails_the_single_controller_invariant : controllerCount duplicateController ≠ 1 := by
  decide +kernel

theorem the_prepared_example_cannot_spin :
    ∃ prepared, Executes [] (canonicalWaiting oldStore) prepared ∧
      ¬ ∃ worlds : Nat → World, worlds 0 = prepared ∧
        (∀ n, Has (worlds n).present (.waiting 1 intent.plan)) ∧
        ∀ n, Executes [] (worlds n) (worlds (n+1)) := by
  have consistent : action.Consistent (canonicalWaiting oldStore).equations :=
    ⟨(),by simp [canonicalWaiting,SubstitutionAction.Models]⟩
  have snapshot : SnapshotCopy.Snapshot (heapWorld (canonicalWaiting oldStore)).present
      0 oldStore.cells oldStore.trace := by
    rw [canonical_heap]
    exact NeedSnapshots.encoded_snapshot 1 0 oldStore
  have fresh : SnapshotCopy.Fresh (heapWorld (canonicalWaiting oldStore)).present 1 := by
    rw [canonical_heap]
    exact NeedSnapshots.encoded_fresh oldStore (by decide : 0 ≠ 1)
  have requested : (4,SnapshotCopy.Row.request 1 0) ∈ (heapWorld (canonicalWaiting oldStore)).present := by
    rw [canonical_heap]
    decide +kernel
  obtain ⟨heapAfter,⟨firing⟩⟩ := SnapshotCopy.begin_exists (heapWorld (canonicalWaiting oldStore))
    1 0 1 oldStore.cells oldStore.trace snapshot fresh (4,.request 1 0) requested rfl (heap_consistent consistent)
  have waiting : Has (canonicalWaiting oldStore).present (.waiting 1 intent.plan) := by
    exact ⟨(5,.waiting 1 intent.plan),by decide +kernel,rfl⟩
  obtain ⟨prepared,step,projected⟩ := copy_lifts 1 intent.plan.input intent.plan.reads 0
    (.memo 0 (.done (.sym 42))) resume (.begin 1 [3]) consistent waiting firing.ordinary
  have execution : Executes [] (canonicalWaiting oldStore) prepared :=
    ⟨_,.copy _ _ _ _ _ _ _,step⟩
  have single : controllerCount prepared = 1 :=
    execution.controller_count.trans (by decide +kernel)
  obtain ⟨cursor,progress⟩ := SnapshotCopy.progress_after_begin snapshot fresh firing
  have preparedProgress : SnapshotCopy.Progress (heapWorld prepared) 1 0 1 oldStore.cells oldStore.trace
      0 oldStore.cells.length cursor := by
    rw [projected]
    exact progress
  exact ⟨prepared,execution,no_infinite_waiting intent.plan.input intent.plan.reads
    (.memo 0 (.done (.sym 42))) resume single preparedProgress⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.ProjectionControls
