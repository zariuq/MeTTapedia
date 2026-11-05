import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

/-!
# Projecting controlled firings to their actual heap firings

Projection retains heap occurrence identities and filters the actual
accumulated equation history. The proof applies to this ground machine's
positive and heap-absence rules. Guards are checked at the original world;
no count guard or nonrigid unification profile is claimed by this result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Suspension)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def rowPart : Row → Option (SnapshotCopy.Row Suspension)
  | .heap row => some row
  | _ => none

def checkPart : Check Row → Option (Check (SnapshotCopy.Row Suspension))
  | .absent (.heap row) => some (.absent row)
  | _ => none

def HeapAbsenceChecks (rule : RuleInstance Row) : Prop :=
  ∀ check ∈ rule.checks, ∃ row, check = .absent (.heap row)

def heapRule (rule : RuleInstance Row) : RuleInstance (SnapshotCopy.Row Suspension) :=
  ⟨rule.take.filterMap rowPart,rule.read.filterMap rowPart,rule.tell.filterMap heapEquation,
    rule.checks.filterMap checkPart,rule.produce.filterMap rowPart⟩

def heapSelection (picked : Selection Occurrence) : Selection (SnapshotCopy.Occurrence Suspension) :=
  ⟨picked.taken.filterMap heapPart,picked.read.filterMap heapPart,picked.made.filterMap heapPart⟩

@[simp] theorem mem_heapList (selected : List Occurrence) (occurrence : SnapshotCopy.Occurrence Suspension) :
    occurrence ∈ selected.filterMap heapPart ↔ embedHeap occurrence ∈ selected := by
  simp [List.mem_filterMap]

theorem heapList_nodup {selected : List Occurrence} (distinct : selected.Nodup) :
    (selected.filterMap heapPart).Nodup := by
  apply distinct.filterMap
  intro first second heap atFirst atSecond
  have firstEq := (heapPart_some first heap).mp (Option.mem_def.mp atFirst)
  have secondEq := (heapPart_some second heap).mp (Option.mem_def.mp atSecond)
  exact firstEq.trans secondEq.symm

theorem heap_labels (selected : List Occurrence) :
    (selected.filterMap heapPart).map SnapshotCopy.label = (selected.map label).filterMap rowPart := by
  induction selected with
  | nil => rfl
  | cons occurrence rest ih =>
      rcases occurrence with ⟨index,row⟩
      cases row with
      | heap row =>
          change row :: (rest.filterMap heapPart).map SnapshotCopy.label =
            row :: (rest.map label).filterMap rowPart
          exact congrArg (List.cons row) ih
      | control => exact ih
      | waiting => exact ih

theorem diagonal_equations (selected : List Occurrence) :
    (Selection.equations label (selected.map label) selected).filterMap heapEquation =
      Selection.equations SnapshotCopy.label
        ((selected.filterMap heapPart).map SnapshotCopy.label) (selected.filterMap heapPart) := by
  induction selected with
  | nil => rfl
  | cons occurrence rest ih =>
      rcases occurrence with ⟨index,row⟩
      cases row with
      | heap row =>
          change (row,row) :: (Selection.equations label (rest.map label) rest).filterMap heapEquation =
            (row,row) :: Selection.equations SnapshotCopy.label
              ((rest.filterMap heapPart).map SnapshotCopy.label) (rest.filterMap heapPart)
          exact congrArg (List.cons (row,row)) ih
      | control => exact ih
      | waiting => exact ih

theorem selected_equations {patterns : List Row} {selected : List Occurrence}
    (labels : selected.map label = patterns) :
    (Selection.equations label patterns selected).filterMap heapEquation =
      Selection.equations SnapshotCopy.label (patterns.filterMap rowPart) (selected.filterMap heapPart) := by
  rw [← labels,← heap_labels]
  exact diagonal_equations selected

theorem problem_projected {rule : RuleInstance Row} {picked : Selection Occurrence} {before : World}
    (valid : picked.Valid action label rule before) :
    (picked.problem label rule before).filterMap heapEquation =
      (heapSelection picked).problem SnapshotCopy.label (heapRule rule) (heapWorld before) := by
  simp only [Selection.problem,List.filterMap_append]
  rw [selected_equations (Selected.input_labels valid).1,
    selected_equations (Selected.input_labels valid).2]
  rfl

theorem result_projected {rule : RuleInstance Row} {picked : Selection Occurrence} {before : World}
    (valid : picked.Valid action label rule before) :
    heapWorld (picked.result label rule before) =
      (heapSelection picked).result SnapshotCopy.label (heapRule rule) (heapWorld before) := by
  apply congrArg₂ Configuration.mk
  · exact problem_projected valid
  · ext occurrence
    simp [heapWorld,Selection.result,fire,Selection.commit,heapSelection,mem_heapPresent]

/-- Each selected positive or heap-absence firing has a genuine projected
selection, with the same physical data resources and full data equations. -/
theorem valid_projected {rule : RuleInstance Row} {picked : Selection Occurrence} {before : World}
    (checks : HeapAbsenceChecks rule) (valid : picked.Valid action label rule before) :
    (heapSelection picked).Valid SnapshotCopy.action SnapshotCopy.label (heapRule rule) (heapWorld before) := by
  have takes : (heapSelection picked).taken.map SnapshotCopy.label = (heapRule rule).take := by
    change (picked.taken.filterMap heapPart).map SnapshotCopy.label = rule.take.filterMap rowPart
    rw [heap_labels,(Selected.input_labels valid).1]
  have reads : (heapSelection picked).read.map SnapshotCopy.label = (heapRule rule).read := by
    change (picked.read.filterMap heapPart).map SnapshotCopy.label = rule.read.filterMap rowPart
    rw [heap_labels,(Selected.input_labels valid).2]
  have outputs : (heapSelection picked).made.map SnapshotCopy.label = (heapRule rule).produce := by
    change (picked.made.filterMap heapPart).map SnapshotCopy.label = rule.produce.filterMap rowPart
    rw [heap_labels,valid.outputs]
  refine ⟨heapList_nodup valid.take_distinct,heapList_nodup valid.output_distinct,?_,?_,outputs,?_,?_,?_⟩
  · simpa using (congrArg List.length takes).symm
  · simpa using (congrArg List.length reads).symm
  · refine ⟨?_,?_,?_,?_,by intro query member; cases member⟩
    · intro occurrence member
      apply (mem_heapPresent before.present occurrence).mpr
      exact valid.occurrences.taken_subset (by simpa [heapSelection,Selection.commit] using member)
    · intro occurrence member
      apply (mem_heapPresent before.present occurrence).mpr
      exact valid.occurrences.kept_subset (by simpa [heapSelection,Selection.commit] using member)
    · apply Finset.disjoint_left.mpr
      intro occurrence taken kept
      exact Finset.disjoint_left.mp valid.occurrences.apart
        (by simpa [heapSelection,Selection.commit] using taken)
        (by simpa [heapSelection,Selection.commit] using kept)
    · apply Finset.disjoint_left.mpr
      intro occurrence made old
      exact Finset.disjoint_left.mp valid.occurrences.fresh
        (by simpa [heapSelection,Selection.commit] using made)
        ((mem_heapPresent before.present occurrence).mp old)
  · have consistent := heap_consistent (world := picked.result label rule before) valid.consistent
    change SnapshotCopy.action.Consistent ((picked.problem label rule before).filterMap heapEquation) at consistent
    rw [problem_projected valid] at consistent
    exact consistent
  · intro check member
    obtain ⟨original,inRule,projects⟩ := List.mem_filterMap.mp member
    obtain ⟨row,rfl⟩ := checks original inRule
    have same : check = .absent row := (Option.some.inj projects).symm
    subst check
    obtain ⟨assignment,solved⟩ := valid.consistent
    intro _ _ occurrence old equal
    apply valid.checks (.absent (.heap row)) inRule assignment solved (embedHeap occurrence)
      ((mem_heapPresent before.present occurrence).mp old)
    exact congrArg Row.heap equal

theorem step_projected {rule : RuleInstance Row} {before after : World}
    (checks : HeapAbsenceChecks rule) (stepped : Step action label rule before after) :
    Step SnapshotCopy.action SnapshotCopy.label (heapRule rule) (heapWorld before) (heapWorld after) := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  exact ⟨heapSelection picked,valid_projected checks valid,result_projected valid⟩

theorem heapRule_copyRule (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension) :
    heapRule (copyRule job input reads source operation resume event) = event.rule job source job := by
  cases event <;>
    simp [heapRule,copyRule,SnapshotCopy.Event.rule,SnapshotCopy.beginRule,SnapshotCopy.copyRule,
      SnapshotCopy.finishRule,rowPart,checkPart,Check.map]

theorem copyRule_checks (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension) : HeapAbsenceChecks (copyRule job input reads source operation resume event) := by
  cases event <;>
    simp [HeapAbsenceChecks,copyRule,SnapshotCopy.Event.rule,SnapshotCopy.beginRule,SnapshotCopy.copyRule,
      SnapshotCopy.finishRule,Check.map]

theorem copy_projects {before after : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension)
    (stepped : Step action label (copyRule job input reads source operation resume event) before after) :
    Step SnapshotCopy.action SnapshotCopy.label (event.rule job source job) (heapWorld before) (heapWorld after) := by
  simpa only [heapRule_copyRule] using step_projected (copyRule_checks job input reads source operation resume event) stepped

/-- Every controlled copying event decreases the existing exact rank.
The frame contains the real selected occurrences, not reconstructed data. -/
theorem controlled_copy_phase {before after : World} {job source rank : Nat}
    {values : List Suspension} {trace : List Nat}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (phase : SnapshotCopy.Phase (heapWorld before) job source job values trace rank)
    (event : SnapshotCopy.Event Suspension)
    (stepped : Step action label (copyRule job input reads source operation resume event) before after) :
    ∃ nextRank, SnapshotCopy.Phase (heapWorld after) job source job values trace nextRank ∧ rank = nextRank+1 := by
  obtain ⟨token,⟨firing⟩⟩ := SnapshotCopy.firing_of_step event
    (copy_projects job input reads source operation resume event stepped)
  exact phase.step event firing

theorem heapRule_commitRule (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat) (resume : NeedControl.Resume)
    (event : NeedStoreOperations.Event) :
    heapRule (commitRule job input reads source resume event) = event.publishedRule job job := by
  cases event <;> simp [heapRule,commitRule,NeedStoreOperations.Event.rule,NeedStoreOperations.Event.publishedRule,rowPart]

theorem commit_projects {before after : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat) (resume : NeedControl.Resume)
    (event : NeedStoreOperations.Event)
    (stepped : Step action label (commitRule job input reads source resume event) before after) :
    Step SnapshotCopy.action SnapshotCopy.label (event.publishedRule job job) (heapWorld before) (heapWorld after) := by
  have checks : HeapAbsenceChecks (commitRule job input reads source resume event) := by
    simp [HeapAbsenceChecks,commitRule]
  simpa only [heapRule_commitRule] using step_projected checks stepped

theorem commit_heap_preserved {before after : World} {job source : Nat}
    {store : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Store}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (resume : NeedControl.Resume) (event : NeedStoreOperations.Event)
    (represented : NeedStoreOperations.Editable (heapWorld before).present job job store)
    (stepped : Step action label (commitRule job input reads source resume event) before after) :
    SnapshotCopy.Snapshot (heapWorld after).present job (event.operation.apply store).cells (event.operation.apply store).trace ∧
      SnapshotCopy.UniqueRow (heapWorld after).present
        (.metadata job (event.operation.apply store).cells.length (event.operation.apply store).trace) ∧
      ¬ SnapshotCopy.Has (heapWorld after).present (.reply job job) :=
  NeedStoreOperations.published_preserves represented event (commit_projects job input reads source resume event stepped)

theorem commit_other_snapshot_preserved {before after : World} {job source other : Nat}
    {store : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Store} {values : List Suspension} {trace : List Nat}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (resume : NeedControl.Resume) (event : NeedStoreOperations.Event)
    (represented : NeedStoreOperations.Editable (heapWorld before).present job job store)
    (different : other ≠ job) (retained : SnapshotCopy.Snapshot (heapWorld before).present other values trace)
    (stepped : Step action label (commitRule job input reads source resume event) before after) :
    SnapshotCopy.Snapshot (heapWorld after).present other values trace :=
  NeedStoreOperations.published_preserves_other represented event
    (commit_projects job input reads source resume event stepped) different retained

theorem commit_outputs_control {before after : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat) (resume : NeedControl.Resume)
    (event : NeedStoreOperations.Event)
    (stepped : Step action label (commitRule job input reads source resume event) before after) :
    Has after.present (.control (job+1) (NeedControl.resumeAt job resume)) := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  exact Selected.output_rows valid _ (by simp [commitRule])

@[simp] theorem filter_embedded (selected : List (SnapshotCopy.Occurrence Suspension)) :
    (selected.map embedHeap).filterMap heapPart = selected := by
  induction selected with
  | nil => rfl
  | cons occurrence rest ih =>
      change occurrence :: (rest.map embedHeap).filterMap heapPart = occurrence :: rest
      exact congrArg (List.cons occurrence) ih

theorem labels_embedded (selected : List (SnapshotCopy.Occurrence Suspension)) :
    (selected.map embedHeap).map label = (selected.map SnapshotCopy.label).map Row.heap := by
  simp only [List.map_map]
  rfl

def liftCopySelection (picked : Selection (SnapshotCopy.Occurrence Suspension)) (waiting : Occurrence) : Selection Occurrence :=
  ⟨picked.taken.map embedHeap,picked.read.map embedHeap ++ [waiting],picked.made.map embedHeap⟩

theorem heapSelection_liftCopySelection (picked : Selection (SnapshotCopy.Occurrence Suspension))
    (waiting : Occurrence) (noHeap : heapPart waiting = none) :
    heapSelection (liftCopySelection picked waiting) = picked := by
  cases picked
  simp only [heapSelection,liftCopySelection,List.filterMap_append,List.filterMap_cons,
    noHeap,List.filterMap_nil,List.append_nil,filter_embedded]

/-- A concrete heap firing lifts with exactly its original physical heap
selection and endpoint. The additional control read cannot alias a heap
take, and the absence test keeps its original admission world. -/
theorem lift_copy_selection {before : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension) (picked : Selection (SnapshotCopy.Occurrence Suspension))
    (qualified : picked.Valid SnapshotCopy.action SnapshotCopy.label (event.rule job source job) (heapWorld before))
    (consistent : action.Consistent before.equations) (waiting : Occurrence) (waitingHere : waiting ∈ before.present)
    (atWaiting : label waiting = .waiting job ⟨input,reads,.edit source operation resume⟩) :
    (liftCopySelection picked waiting).Valid action label (copyRule job input reads source operation resume event) before := by
  have labels := ExactInteractionExecution.rigid_input_labels SnapshotCopy.action (by intros; rfl) qualified
  have takes : (liftCopySelection picked waiting).taken.map label =
      (copyRule job input reads source operation resume event).take := by
    change (picked.taken.map embedHeap).map label = (event.rule job source job).take.map Row.heap
    rw [labels_embedded,labels.1]
  have kept : (liftCopySelection picked waiting).read.map label =
      (copyRule job input reads source operation resume event).read := by
    simp only [liftCopySelection,copyRule,List.map_append,List.map_cons,List.map_nil,
      labels_embedded,labels.2,atWaiting]
  have made : (liftCopySelection picked waiting).made.map label =
      (copyRule job input reads source operation resume event).produce := by
    change (picked.made.map embedHeap).map label = (event.rule job source job).produce.map Row.heap
    rw [labels_embedded,qualified.outputs]
  have notWaiting (occurrence : SnapshotCopy.Occurrence Suspension) : embedHeap occurrence ≠ waiting := by
    intro same
    have tagged := (congrArg label same).trans atWaiting
    cases tagged
  refine ⟨qualified.take_distinct.map embedHeap_injective,qualified.output_distinct.map embedHeap_injective,
    ?_,?_,made,?_,?_,?_⟩
  · simpa using (congrArg List.length takes).symm
  · simpa using (congrArg List.length kept).symm
  · refine ⟨?_,?_,?_,?_,by intro query member; cases member⟩
    · intro occurrence member
      have selectedHere : occurrence ∈ picked.taken.map embedHeap := by
        simpa only [Selection.commit,liftCopySelection,List.mem_toFinset] using member
      obtain ⟨old,selected,rfl⟩ := List.mem_map.mp selectedHere
      apply (mem_heapPresent before.present old).mp
      exact qualified.occurrences.taken_subset (by simpa [Selection.commit] using selected)
    · intro occurrence member
      have selected : occurrence ∈ picked.read.map embedHeap ∨ occurrence = waiting := by
        simpa only [Selection.commit,liftCopySelection,List.mem_toFinset,List.mem_append,List.mem_singleton] using member
      rcases selected with heap | rfl
      · obtain ⟨old,selected,rfl⟩ := List.mem_map.mp heap
        apply (mem_heapPresent before.present old).mp
        exact qualified.occurrences.kept_subset (by simpa [Selection.commit] using selected)
      · exact waitingHere
    · apply Finset.disjoint_left.mpr
      intro occurrence taken keptHere
      have selectedHere : occurrence ∈ picked.taken.map embedHeap := by
        simpa only [Selection.commit,liftCopySelection,List.mem_toFinset] using taken
      obtain ⟨old,selected,rfl⟩ := List.mem_map.mp selectedHere
      have keptHere : embedHeap old ∈ picked.read.map embedHeap ∨ embedHeap old = waiting := by
        simpa only [Selection.commit,liftCopySelection,List.mem_toFinset,List.mem_append,List.mem_singleton] using keptHere
      rcases keptHere with heap | impossible
      · obtain ⟨read,selectedRead,same⟩ := List.mem_map.mp heap
        have equal := embedHeap_injective same
        subst read
        exact Finset.disjoint_left.mp qualified.occurrences.apart
          (by simpa [Selection.commit] using selected) (by simpa [Selection.commit] using selectedRead)
      · exact notWaiting old impossible
    · apply Finset.disjoint_left.mpr
      intro occurrence created present
      have selectedHere : occurrence ∈ picked.made.map embedHeap := by
        simpa only [Selection.commit,liftCopySelection,List.mem_toFinset] using created
      obtain ⟨old,selected,rfl⟩ := List.mem_map.mp selectedHere
      exact Finset.disjoint_left.mp qualified.occurrences.fresh
        (by simpa [Selection.commit] using selected) ((mem_heapPresent before.present old).mpr present)
  · obtain ⟨assignment,solved⟩ := consistent
    refine ⟨assignment,?_⟩
    change action.Models assignment (before.equations ++
      Selection.equations label (copyRule job input reads source operation resume event).take
        (liftCopySelection picked waiting).taken ++
      Selection.equations label (copyRule job input reads source operation resume event).read
        (liftCopySelection picked waiting).read ++ [])
    rw [← takes,← kept]
    simp only [SubstitutionAction.models_append,SubstitutionAction.models_nil,and_true]
    exact ⟨⟨solved,RequestActivation.self_equations action assignment label _⟩,
      RequestActivation.self_equations action assignment label _⟩
  · intro check member
    cases event with
    | begin count trace =>
        have same : check = .absent (.heap (.allocated job)) := by
          simpa [copyRule,SnapshotCopy.Event.rule,SnapshotCopy.beginRule,Check.map] using member
        subst check
        obtain ⟨assignment,solved⟩ := qualified.consistent
        intro _ _ occurrence present equal
        rcases occurrence with ⟨index,row⟩
        change Row.heap (.allocated job) = row at equal
        subst row
        exact qualified.checks (.absent (.allocated job)) (by simp [SnapshotCopy.Event.rule,SnapshotCopy.beginRule])
          assignment solved (index,.allocated job) ((mem_heapPresent before.present _).mpr present) rfl
    | copy | finish => simp [copyRule,SnapshotCopy.Event.rule,SnapshotCopy.copyRule,SnapshotCopy.finishRule] at member

theorem copy_lifts {before : World} {heapAfter : SnapshotCopy.World Suspension}
    (job : Nat) (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (source : Nat) (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension) (consistent : action.Consistent before.equations)
    (waiting : Has before.present (.waiting job ⟨input,reads,.edit source operation resume⟩))
    (heapStep : Step SnapshotCopy.action SnapshotCopy.label (event.rule job source job) (heapWorld before) heapAfter) :
    ∃ after, Step action label (copyRule job input reads source operation resume event) before after ∧ heapWorld after = heapAfter := by
  obtain ⟨picked,qualified,rfl⟩ := heapStep
  obtain ⟨control,here,atControl⟩ := waiting
  have valid := lift_copy_selection job input reads source operation resume event picked qualified consistent control here atControl
  have noHeap : heapPart control = none := by
    rcases control with ⟨index,row⟩
    change row = .waiting job ⟨input,reads,.edit source operation resume⟩ at atControl
    subst row
    rfl
  refine ⟨(liftCopySelection picked control).result label _ before,⟨_,valid,rfl⟩,?_⟩
  rw [result_projected valid,heapRule_copyRule,heapSelection_liftCopySelection picked control noHeap]

theorem copy_keeps_waiting {before after : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (event : SnapshotCopy.Event Suspension)
    (stepped : Step action label (copyRule job input reads source operation resume event) before after) :
    Has after.present (.waiting job ⟨input,reads,.edit source operation resume⟩) := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  exact Selected.kept_rows valid _ (by simp [copyRule])

/-- The lift follows the given heap trace, keeping the actual intermediate
worlds and the waiting control. It does not restart a copy from an encoding. -/
theorem copy_execution_lifts {job source : Nat} {events : List (SnapshotCopy.Event Suspension)}
    {heapBefore heapAfter : SnapshotCopy.World Suspension}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (execution : SnapshotCopy.Execution job source job events heapBefore heapAfter) :
    ∀ before : World, heapWorld before = heapBefore → action.Consistent before.equations →
      Has before.present (.waiting job ⟨input,reads,.edit source operation resume⟩) →
      ∃ after, Relation.ReflTransGen
        (fun first second => ∃ event : SnapshotCopy.Event Suspension,
          Step action label (copyRule job input reads source operation resume event) first second) before after ∧
        heapWorld after = heapAfter ∧ action.Consistent after.equations ∧
          Has after.present (.waiting job ⟨input,reads,.edit source operation resume⟩) := by
  induction execution with
  | nil world =>
      intro before projected consistent waiting
      exact ⟨before,.refl,projected,consistent,waiting⟩
  | cons event token firing rest ih =>
      intro before projected consistent waiting
      have heapStep := firing.ordinary
      rw [← projected] at heapStep
      obtain ⟨middle,step,projectedMiddle⟩ := copy_lifts job input reads source operation resume event consistent waiting heapStep
      have waitingMiddle := copy_keeps_waiting job input reads source operation resume event step
      obtain ⟨after,path,projectedAfter,consistentAfter,waitingAfter⟩ :=
        ih middle projectedMiddle step.consistent waitingMiddle
      exact ⟨after,(Relation.ReflTransGen.single ⟨event,step⟩).trans path,
        projectedAfter,consistentAfter,waitingAfter⟩

/-- The exact requested operation has an admitted fused commit. The source
store is used only to prove that the required physical rows are available. -/
theorem commit_exists (before : World) (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (store : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Store)
    (consistent : action.Consistent before.equations)
    (represented : NeedStoreOperations.Editable (heapWorld before).present job job store)
    (waiting : Has before.present (.waiting job ⟨input,reads,.edit source operation resume⟩)) :
    ∃ event : NeedStoreOperations.Event, ∃ after, event.operation = operation ∧
      Step action label (commitRule job input reads source resume event) before after := by
  let event := operation.eventFor store
  have matched := operation.eventFor_matches store
  have atOperation := operation.eventFor_operation store
  change event.operation = operation at atOperation
  obtain ⟨heapAfter,heapStep⟩ := NeedStoreOperations.step_exists represented event matched (heap_consistent consistent)
  obtain ⟨heapPicked,heapValid,_⟩ := heapStep
  have takeAvailable : ∀ row ∈ (commitRule job input reads source resume event).take, Has before.present row := by
    intro row member
    simp only [commitRule,List.mem_cons] at member
    rcases member with rfl | heapMember
    · simpa only [atOperation] using waiting
    · obtain ⟨heap,selected,rfl⟩ := List.mem_map.mp heapMember
      exact (has_heap_iff before.present heap).mpr (NeedStoreOperations.Ground.taken_rows heapValid heap selected)
  have readAvailable : ∀ row ∈ (commitRule job input reads source resume event).read, Has before.present row := by
    intro row member
    obtain ⟨heap,selected,rfl⟩ := List.mem_map.mp member
    exact (has_heap_iff before.present heap).mpr (NeedStoreOperations.Ground.read_rows heapValid heap selected)
  obtain ⟨taken,takePresent,takeLabels⟩ := GuardedMultisetRewriting.exists_list_of_mem label before.present
    (commitRule job input reads source resume event).take takeAvailable
  have distinct : taken.Nodup := List.Nodup.of_map label (takeLabels.symm ▸
    (by cases event <;> simp [commitRule,NeedStoreOperations.Event.rule]))
  have apart : ∀ row ∈ (commitRule job input reads source resume event).take,
      row ∉ (commitRule job input reads source resume event).read := by
    cases event <;> simp [commitRule,NeedStoreOperations.Event.rule]
  obtain ⟨picked,_,valid⟩ := ExactInteractionExecution.selection action
    (commitRule job input reads source resume event).take (commitRule job input reads source resume event).read
    (commitRule job input reads source resume event).produce before consistent taken distinct takePresent takeLabels
    readAvailable (by intro occurrence _ read takenHere
                      have valueTaken : label occurrence ∈ (commitRule job input reads source resume event).take := by
                        rw [← takeLabels]
                        exact List.mem_map.mpr ⟨occurrence,takenHere,rfl⟩
                      exact apart _ valueTaken read)
  exact ⟨event,picked.result label _ before,atOperation,⟨picked,valid,rfl⟩⟩

def StorageAt (name : Nat) : SnapshotCopy.Row Suspension → Prop
  | .allocated snapshot | .ready snapshot | .metadata snapshot _ _ | .cell snapshot _ _ => snapshot = name
  | _ => False

/-- Snapshot interpretation depends only on the physical storage rows for
that name; unrelated control rows may be inserted or removed. -/
theorem snapshot_transfer {before after : Finset (SnapshotCopy.Occurrence Suspension)}
    {name : Nat} {values : List Suspension} {trace : List Nat}
    (same : ∀ occurrence, StorageAt name (SnapshotCopy.label occurrence) → (occurrence ∈ before ↔ occurrence ∈ after))
    (snapshot : SnapshotCopy.Snapshot before name values trace) : SnapshotCopy.Snapshot after name values trace := by
  have has : ∀ row, StorageAt name row → (SnapshotCopy.Has before row ↔ SnapshotCopy.Has after row) := by
    intro row stored
    constructor
    · rintro ⟨occurrence,present,labelEq⟩
      exact ⟨occurrence,(same occurrence (labelEq.symm ▸ stored)).mp present,labelEq⟩
    · rintro ⟨occurrence,present,labelEq⟩
      exact ⟨occurrence,(same occurrence (labelEq.symm ▸ stored)).mpr present,labelEq⟩
  refine ⟨(has (.allocated name) rfl).mp snapshot.allocated,
    ⟨(has (.metadata name values.length trace) rfl).mp snapshot.metadata.present,?_⟩,
    (has (.ready name) rfl).mp snapshot.ready,⟨?_,?_⟩⟩
  · intro count history present
    exact snapshot.metadata.agreement count history ((has (.metadata name count history) rfl).mpr present)
  · intro index value
    exact (has (.cell name index value) rfl).symm.trans (snapshot.cells.exact index value)
  · intro first firstHere second secondHere index firstValue secondValue firstLabel secondLabel
    exact snapshot.cells.unique first ((same first (by rw [firstLabel]; rfl)).mpr firstHere)
      second ((same second (by rw [secondLabel]; rfl)).mpr secondHere)
      index firstValue secondValue firstLabel secondLabel

private theorem copy_storage_untouched (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat) (operation : NeedStoreOperations.Operation)
    (resume : NeedControl.Resume) (event : SnapshotCopy.Event Suspension) (other : Nat) (different : other ≠ job)
    (row : SnapshotCopy.Row Suspension) (stored : StorageAt other row) :
    Row.heap row ∉ (copyRule job input reads source operation resume event).take ∧
      Row.heap row ∉ (copyRule job input reads source operation resume event).produce := by
  cases event <;> cases row <;>
    simp_all [StorageAt,copyRule,SnapshotCopy.Event.rule,SnapshotCopy.beginRule,SnapshotCopy.copyRule,SnapshotCopy.finishRule]

theorem copy_preserves_other_snapshot {before after : World} {other : Nat} {values : List Suspension} {trace : List Nat}
    (job : Nat) (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume) (event : SnapshotCopy.Event Suspension)
    (different : other ≠ job) (snapshot : SnapshotCopy.Snapshot (heapWorld before).present other values trace)
    (stepped : Step action label (copyRule job input reads source operation resume event) before after) :
    SnapshotCopy.Snapshot (heapWorld after).present other values trace := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  apply snapshot_transfer ?_ snapshot
  intro occurrence stored
  have untouched := copy_storage_untouched job input reads source operation resume event other different
    (SnapshotCopy.label occurrence) stored
  simp only [heapWorld,mem_heapPresent]
  exact (Selected.occurrence_untouched valid (embedHeap occurrence) untouched.1 untouched.2).symm

theorem start_preserves_snapshots {program : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Program}
    {before after : World} {name : Nat} {values : List Suspension} {trace : List Nat}
    (next : Nat) (intent : NeedControl.Intent program)
    (snapshot : SnapshotCopy.Snapshot (heapWorld before).present name values trace)
    (stepped : Step action label (startRule next intent) before after) :
    SnapshotCopy.Snapshot (heapWorld after).present name values trace := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  apply snapshot_transfer ?_ snapshot
  intro occurrence stored
  have untouched : Row.heap (SnapshotCopy.label occurrence) ∉ (startRule next intent).take ∧
      Row.heap (SnapshotCopy.label occurrence) ∉ (startRule next intent).produce := by
    rcases occurrence with ⟨index,row⟩
    change StorageAt name row at stored
    cases selected : intent.plan.action <;> cases row <;>
      simp_all [StorageAt,startRule,label,SnapshotCopy.label,IndexedOccurrences.label]
  simp only [heapWorld,mem_heapPresent]
  exact (Selected.occurrence_untouched valid (embedHeap occurrence) untouched.1 untouched.2).symm

theorem copy_path_preserves_other {before after : World} {other : Nat} {values : List Suspension} {trace : List Nat}
    (job : Nat) (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume) (different : other ≠ job)
    (snapshot : SnapshotCopy.Snapshot (heapWorld before).present other values trace)
    (path : Relation.ReflTransGen (fun first second => ∃ event : SnapshotCopy.Event Suspension,
      Step action label (copyRule job input reads source operation resume event) first second) before after) :
    SnapshotCopy.Snapshot (heapWorld after).present other values trace := by
  induction path with
  | refl => exact snapshot
  | tail earlier edge ih =>
      obtain ⟨event,step⟩ := edge
      exact copy_preserves_other_snapshot job input reads source operation resume event different ih step

/-- A waiting edit completes through actual controlled copying and one
fused commit. The original source store is retained and the resumed control
names the new edited store. This is a general block theorem, independent
of the size and contents of the represented store. -/
theorem edit_block_completes (program : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Program)
    (before : World) (job source : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (store : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Store)
    (consistent : action.Consistent before.equations)
    (snapshot : SnapshotCopy.Snapshot (heapWorld before).present source store.cells store.trace)
    (fresh : SnapshotCopy.Fresh (heapWorld before).present job)
    (request : Has before.present (.heap (.request job source)))
    (waiting : Has before.present (.waiting job ⟨input,reads,.edit source operation resume⟩)) :
    ∃ after, Path program before after ∧
      SnapshotCopy.Snapshot (heapWorld after).present source store.cells store.trace ∧
      SnapshotCopy.Snapshot (heapWorld after).present job (operation.apply store).cells (operation.apply store).trace ∧
      Has after.present (.control (job+1) (NeedControl.resumeAt job resume)) ∧
      ¬ Has after.present (.heap (.reply job job)) ∧
      ∀ other, other ≠ job → ∀ values trace,
        SnapshotCopy.Snapshot (heapWorld before).present other values trace →
        SnapshotCopy.Snapshot (heapWorld after).present other values trace := by
  obtain ⟨requestId,requestHere,atRequest⟩ := (has_heap_iff before.present (.request job source)).mp request
  obtain ⟨heapCopied,events,copying,_,parent,editable⟩ := NeedStoreOperations.copy_for_editing
    (heapWorld before) job source job store snapshot fresh requestId requestHere atRequest (heap_consistent consistent)
  obtain ⟨copied,copyPath,projected,copiedConsistent,waitingCopied⟩ :=
    copy_execution_lifts input reads operation resume copying before rfl consistent waiting
  have editableCopied : NeedStoreOperations.Editable (heapWorld copied).present job job store := by
    rw [projected]
    exact editable
  have parentCopied : SnapshotCopy.Snapshot (heapWorld copied).present source store.cells store.trace := by
    rw [projected]
    exact parent
  obtain ⟨event,after,atOperation,commit⟩ := commit_exists copied job input reads source operation resume store
    copiedConsistent editableCopied waitingCopied
  have distinct : source ≠ job := by
    intro same
    subst job
    exact fresh.not_has (.allocated source) (by simp [SnapshotCopy.Row.mentions]) snapshot.allocated
  have retained := commit_other_snapshot_preserved input reads resume event editableCopied distinct parentCopied commit
  have result := commit_heap_preserved input reads resume event editableCopied commit
  have active := commit_outputs_control job input reads source resume event commit
  have copyRun : Path program before copied := by
    apply Relation.ReflTransGen.mono ?_ before copied copyPath
    intro first second edge
    obtain ⟨copiedEvent,step⟩ := edge
    exact ⟨copyRule job input reads source operation resume copiedEvent,.copy _ _ _ _ _ _ _,step⟩
  refine ⟨after,copyRun.trans (Relation.ReflTransGen.single
    ⟨commitRule job input reads source resume event,.commit _ _ _ _ _ _,commit⟩),retained,?_,active,?_,?_⟩
  · simpa only [atOperation] using result.1
  · intro reply
    exact result.2.2 ((has_heap_iff after.present (.reply job job)).mp reply)
  · intro other different values trace old
    have inCopied := copy_path_preserves_other job input reads source operation resume different old copyPath
    exact commit_other_snapshot_preserved input reads resume event editableCopied different inCopied commit

theorem no_infinite_controlled_copy {before : World} {job source index remaining : Nat}
    {token : SnapshotCopy.Occurrence Suspension} {values : List Suspension} {trace : List Nat}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (progress : SnapshotCopy.Progress (heapWorld before) job source job values trace index remaining token) :
    ¬ ∃ worlds : Nat → World, worlds 0 = before ∧
      ∀ n, ∃ event : SnapshotCopy.Event Suspension,
        Step action label (copyRule job input reads source operation resume event) (worlds n) (worlds (n+1)) := by
  rintro ⟨worlds,start,steps⟩
  apply SnapshotCopy.no_infinite_copy progress
  refine ⟨fun n => heapWorld (worlds n),congrArg heapWorld start,?_⟩
  intro n
  obtain ⟨event,step⟩ := steps n
  exact ⟨event,copy_projects job input reads source operation resume event step⟩

theorem waiting_step_is_copy {program : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Program}
    {before after : World} (job : Nat) (input : NeedControl.Control Nat)
    (reads : List (SnapshotCopy.Row Suspension)) (source : Nat)
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (single : controllerCount before = 1)
    (waitingBefore : Has before.present (.waiting job ⟨input,reads,.edit source operation resume⟩))
    (waitingAfter : Has after.present (.waiting job ⟨input,reads,.edit source operation resume⟩))
    (execution : Executes program before after) :
    ∃ event : SnapshotCopy.Event Suspension, Step action label (copyRule job input reads source operation resume event) before after := by
  obtain ⟨otherInput,otherReads,otherSource,otherOperation,otherResume,same,edge⟩ :=
    waiting_step_matches_plan job _ single waitingBefore execution
  obtain ⟨rfl,rfl,actionEq⟩ := NeedControl.Plan.mk.inj same
  obtain ⟨rfl,rfl,rfl⟩ := NeedControl.Action.edit.inj actionEq
  rcases edge with copy | ⟨event,_,commit⟩
  · exact copy
  · have active := commit_outputs_control job _ _ _ _ event commit
    have singleAfter := execution.controller_count.trans single
    have impossible := controller_unique singleAfter waitingAfter active rfl rfl
    cases impossible

/-- The entire generated catalogue, not merely a preselected copy family,
cannot spin forever while retaining one prepared waiting edit. -/
theorem no_infinite_waiting {program : Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Program}
    {before : World} {job source index remaining : Nat} {token : SnapshotCopy.Occurrence Suspension}
    {values : List Suspension} {trace : List Nat}
    (input : NeedControl.Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (operation : NeedStoreOperations.Operation) (resume : NeedControl.Resume)
    (single : controllerCount before = 1)
    (progress : SnapshotCopy.Progress (heapWorld before) job source job values trace index remaining token) :
    ¬ ∃ worlds : Nat → World, worlds 0 = before ∧
      (∀ n, Has (worlds n).present (.waiting job ⟨input,reads,.edit source operation resume⟩)) ∧
      ∀ n, Executes program (worlds n) (worlds (n+1)) := by
  rintro ⟨worlds,start,waiting,steps⟩
  have singles : ∀ n, controllerCount (worlds n) = 1 := by
    intro n
    induction n with
    | zero => simpa only [start] using single
    | succ n ih => exact (steps n).controller_count.trans ih
  apply no_infinite_controlled_copy input reads operation resume progress
  refine ⟨worlds,start,?_⟩
  intro n
  exact waiting_step_is_copy job input reads source operation resume (singles n) (waiting n) (waiting (n+1)) (steps n)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine
