import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyInvariant
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControlReferences

/-!
# Published-store and active-control invariants

Only the finite allocated prefix needs a physical store interpretation.
Running controls refer into that prefix and leave no auxiliary heap token.
Waiting controls retain the actual instruction plan and its original data
admission, together with the bounded copying phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Program Store Suspension)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def Published (world : World) (next : Nat) (stores : Nat → Store) : Prop :=
  ∀ name, name < next → SnapshotCopy.Snapshot (heapWorld world).present name (stores name).cells (stores name).trace

structure Running (world : World) (next : Nat) (stores : Nat → Store) (control : Control Nat) : Prop where
  consistent : action.Consistent world.equations
  single : controllerCount world = 1
  active : Has world.present (.control next control)
  bounded : ∀ name ∈ control.names, name < next
  published : Published world next stores
  frame : NeedHeapFrames.Frame next none (heapWorld world).present

structure Waiting {program : Program} (world : World) (job : Nat) (stores : Nat → Store)
    (intent : Intent program) (source : Nat) (operation : NeedStoreOperations.Operation)
    (resume : Resume) (rank : Nat) : Prop where
  consistent : action.Consistent world.equations
  single : controllerCount world = 1
  waiting : Has world.present (.waiting job intent.plan)
  bounded : ∀ name ∈ intent.plan.input.names, name < job
  published : Published world job stores
  edit : intent.plan.action = .edit source operation resume
  supported : intent.plan.Supported stores
  phase : NeedHeapFrames.CopyState (heapWorld world) job source (stores source) rank

abbrev CopyPath (job : Nat) (input : Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume) :=
  Relation.ReflTransGen (fun before after => ∃ event : SnapshotCopy.Event Suspension,
    Step action label (copyRule job input reads source operation resume event) before after)

theorem CopyPath.ordinary {program : Program} {before after : World} {job source : Nat}
    {input : Control Nat} {reads : List (SnapshotCopy.Row Suspension)}
    {operation : NeedStoreOperations.Operation} {resume : Resume}
    (path : CopyPath job input reads source operation resume before after) : Path program before after := by
  apply Relation.ReflTransGen.mono ?_ before after path
  intro first second edge
  obtain ⟨event,step⟩ := edge
  exact ⟨_,.copy _ _ _ _ _ _ _,step⟩

theorem Published.start {program : Program} {before after : World} {next : Nat} {stores : Nat → Store}
    (published : Published before next stores) (intent : Intent program)
    (step : Step action label (startRule next intent) before after) : Published after next stores := by
  intro name bounded
  exact start_preserves_snapshots next intent (published name bounded) step

theorem Running.read_models {program : Program} {world : World} {next : Nat} {stores : Nat → Store}
    (intent : Intent program) (running : Running world next stores intent.plan.input) :
    ∀ name, (∃ row ∈ intent.plan.reads, name ∈ row.mentions) →
      SnapshotCopy.Snapshot (heapWorld world).present name (stores name).cells (stores name).trace := by
  rintro name ⟨row,read,mentioned⟩
  exact running.published name (running.bounded name (intent.read_names_subset row read name mentioned))

theorem Running.supported {program : Program} {before after : World} {next : Nat} {stores : Nat → Store}
    (intent : Intent program) (running : Running before next stores intent.plan.input)
    (step : Step action label (startRule next intent) before after) : intent.plan.Supported stores := by
  apply supported_of_read_rows intent (running.read_models intent)
  obtain ⟨picked,valid,_⟩ := step
  intro row member
  apply Selected.read_rows valid (.heap row)
  cases selected : intent.plan.action <;> simp [startRule,selected,member]

theorem Running.direct {program : Program} {before after : World} {next : Nat} {stores : Nat → Store}
    (intent : Intent program) (control : Control Nat) (direct : intent.plan.action = .direct control)
    (running : Running before next stores intent.plan.input)
    (step : Step action label (startRule next intent) before after) : Running after next stores control := by
  refine ⟨step.consistent,?_,direct_start_outputs next intent control direct step,
    intent.direct_names_bounded next control direct running.bounded,running.published.start intent step,?_⟩
  · exact (show Executes program before after from ⟨_,.start _ _,step⟩).controller_count.trans running.single
  · have same := direct_start_keeps_heap next intent control direct step
    change NeedHeapFrames.Frame next none (heapPresent after.present)
    rw [same]
    exact running.frame

theorem Running.read_rows {program : Program} {world : World} {next : Nat} {stores : Nat → Store}
    (intent : Intent program) (running : Running world next stores intent.plan.input)
    (supported : intent.plan.Supported stores) : ∀ row ∈ intent.plan.reads, Has world.present (.heap row) := by
  intro row member
  have models := running.read_models intent
  apply (has_heap_iff world.present row).mpr
  rcases intent.read_kind row member with ⟨name,rfl⟩ | ⟨name,count,trace,rfl⟩ | ⟨name,index,value,rfl⟩
  · exact (models name ⟨_,member,by simp [SnapshotCopy.Row.mentions]⟩).ready
  · have matched := supported _ member
    change count = (stores name).cells.length ∧ trace = (stores name).trace at matched
    obtain ⟨rfl,rfl⟩ := matched
    exact (models name ⟨_,member,by simp [SnapshotCopy.Row.mentions]⟩).metadata.present
  · exact ((models name ⟨_,member,by simp [SnapshotCopy.Row.mentions]⟩).cells.exact index value).mpr
      (supported _ member)

theorem Running.start_exists {program : Program} {world : World} {next : Nat} {stores : Nat → Store}
    (intent : Intent program) (running : Running world next stores intent.plan.input)
    (supported : intent.plan.Supported stores) : ∃ after, Step action label (startRule next intent) world after := by
  apply NeedMachine.start_exists world next intent running.consistent running.active (running.read_rows intent supported)
  intro source operation resume _ allocated
  exact running.frame.fresh.not_has (.allocated next) (by simp [SnapshotCopy.Row.mentions])
    ((has_heap_iff world.present (.allocated next)).mp allocated)

theorem start_edit_frame {program : Program} {before after : World} {next source : Nat}
    {operation : NeedStoreOperations.Operation} {resume : Resume}
    (intent : Intent program) (edit : intent.plan.action = .edit source operation resume)
    (frame : NeedHeapFrames.Frame next none (heapWorld before).present)
    (step : Step action label (startRule next intent) before after) :
    ∃ token, token ∈ (heapWorld after).present ∧ SnapshotCopy.label token = .request next source ∧
      NeedHeapFrames.Frame next (some token) (heapWorld after).present := by
  obtain ⟨picked,valid,rfl⟩ := step
  have requested : Row.heap (.request next source) ∈ picked.made.map label := by
    rw [valid.outputs]
    simp [startRule,edit]
  obtain ⟨⟨index,row⟩,made,atRequest⟩ := List.mem_map.mp requested
  change row = .heap (.request next source) at atRequest
  subst row
  let token : SnapshotCopy.Occurrence Suspension := (index,.request next source)
  have here : token ∈ (heapWorld (picked.result label (startRule next intent) before)).present := by
    apply (mem_heapPresent _ token).mpr
    exact made_subset_fire (by simpa [Selection.commit,token,embedHeap] using made)
  refine ⟨token,here,rfl,?_⟩
  intro occurrence present
  have globalHere := (mem_heapPresent _ occurrence).mp present
  have casesHere : (embedHeap occurrence ∈ before.present ∧ embedHeap occurrence ∉ picked.taken) ∨
      embedHeap occurrence ∈ picked.made := by
    simpa only [Selection.result,fire,Selection.commit,Finset.mem_union,Finset.mem_sdiff,
      List.mem_toFinset] using globalHere
  rcases casesHere with old | created
  · rcases frame occurrence ((mem_heapPresent before.present occurrence).mpr old.1) with data | impossible
    · exact Or.inl data
    · cases impossible
  · have output : label (embedHeap occurrence) ∈ (startRule next intent).produce := by
      rw [← valid.outputs]
      exact List.mem_map.mpr ⟨_,created,rfl⟩
    simp only [startRule,edit,List.mem_cons,List.not_mem_nil,or_false] at output
    rcases output with impossible | atRequest
    · cases impossible
    · have distinct : (picked.made.map label).Nodup := by
        rw [valid.outputs]
        simp [startRule,edit]
      have same := List.inj_on_of_nodup_map distinct created made atRequest
      exact Or.inr (congrArg some (embedHeap_injective same))

theorem Running.edit {program : Program} {before after : World} {job source : Nat} {stores : Nat → Store}
    (intent : Intent program) (operation : NeedStoreOperations.Operation) (resume : Resume)
    (edit : intent.plan.action = .edit source operation resume)
    (running : Running before job stores intent.plan.input)
    (step : Step action label (startRule job intent) before after) :
    Waiting after job stores intent source operation resume ((stores source).cells.length+2) := by
  have sourceBound := running.bounded source (intent.edit_source_in source operation resume edit)
  have published := running.published.start intent step
  obtain ⟨token,here,atToken,frame⟩ := start_edit_frame intent edit running.frame step
  have fresh : SnapshotCopy.Fresh (heapWorld after).present job := by
    intro occurrence present mentions
    rcases frame occurrence present with data | same
    · exact (Nat.lt_irrefl job) (data.mentions job mentions)
    · have equal := Option.some.inj same
      subst occurrence
      rw [atToken] at mentions
      have sameName : job = source := by simpa [SnapshotCopy.Row.mentions] using mentions
      exact (Nat.ne_of_lt sourceBound) sameName.symm
  have waiting : Has after.present (.waiting job intent.plan) := by
    obtain ⟨picked,valid,rfl⟩ := step
    exact Selected.output_rows valid _ (by simp [startRule,edit])
  exact ⟨step.consistent,
    (show Executes program before after from ⟨_,.start _ _,step⟩).controller_count.trans running.single,
    waiting,running.bounded,published,edit,running.supported intent step,
    .requested token (published source sourceBound) fresh here atToken frame⟩

theorem plan_eq_edit {plan : Plan} {source : Nat} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (edit : plan.action = .edit source operation resume) :
    plan = ⟨plan.input,plan.reads,.edit source operation resume⟩ := by
  cases plan
  simp_all

theorem Waiting.copy {program : Program} {before after : World} {job source rank : Nat} {stores : Nat → Store}
    {intent : Intent program} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (waiting : Waiting before job stores intent source operation resume rank)
    (event : SnapshotCopy.Event Suspension)
    (step : Step action label (copyRule job intent.plan.input intent.plan.reads source operation resume event) before after) :
    ∃ nextRank, Waiting after job stores intent source operation resume nextRank ∧ rank = nextRank+1 := by
  obtain ⟨token,⟨firing⟩⟩ := SnapshotCopy.firing_of_step event
    (copy_projects job intent.plan.input intent.plan.reads source operation resume event step)
  obtain ⟨nextRank,phase,decreases⟩ := waiting.phase.step event firing
  refine ⟨nextRank,⟨step.consistent,?_,?_,waiting.bounded,?_,waiting.edit,waiting.supported,phase⟩,decreases⟩
  · exact (show Executes program before after from ⟨_,.copy _ _ _ _ _ _ _,step⟩).controller_count.trans waiting.single
  · rw [plan_eq_edit waiting.edit]
    exact copy_keeps_waiting job intent.plan.input intent.plan.reads source operation resume event step
  · intro name below
    exact copy_preserves_other_snapshot job intent.plan.input intent.plan.reads source operation resume event
      (Nat.ne_of_lt below) (waiting.published name below) step

theorem Waiting.commit {program : Program} {before after : World} {job source rank : Nat} {stores : Nat → Store}
    {intent : Intent program} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (waiting : Waiting before job stores intent source operation resume rank)
    (event : NeedStoreOperations.Event) (requested : event.operation = operation)
    (step : Step action label (commitRule job intent.plan.input intent.plan.reads source resume event) before after) :
    rank = 0 ∧ Running after (job+1) (Function.update stores job (operation.apply (stores source))) (resumeAt job resume) := by
  have heapStep := commit_projects job intent.plan.input intent.plan.reads source resume event step
  have replied : SnapshotCopy.Has (heapWorld before).present (.reply job job) := by
    obtain ⟨picked,valid,_⟩ := heapStep
    exact NeedStoreOperations.Ground.taken_rows valid _
      (by cases event <;> simp [NeedStoreOperations.Event.publishedRule,NeedStoreOperations.Event.rule])
  obtain ⟨rankEq,token,completed,_,_,frame⟩ := waiting.phase.completed_of_reply replied
  have editable := NeedStoreOperations.editable_of_completed completed
  have edited := commit_heap_preserved intent.plan.input intent.plan.reads resume event editable step
  refine ⟨rankEq,⟨step.consistent,?_,commit_outputs_control job intent.plan.input intent.plan.reads source resume event step,
    intent.resumed_names_bounded job source operation resume waiting.edit waiting.bounded,?_,
    frame.after_publication event heapStep⟩⟩
  · exact (show Executes program before after from ⟨_,.commit _ _ _ _ _ _,step⟩).controller_count.trans waiting.single
  · intro name below
    by_cases same : name = job
    · subst name
      simpa [requested] using edited.1
    · have oldBound : name < job := by omega
      rw [Function.update_of_ne same]
      exact commit_other_snapshot_preserved intent.plan.input intent.plan.reads resume event editable same
        (waiting.published name oldBound) step

/-- Proof-side interpretation data. The finite physical allocation prefix
is certified; the total mathematical map is used only for decoding. -/
inductive Witness (program : Program) (world : World) where
  | running (next : Nat) (stores : Nat → Store) (control : Control Nat)
      (valid : Running world next stores control)
  | waiting (job : Nat) (stores : Nat → Store) (intent : Intent program)
      (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume) (rank : Nat)
      (valid : Waiting world job stores intent source operation resume rank)

def Witness.decode {program : Program} {world : World} : Witness program world →
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control
  | .running _ stores control _ => control.decode stores
  | .waiting _ stores intent _ _ _ _ _ => intent.plan.action.decode stores

/-- Copy work includes the final publication transition. -/
def Witness.copyRank {program : Program} {world : World} : Witness program world → Nat
  | .running _ _ _ _ => 0
  | .waiting _ _ _ _ _ _ rank _ => rank+1

/-- Every generated firing either realizes an independent source
instruction or strictly decreases remaining internal work while preserving
the complete source control. The successor witness is constructed from the
actual target world. -/
theorem Witness.step {program : Program} {before after : World} (witness : Witness program before)
    (execution : Executes program before after) :
    ∃ target : Witness program after,
      (witness.copyRank = 0 ∧
        Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Instruction program witness.decode target.decode) ∨
        (target.decode = witness.decode ∧ target.copyRank < witness.copyRank) := by
  cases witness with
  | running next stores control valid =>
      obtain ⟨intent,input,step⟩ := running_step_is_start next control valid.single valid.active execution
      subst control
      have sourceStep := start_source_instruction next intent (valid.read_models intent) step
      cases selected : intent.plan.action with
      | direct control =>
          refine ⟨.running next stores control (valid.direct intent control selected step),Or.inl ⟨rfl,?_⟩⟩
          simpa only [Witness.decode,selected,Action.decode] using sourceStep
      | edit source operation resume =>
          exact ⟨.waiting next stores intent source operation resume ((stores source).cells.length+2)
            (valid.edit intent operation resume selected step),Or.inl ⟨rfl,sourceStep⟩⟩
  | waiting job stores intent source operation resume rank valid =>
      obtain ⟨otherInput,otherReads,otherSource,otherOperation,otherResume,same,edge⟩ :=
        waiting_step_matches_plan job intent.plan valid.single valid.waiting execution
      obtain ⟨rfl,rfl,actionEq⟩ := Plan.mk.inj ((plan_eq_edit valid.edit).symm.trans same)
      obtain ⟨rfl,rfl,rfl⟩ := Action.edit.inj actionEq
      rcases edge with ⟨event,copy⟩ | ⟨event,requested,commit⟩
      · obtain ⟨nextRank,nextValid,decreases⟩ := valid.copy event copy
        refine ⟨.waiting job stores intent source operation resume nextRank nextValid,Or.inr ⟨rfl,?_⟩⟩
        change nextRank+1 < rank+1
        omega
      · have finished := valid.commit event requested commit
        refine ⟨.running (job+1) (Function.update stores job (operation.apply (stores source)))
          (resumeAt job resume) finished.2,Or.inr ⟨?_,?_⟩⟩
        · exact intent.resume_interpretation stores job source operation resume valid.edit valid.bounded
        · change 0 < rank+1
          omega

/-- All finite catalogue paths retain a valid interpretation and project
to an actual finite source-instruction path. Administrative states remain
in the physical path rather than being reconstructed from an endpoint. -/
theorem Witness.path {program : Program} {before after : World} (witness : Witness program before)
    (path : Path program before after) :
    ∃ target : Witness program after,
      Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Path program witness.decode target.decode := by
  induction path with
  | refl => exact ⟨witness,.refl⟩
  | tail earlier edge ih =>
      obtain ⟨middle,sourcePath⟩ := ih
      obtain ⟨target,progress⟩ := middle.step edge
      refine ⟨target,?_⟩
      rcases progress with ⟨_,instruction⟩ | ⟨same,_⟩
      · exact sourcePath.tail instruction
      · rw [same]
        exact sourcePath

/-- A path consisting only of this job's actual copying rules retains its
original plan and source-store interpretation. -/
theorem Waiting.copy_path {program : Program} {before after : World} {job source rank : Nat} {stores : Nat → Store}
    {intent : Intent program} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (waiting : Waiting before job stores intent source operation resume rank)
    (path : CopyPath job intent.plan.input intent.plan.reads source operation resume before after) :
    ∃ nextRank, Waiting after job stores intent source operation resume nextRank := by
  induction path with
  | refl => exact ⟨rank,waiting⟩
  | tail earlier edge ih =>
      obtain ⟨middleRank,middle⟩ := ih
      obtain ⟨event,step⟩ := edge
      obtain ⟨nextRank,ready,_⟩ := middle.copy event step
      exact ⟨nextRank,ready⟩

/-- The copy-only prefix is exposed for comparisons at source-action
granularity. It contains no new instruction start or final commit. -/
theorem Waiting.copy_to_completion {program : Program} {before : World} {job source rank : Nat} {stores : Nat → Store}
    {intent : Intent program} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (waiting : Waiting before job stores intent source operation resume rank) :
    ∃ after, CopyPath job intent.plan.input intent.plan.reads source operation resume before after ∧
      Waiting after job stores intent source operation resume 0 := by
  induction rank using Nat.strong_induction_on generalizing before with
  | h rank ih =>
      have waitingRow : Has before.present (.waiting job ⟨intent.plan.input,intent.plan.reads,.edit source operation resume⟩) := by
        rw [← plan_eq_edit waiting.edit]
        exact waiting.waiting
      by_cases done : rank = 0
      · subst rank
        exact ⟨before,.refl,waiting⟩
      · obtain ⟨event,heapAfter,heapStep⟩ := waiting.phase.progress (Nat.pos_of_ne_zero done)
          (heap_consistent waiting.consistent)
        obtain ⟨middle,step,_⟩ := copy_lifts job intent.plan.input intent.plan.reads source operation resume event
          waiting.consistent waitingRow heapStep
        obtain ⟨nextRank,middleValid,decreases⟩ := waiting.copy event step
        obtain ⟨after,path,ready⟩ := ih nextRank (by omega) middleValid
        exact ⟨after,(Relation.ReflTransGen.single ⟨event,step⟩).trans path,ready⟩

/-- An entire pending edit completes into the next running invariant.
The induction follows the actual per-cell work count, not a whole-store
transition hidden in the rule catalogue. -/
theorem Waiting.completes {program : Program} {before : World} {job source rank : Nat} {stores : Nat → Store}
    {intent : Intent program} {operation : NeedStoreOperations.Operation} {resume : Resume}
    (waiting : Waiting before job stores intent source operation resume rank) :
    ∃ after, Path program before after ∧
      Running after (job+1) (Function.update stores job (operation.apply (stores source))) (resumeAt job resume) := by
  obtain ⟨copied,copies,ready⟩ := waiting.copy_to_completion
  have waitingRow : Has copied.present (.waiting job ⟨intent.plan.input,intent.plan.reads,.edit source operation resume⟩) := by
    rw [← plan_eq_edit ready.edit]
    exact ready.waiting
  obtain ⟨_,token,completed,_,_,_⟩ := ready.phase.completed_of_reply ready.phase.zero_replied
  have editable := NeedStoreOperations.editable_of_completed completed
  obtain ⟨event,after,requested,step⟩ := commit_exists copied job intent.plan.input intent.plan.reads source
    operation resume (stores source) ready.consistent editable waitingRow
  exact ⟨after,copies.ordinary.trans (Relation.ReflTransGen.single ⟨_,.commit _ _ _ _ _ _,step⟩),
    (ready.commit event requested step).2⟩

theorem Running.realize_instruction {program : Program} {before : World} {next : Nat} {stores : Nat → Store}
    {control : Control Nat} (running : Running before next stores control)
    (target : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control)
    (instruction : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Instruction program
      (control.decode stores) target) :
    ∃ after next' stores' control', Path program before after ∧ Running after next' stores' control' ∧
      control'.decode stores' = target := by
  obtain ⟨intent,input,supported,output⟩ :=
    (source_instruction_iff_supported_plan program stores control target).mp instruction
  subst control
  obtain ⟨middle,step⟩ := running.start_exists intent supported
  have started : Path program before middle := Relation.ReflTransGen.single ⟨_,.start _ _,step⟩
  cases selected : intent.plan.action with
  | direct control =>
      refine ⟨middle,next,stores,control,started,running.direct intent control selected step,?_⟩
      simpa only [selected,Action.decode] using output
  | edit source operation resume =>
      have waiting := running.edit intent operation resume selected step
      obtain ⟨after,completion,ready⟩ := waiting.completes
      exact ⟨after,next+1,Function.update stores next (operation.apply (stores source)),resumeAt next resume,
        started.trans completion,ready,
        (intent.resume_interpretation stores next source operation resume selected running.bounded).trans output⟩

/-- Every finite independently specified instruction path has a physical
ordinary-rule realization ending in the corresponding running state. -/
theorem Running.realize_path {program : Program} {before : World} {next : Nat} {stores : Nat → Store}
    {control : Control Nat} (running : Running before next stores control)
    (target : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control)
    (path : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Path program (control.decode stores) target) :
    ∃ after next' stores' control', Path program before after ∧ Running after next' stores' control' ∧
      control'.decode stores' = target := by
  induction path with
  | refl => exact ⟨before,next,stores,control,.refl,running,rfl⟩
  | tail earlier instruction ih =>
      obtain ⟨middle,next',stores',control',executed,valid,decoded⟩ := ih
      rw [← decoded] at instruction
      obtain ⟨after,next'',stores'',control'',continued,ready,result⟩ := valid.realize_instruction _ instruction
      exact ⟨after,next'',stores'',control'',executed.trans continued,ready,result⟩

theorem snapshot_store_unique {present : Finset (SnapshotCopy.Occurrence Suspension)} {name : Nat}
    {first second : Store}
    (left : SnapshotCopy.Snapshot present name first.cells first.trace)
    (right : SnapshotCopy.Snapshot present name second.cells second.trace) : first = second := by
  have traceEq := (left.metadata.agreement second.cells.length second.trace right.metadata.present).2.symm
  have cellsEq : first.cells = second.cells := by
    apply List.ext_getElem?
    intro index
    cases leftValue : first.cells[index]? with
    | none =>
        cases rightValue : second.cells[index]? with
        | none => rfl
        | some value =>
            have found := (left.cells.exact index value).mp ((right.cells.exact index value).mpr rightValue)
            rw [leftValue] at found
            cases found
    | some value =>
        have found := (right.cells.exact index value).mp ((left.cells.exact index value).mpr leftValue)
        exact found.symm
  cases first
  cases second
  cases cellsEq
  cases traceEq
  rfl

/-- Different mathematical model functions cannot give different source
controls at a running endpoint: all references lie in its represented
prefix, whose actual metadata and cells fix the store values. -/
theorem Witness.agrees_running {program : Program} {world : World} {next : Nat} {stores : Nat → Store}
    {control : Control Nat} (witness : Witness program world) (running : Running world next stores control) :
    witness.decode = control.decode stores := by
  cases witness with
  | running otherNext otherStores otherControl valid =>
      obtain ⟨counter,body⟩ := Row.control.inj (controller_unique running.single running.active valid.active rfl rfl)
      subst otherNext
      subst otherControl
      apply Control.decode_congr
      intro name member
      have bound := running.bounded name member
      exact snapshot_store_unique (valid.published name bound) (running.published name bound)
  | waiting job oldStores intent source operation resume rank valid =>
      have impossible := controller_unique running.single running.active valid.waiting rfl rfl
      cases impossible

/-- Two-way finite-path adequacy for the complete fixed-program instruction
grammar and its physical ordinary-rule realization, at running boundaries.
The target path retains its administrative worlds and equations. -/
theorem Running.source_path_iff {program : Program} {before : World} {next : Nat} {stores : Nat → Store}
    {control : Control Nat} (running : Running before next stores control)
    (target : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control) :
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Path program (control.decode stores) target ↔
      ∃ after next' stores' control', Path program before after ∧ Running after next' stores' control' ∧
        control'.decode stores' = target := by
  constructor
  · exact running.realize_path target
  · rintro ⟨after,next',stores',control',actual,ready,decoded⟩
    obtain ⟨witness,sourcePath⟩ := (Witness.running next stores control running).path actual
    have same := witness.agrees_running ready
    change Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Path program
      (control.decode stores) witness.decode at sourcePath
    rw [same,decoded] at sourcePath
    exact sourcePath

theorem intent_action_decode_congr {program : Program} (intent : Intent program) (first second : Nat → Store)
    (agree : ∀ name ∈ intent.plan.input.names, first name = second name) :
    intent.plan.action.decode first = intent.plan.action.decode second := by
  cases selected : intent.plan.action with
  | direct control =>
      apply Control.decode_congr
      intro name member
      apply agree name
      apply intent.old_names_subset name
      simpa only [selected,Action.oldNames] using member
  | edit source operation resume =>
      apply Control.decode_congr
      intro name member
      cases name with
      | none =>
          exact congrArg operation.apply (agree source (intent.edit_source_in source operation resume selected))
      | some old =>
          apply agree old
          apply intent.old_names_subset old
          rw [selected]
          exact List.mem_filterMap.mpr ⟨some old,member,rfl⟩

/-- Interpretation and remaining copy work are fixed by the physical
world, not by a choice of proof-side model witness. -/
theorem Witness.unique {program : Program} {world : World} (first second : Witness program world) :
    first.decode = second.decode ∧ first.copyRank = second.copyRank := by
  cases first with
  | running next stores control valid =>
      cases second with
      | running otherNext otherStores otherControl otherValid =>
          exact ⟨(Witness.running otherNext otherStores otherControl otherValid).agrees_running valid |>.symm,rfl⟩
      | waiting job otherStores intent source operation resume rank otherValid =>
          have impossible := controller_unique valid.single valid.active otherValid.waiting rfl rfl
          cases impossible
  | waiting job stores intent source operation resume rank valid =>
      cases second with
      | running next otherStores control otherValid =>
          have impossible := controller_unique valid.single valid.waiting otherValid.active rfl rfl
          cases impossible
      | waiting otherJob otherStores otherIntent otherSource otherOperation otherResume otherRank otherValid =>
          obtain ⟨jobEq,planEq⟩ := Row.waiting.inj
            (controller_unique valid.single valid.waiting otherValid.waiting rfl rfl)
          subst otherJob
          have actions := congrArg Plan.action planEq
          rw [valid.edit,otherValid.edit] at actions
          obtain ⟨sourceEq,_,_⟩ := Action.edit.inj actions
          subst otherSource
          refine ⟨?_,congrArg (fun n => n+1) (valid.phase.rank_unique otherValid.phase)⟩
          change intent.plan.action.decode stores = otherIntent.plan.action.decode otherStores
          rw [← planEq]
          apply intent_action_decode_congr
          intro name member
          have below := valid.bounded name member
          exact snapshot_store_unique (valid.published name below) (otherValid.published name below)

abbrev CertifiedState (program : Program) := (world : World) × Witness program world

def CertifiedState.decode {program : Program} (state : CertifiedState program) := state.2.decode

def CertifiedState.rank {program : Program} (state : CertifiedState program) : (Nat × Nat) × Nat :=
  (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.administrativeRank state.decode,state.2.copyRank)

def AdministrativeRankLT : ((Nat × Nat) × Nat) → ((Nat × Nat) × Nat) → Prop :=
  Prod.Lex (Prod.Lex (· < ·) (· < ·)) (· < ·)

/-- Across all generated rules, an administrative transition either
decreases the source continuation rank or preserves it and decreases the
remaining copy/publication work. -/
theorem administrative_step_decreases {program : Program} (before after : CertifiedState program)
    (step : Executes program before.1 after.1)
    (administrative : 0 < before.2.copyRank ∨
      (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork before.decode = false ∧
        Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork after.decode = false)) :
    AdministrativeRankLT after.rank before.rank := by
  obtain ⟨target,progress⟩ := before.2.step step
  have same := target.unique after.2
  rcases progress with ⟨notCopying,instruction⟩ | ⟨decoded,decreased⟩
  · obtain ⟨beforeAdministrative,afterAdministrative⟩ :
        Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork before.decode = false ∧
          Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork after.decode = false := by
      rcases administrative with copying | source
      · omega
      · exact source
    rw [same.1] at instruction
    exact Prod.Lex.left _ _
      (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.administrative_decreases
        instruction beforeAdministrative afterAdministrative)
  · have sourceEq : after.decode = before.decode := same.1.symm.trans decoded
    have workLt : after.2.copyRank < before.2.copyRank := same.2 ▸ decreased
    change Prod.Lex (Prod.Lex (· < ·) (· < ·)) (· < ·)
      (_,after.2.copyRank) (_,before.2.copyRank)
    rw [show Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.administrativeRank after.decode =
      Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.administrativeRank before.decode from congrArg _ sourceEq]
    exact Prod.Lex.right _ workLt

/-- The complete generated machine cannot perform an infinite execution
consisting solely of source bookkeeping and its internal copy work. -/
theorem administrative_wellFounded (program : Program) :
    WellFounded (fun after before : CertifiedState program => Executes program before.1 after.1 ∧
      (0 < before.2.copyRank ∨
        (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork before.decode = false ∧
          Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.sourceWork after.decode = false))) := by
  exact Subrelation.wf (r := InvImage AdministrativeRankLT CertifiedState.rank)
    (fun {_ _} step => administrative_step_decreases _ _ step.1 step.2)
    (InvImage.wf CertifiedState.rank ((Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf).prod_lex Nat.lt_wfRel.wf))

theorem Running.no_execution_of_stuck {program : Program} {world : World} {next : Nat}
    {stores : Nat → Store} {control : Control Nat} (running : Running world next stores control)
    (stuck : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.next program (control.decode stores) = none) :
    ¬ ∃ after, Executes program world after := by
  rintro ⟨after,execution⟩
  obtain ⟨intent,input,step⟩ := running_step_is_start next control running.single running.active execution
  subst control
  have source := start_source_instruction next intent (running.read_models intent) step
  have actual := Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.next_complete source
  rw [stuck] at actual
  cases actual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine
