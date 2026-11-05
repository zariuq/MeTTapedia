import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl

/-!
# Physical instruction and snapshot rules in one occurrence world

Control and heap rows inhabit the same ordinary transform configuration.
The rule catalogue exposes instruction starts, individual copy events and
the final requested edit. A copy reads its waiting control; an edit consumes
that control together with the actual store resources. No rule calls an
instruction interpreter or carries a whole source store.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Suspension Store Program)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

inductive Row where
  | heap (row : SnapshotCopy.Row Suspension)
  | control (next : Nat) (current : Control Nat)
  | waiting (job : Nat) (plan : Plan)
  deriving DecidableEq

abbrev Occurrence := IndexedOccurrences.Occurrence Row
abbrev World := Configuration Row Occurrence
abbrev label : Occurrence → Row := IndexedOccurrences.label

/-- This instruction client uses closed data. Open contextual constraint
solving remains the existing separate, nonrigid calculus profile. -/
def action : SubstitutionAction Row Unit where
  E := Eq
  equivalence := ⟨Eq.refl,Eq.symm,Eq.trans⟩
  apply := fun _ row => row
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ {_ _} same => same

def embedHeap (occurrence : SnapshotCopy.Occurrence Suspension) : Occurrence :=
  (occurrence.1,.heap occurrence.2)

def heapPart : Occurrence → Option (SnapshotCopy.Occurrence Suspension)
  | (index,.heap row) => some (index,row)
  | _ => none

@[simp] theorem heapPart_some (occurrence : Occurrence) (heap : SnapshotCopy.Occurrence Suspension) :
    heapPart occurrence = some heap ↔ occurrence = embedHeap heap := by
  rcases occurrence with ⟨index,row⟩
  cases row <;> cases heap <;> simp [heapPart,embedHeap]

theorem embedHeap_injective : Function.Injective embedHeap := by
  intro first second same
  have equal := congrArg heapPart same
  simpa only [heapPart,embedHeap,Option.some.injEq] using equal

def heapPresent (world : Finset Occurrence) : Finset (SnapshotCopy.Occurrence Suspension) :=
  (world.val.filterMap heapPart).toFinset

@[simp] theorem mem_heapPresent (world : Finset Occurrence) (occurrence : SnapshotCopy.Occurrence Suspension) :
    occurrence ∈ heapPresent world ↔ embedHeap occurrence ∈ world := by
  simp [heapPresent,Multiset.mem_filterMap]

def heapEquation : Equation Row → Option (Equation (SnapshotCopy.Row Suspension))
  | (.heap first,.heap second) => some (first,second)
  | _ => none

def heapWorld (world : World) : SnapshotCopy.World Suspension :=
  ⟨world.equations.filterMap heapEquation,heapPresent world.present⟩

theorem heap_consistent {world : World} (consistent : action.Consistent world.equations) :
    SnapshotCopy.action.Consistent (heapWorld world).equations := by
  obtain ⟨assignment,solved⟩ := consistent
  refine ⟨(),?_⟩
  intro equation member
  obtain ⟨original,old,projects⟩ := List.mem_filterMap.mp member
  have equal : original.1 = original.2 := solved original old
  rcases original with ⟨first,second⟩
  cases first <;> cases second <;> simp only [heapEquation,Option.some.injEq,reduceCtorEq] at projects
  rename_i first second
  subst equation
  exact Row.heap.inj equal

def startRule {program : Program} (next : Nat) (intent : Intent program) : RuleInstance Row :=
  let plan := intent.plan
  match plan.action with
  | .direct after =>
      ⟨[.control next plan.input],plan.reads.map .heap,[],[],[.control next after]⟩
  | .edit source _ _ =>
      ⟨[.control next plan.input],plan.reads.map .heap,[],[.absent (.heap (.allocated next))],
        [.waiting next plan,.heap (.request next source)]⟩

def copyRule (job : Nat) (input : Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
    (event : SnapshotCopy.Event Suspension) : RuleInstance Row :=
  let plan : Plan := ⟨input,reads,.edit source operation resume⟩
  let rule := event.rule job source job
  ⟨rule.take.map .heap,rule.read.map .heap ++ [.waiting job plan],[],
    rule.checks.map (Check.map Row.heap),rule.produce.map .heap⟩

def commitRule (job : Nat) (input : Control Nat) (reads : List (SnapshotCopy.Row Suspension))
    (source : Nat) (resume : Resume) (event : NeedStoreOperations.Event) : RuleInstance Row :=
  let plan : Plan := ⟨input,reads,.edit source event.operation resume⟩
  let rule := event.rule job job
  ⟨.waiting job plan :: rule.take.map .heap,rule.read.map .heap,[],[],
    .control (job+1) (resumeAt job resume) :: rule.produce.tail.map .heap⟩

/-- The generated ordinary rule catalogue. The resource-operation rules
are admitted only together with their matching waiting control. -/
inductive Catalogue (program : Program) : RuleInstance Row → Prop where
  | start (next : Nat) (intent : Intent program) : Catalogue program (startRule next intent)
  | copy (job : Nat) (input : Control Nat) (reads : List (SnapshotCopy.Row Suspension))
      (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
      (event : SnapshotCopy.Event Suspension) :
      Catalogue program (copyRule job input reads source operation resume event)
  | commit (job : Nat) (input : Control Nat) (reads : List (SnapshotCopy.Row Suspension))
      (source : Nat) (resume : Resume) (event : NeedStoreOperations.Event) :
      Catalogue program (commitRule job input reads source resume event)

abbrev Executes (program : Program) (before after : World) : Prop :=
  ∃ rule, Catalogue program rule ∧ Step action label rule before after

abbrev Path (program : Program) := Relation.ReflTransGen (Executes program)

def Has (world : Finset Occurrence) (row : Row) : Prop :=
  ∃ occurrence ∈ world, label occurrence = row

theorem has_heap_iff (world : Finset Occurrence) (row : SnapshotCopy.Row Suspension) :
    Has world (.heap row) ↔ SnapshotCopy.Has (heapPresent world) row := by
  constructor
  · rintro ⟨⟨index,value⟩,present,same⟩
    change value = .heap row at same
    subst value
    exact ⟨(index,row),(mem_heapPresent world _).mpr present,rfl⟩
  · rintro ⟨occurrence,present,same⟩
    exact ⟨embedHeap occurrence,(mem_heapPresent world occurrence).mp present,congrArg Row.heap same⟩

namespace Selected

variable {picked : Selection Occurrence} {rule : RuleInstance Row} {before : World}

theorem input_labels (valid : picked.Valid action label rule before) :
    picked.taken.map label = rule.take ∧ picked.read.map label = rule.read :=
  ExactInteractionExecution.rigid_input_labels action (by intros; rfl) valid

theorem read_rows (valid : picked.Valid action label rule before) (row : Row)
    (member : row ∈ rule.read) : Has before.present row := by
  rw [← (input_labels valid).2] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,valid.occurrences.kept_subset (by simpa [Selection.commit] using selected),same⟩

theorem kept_rows (valid : picked.Valid action label rule before) (row : Row)
    (member : row ∈ rule.read) : Has (picked.result label rule before).present row := by
  rw [← (input_labels valid).2] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,valid.kept_survive selected,same⟩

theorem take_rows (valid : picked.Valid action label rule before) (row : Row)
    (member : row ∈ rule.take) : Has before.present row := by
  rw [← (input_labels valid).1] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,valid.occurrences.taken_subset (by simpa [Selection.commit] using selected),same⟩

theorem output_rows (valid : picked.Valid action label rule before) (row : Row)
    (member : row ∈ rule.produce) : Has (picked.result label rule before).present row := by
  rw [← valid.outputs] at member
  obtain ⟨occurrence,made,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,made_subset_fire (by simpa [Selection.commit] using made),same⟩

theorem occurrence_untouched (valid : picked.Valid action label rule before) (occurrence : Occurrence)
    (notTaken : label occurrence ∉ rule.take) (notMade : label occurrence ∉ rule.produce) :
    occurrence ∈ (picked.result label rule before).present ↔ occurrence ∈ before.present := by
  have noTake : occurrence ∉ picked.taken := by
    intro member
    apply notTaken
    rw [← (input_labels valid).1]
    exact List.mem_map.mpr ⟨occurrence,member,rfl⟩
  have noMake : occurrence ∉ picked.made := by
    intro member
    apply notMade
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨occurrence,member,rfl⟩
  simp [Selection.result,fire,Selection.commit,noTake,noMake]

end Selected

/-- A storage model is used only in the proof. Each read is justified by
the corresponding physical source snapshot at the original admission cut. -/
theorem supported_of_read_rows {world : World} {stores : Nat → Store} {program : Program}
    (intent : Intent program)
    (models : ∀ name, (∃ row ∈ intent.plan.reads, name ∈ row.mentions) →
      SnapshotCopy.Snapshot (heapWorld world).present name (stores name).cells (stores name).trace)
    (read : ∀ row ∈ intent.plan.reads, Has world.present (.heap row)) : intent.plan.Supported stores := by
  intro row member
  have present := (has_heap_iff world.present row).mp (read row member)
  rcases intent.read_kind row member with ⟨name,rfl⟩ | ⟨name,count,trace,rfl⟩ | ⟨name,index,value,rfl⟩
  · trivial
  · exact (models name ⟨_,member,by simp [SnapshotCopy.Row.mentions]⟩).metadata.agreement count trace present
  · exact ((models name ⟨_,member,by simp [SnapshotCopy.Row.mentions]⟩).cells.exact index value).mp present

theorem start_source_instruction {program : Program} {before after : World} {stores : Nat → Store}
    (next : Nat) (intent : Intent program)
    (models : ∀ name, (∃ row ∈ intent.plan.reads, name ∈ row.mentions) →
      SnapshotCopy.Snapshot (heapWorld before).present name (stores name).cells (stores name).trace)
    (stepped : Step action label (startRule next intent) before after) :
    Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Instruction program
      (intent.plan.input.decode stores) (intent.plan.action.decode stores) := by
  obtain ⟨picked,valid,_⟩ := stepped
  apply intent.source_step stores
  apply supported_of_read_rows intent models
  intro row member
  apply Selected.read_rows valid (.heap row)
  cases selected : intent.plan.action <;> simp [startRule,selected,member]

/-- Source availability constructs an actual start firing with fresh
physical outputs. The edit case retains the original absence admission cut. -/
theorem start_exists {program : Program} (before : World) (next : Nat) (intent : Intent program)
    (consistent : action.Consistent before.equations)
    (current : Has before.present (.control next intent.plan.input))
    (reads : ∀ row ∈ intent.plan.reads, Has before.present (.heap row))
    (fresh : ∀ source operation resume, intent.plan.action = .edit source operation resume →
      ¬ Has before.present (.heap (.allocated next))) :
    ∃ after, Step action label (startRule next intent) before after := by
  obtain ⟨token,present,atToken⟩ := current
  have readValues : (startRule next intent).read = intent.plan.reads.map .heap := by
    cases selected : intent.plan.action <;> simp [startRule,selected]
  obtain ⟨picked,takes,positive⟩ := ExactRequestExecution.selection action (.control next intent.plan.input)
    (intent.plan.reads.map .heap) (startRule next intent).produce before consistent token present atToken
    (by intro row member
        obtain ⟨original,atOriginal,rfl⟩ := List.mem_map.mp member
        exact reads original atOriginal)
    (by intro occurrence _ member same
        subst occurrence
        obtain ⟨row,_,equal⟩ := List.mem_map.mp member
        change Row.heap row = label token at equal
        rw [atToken] at equal
        cases equal)
  have takeValues : (startRule next intent).take = [.control next intent.plan.input] := by
    cases selected : intent.plan.action <;> simp [startRule,selected]
  have noTell : (startRule next intent).tell = [] := by
    cases selected : intent.plan.action <;> simp [startRule,selected]
  have sameProblem : picked.problem label (startRule next intent) before =
      picked.problem label (ExactRequestExecution.rule (.control next intent.plan.input)
        (intent.plan.reads.map .heap) (startRule next intent).produce) before := by
    simp only [Selection.problem,takeValues,readValues,noTell,ExactRequestExecution.rule]
  have valid : picked.Valid action label (startRule next intent) before := by
    refine ⟨positive.take_distinct,positive.output_distinct,?_,?_,positive.outputs,
      positive.occurrences,?_,?_⟩
    · simpa only [takeValues,ExactRequestExecution.rule] using positive.take_length
    · simpa only [readValues,ExactRequestExecution.rule] using positive.read_length
    · rw [sameProblem]
      exact positive.consistent
    · intro check member
      cases selected : intent.plan.action with
      | direct control => simp [startRule,selected] at member
      | edit source operation resume =>
          have same : check = .absent (.heap (.allocated next)) := by simpa [startRule,selected] using member
          subst check
          intro assignment _ occurrence old equal
          exact fresh source operation resume selected ⟨occurrence,old,equal.symm⟩
  exact ⟨picked.result label _ before,⟨picked,valid,rfl⟩⟩

theorem direct_start_keeps_heap {program : Program} {before after : World}
    (next : Nat) (intent : Intent program) (control : Control Nat)
    (direct : intent.plan.action = .direct control)
    (stepped : Step action label (startRule next intent) before after) :
    heapPresent after.present = heapPresent before.present := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  ext occurrence
  simp only [mem_heapPresent]
  exact Selected.occurrence_untouched valid (embedHeap occurrence)
    (by simp [startRule,direct,embedHeap,label,IndexedOccurrences.label])
    (by simp [startRule,direct,embedHeap,label,IndexedOccurrences.label])

theorem direct_start_outputs {program : Program} {before after : World}
    (next : Nat) (intent : Intent program) (control : Control Nat)
    (direct : intent.plan.action = .direct control)
    (stepped : Step action label (startRule next intent) before after) :
    Has after.present (.control next control) := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  exact Selected.output_rows valid _ (by simp [startRule,direct])

def Row.isController : Row → Bool
  | .heap _ => false
  | .control _ _ | .waiting _ _ => true

def controllerCount (world : World) : Nat :=
  (world.present.filter fun occurrence => (label occurrence).isController).card

private theorem selected_controller_count (selected : List Occurrence) (distinct : selected.Nodup) :
    (selected.toFinset.filter fun occurrence => (label occurrence).isController).card =
      (selected.map label).countP Row.isController := by
  simpa only [List.countP_map,Bool.decide_coe,Function.comp_def] using
    (distinct.card_eq_countP (P := fun occurrence => (label occurrence).isController = true))

/-- Resource validity and balanced control ports preserve the number of
physical controllers. Equal control labels are not silently identified. -/
theorem controller_count_of_balanced_step {before after : World} {rule : RuleInstance Row}
    (balanced : rule.take.countP Row.isController = rule.produce.countP Row.isController)
    (stepped : Step action label rule before after) : controllerCount after = controllerCount before := by
  obtain ⟨picked,valid,rfl⟩ := stepped
  let old := before.present.filter fun occurrence => (label occurrence).isController
  let taken := picked.taken.toFinset.filter fun occurrence => (label occurrence).isController
  let made := picked.made.toFinset.filter fun occurrence => (label occurrence).isController
  have removed : taken ⊆ old := by
    intro occurrence member
    obtain ⟨selected,kind⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨valid.occurrences.taken_subset selected,kind⟩
  have apart : Disjoint (old \ taken) made := by
    apply Finset.disjoint_left.mpr
    intro occurrence retained created
    have oldMember := (Finset.mem_filter.mp (Finset.mem_sdiff.mp retained).1).1
    have newMember := (Finset.mem_filter.mp created).1
    exact Finset.disjoint_left.mp valid.occurrences.fresh newMember oldMember
  have sameShape : (picked.result label rule before).present.filter (fun occurrence => (label occurrence).isController) =
      (old \ taken) ∪ made := by
    ext occurrence
    cases kind : (label occurrence).isController <;>
      simp [old,taken,made,Selection.result,fire,Selection.commit,kind]
  have takeCount : taken.card = rule.take.countP Row.isController := by
    rw [← (Selected.input_labels valid).1]
    exact selected_controller_count picked.taken valid.take_distinct
  have makeCount : made.card = rule.produce.countP Row.isController := by
    rw [← valid.outputs]
    exact selected_controller_count picked.made valid.output_distinct
  have equalCount : made.card = taken.card := by rw [makeCount,takeCount,balanced]
  change ((picked.result label rule before).present.filter _).card = old.card
  rw [sameShape,Finset.card_union_of_disjoint apart,equalCount]
  exact Finset.card_sdiff_add_card_eq_card removed

theorem Catalogue.controller_balance {program : Program} {rule : RuleInstance Row} (catalogue : Catalogue program rule) :
    rule.take.countP Row.isController = rule.produce.countP Row.isController := by
  cases catalogue with
  | start next intent => cases selected : intent.plan.action <;> simp [startRule,selected,Row.isController]
  | copy job input reads source operation resume event =>
      cases event <;> simp [copyRule,Row.isController,SnapshotCopy.Event.rule,SnapshotCopy.beginRule,
        SnapshotCopy.copyRule,SnapshotCopy.finishRule]
  | commit job input reads source resume event =>
      cases event <;> simp [commitRule,Row.isController,NeedStoreOperations.Event.rule]

theorem Executes.controller_count {program : Program} {before after : World} (execution : Executes program before after) :
    controllerCount after = controllerCount before := by
  obtain ⟨rule,catalogue,stepped⟩ := execution
  exact controller_count_of_balanced_step catalogue.controller_balance stepped

theorem Path.controller_count {program : Program} {before after : World} (path : Path program before after) :
    controllerCount after = controllerCount before := by
  induction path with
  | refl => rfl
  | tail earlier step ih => exact step.controller_count.trans ih

theorem Path.single_controller {program : Program} {before after : World} (path : Path program before after)
    (single : controllerCount before = 1) : controllerCount after = 1 := path.controller_count.trans single

theorem controller_unique {world : World} {first second : Row}
    (single : controllerCount world = 1) (firstHere : Has world.present first) (secondHere : Has world.present second)
    (firstKind : first.isController = true) (secondKind : second.isController = true) : first = second := by
  obtain ⟨left,leftHere,leftLabel⟩ := firstHere
  obtain ⟨right,rightHere,rightLabel⟩ := secondHere
  obtain ⟨only,exactly⟩ := Finset.card_eq_one.mp single
  have leftPresent : left ∈ world.present.filter (fun occurrence => (label occurrence).isController) :=
    Finset.mem_filter.mpr ⟨leftHere,by rw [leftLabel]; exact firstKind⟩
  have rightPresent : right ∈ world.present.filter (fun occurrence => (label occurrence).isController) :=
    Finset.mem_filter.mpr ⟨rightHere,by rw [rightLabel]; exact secondKind⟩
  rw [exactly] at leftPresent rightPresent
  have equal : left = right := (Finset.mem_singleton.mp leftPresent).trans (Finset.mem_singleton.mp rightPresent).symm
  exact leftLabel.symm.trans ((congrArg label equal).trans rightLabel)

/-- With one running control, the catalogue cannot choose an unrelated
copy or commit event. Its start must match both the counter and control. -/
theorem running_step_is_start {program : Program} {before after : World} (next : Nat) (current : Control Nat)
    (single : controllerCount before = 1) (active : Has before.present (.control next current))
    (execution : Executes program before after) :
    ∃ intent : Intent program, intent.plan.input = current ∧ Step action label (startRule next intent) before after := by
  obtain ⟨rule,catalogue,stepped⟩ := execution
  obtain ⟨picked,valid,result⟩ := stepped
  cases catalogue with
  | start other intent =>
      have selected := Selected.take_rows valid (.control other intent.plan.input)
        (by cases actionAt : intent.plan.action <;> simp [startRule,actionAt])
      obtain ⟨rfl,equal⟩ := Row.control.inj (controller_unique single active selected rfl rfl)
      exact ⟨intent,equal.symm,⟨picked,valid,result⟩⟩
  | copy job input reads source operation resume event =>
      have selected := Selected.read_rows valid (.waiting job ⟨input,reads,.edit source operation resume⟩) (by simp [copyRule])
      have impossible := controller_unique single active selected rfl rfl
      cases impossible
  | commit job input reads source resume event =>
      have selected := Selected.take_rows valid (.waiting job ⟨input,reads,.edit source event.operation resume⟩) (by simp [commitRule])
      have impossible := controller_unique single active selected rfl rfl
      cases impossible

/-- Waiting fixes the job, operation and continuation of every possible
catalogue step. This is a derived invariant of the ordinary row matching. -/
theorem waiting_step_matches_plan {program : Program} {before after : World} (job : Nat) (plan : Plan)
    (single : controllerCount before = 1) (waiting : Has before.present (.waiting job plan))
    (execution : Executes program before after) :
    ∃ input reads source operation resume, plan = ⟨input,reads,.edit source operation resume⟩ ∧
      ((∃ event : SnapshotCopy.Event Suspension,
          Step action label (copyRule job input reads source operation resume event) before after) ∨
        ∃ event : NeedStoreOperations.Event, event.operation = operation ∧
          Step action label (commitRule job input reads source resume event) before after) := by
  obtain ⟨rule,catalogue,stepped⟩ := execution
  obtain ⟨picked,valid,result⟩ := stepped
  cases catalogue with
  | start next intent =>
      have selected := Selected.take_rows valid (.control next intent.plan.input)
        (by cases actionAt : intent.plan.action <;> simp [startRule,actionAt])
      have impossible := controller_unique single waiting selected rfl rfl
      cases impossible
  | copy other input reads source operation resume event =>
      have selected := Selected.read_rows valid (.waiting other ⟨input,reads,.edit source operation resume⟩) (by simp [copyRule])
      obtain ⟨rfl,rfl⟩ := Row.waiting.inj (controller_unique single waiting selected rfl rfl)
      exact ⟨input,reads,source,operation,resume,rfl,Or.inl ⟨event,picked,valid,result⟩⟩
  | commit other input reads source resume event =>
      have selected := Selected.take_rows valid (.waiting other ⟨input,reads,.edit source event.operation resume⟩) (by simp [commitRule])
      obtain ⟨rfl,rfl⟩ := Row.waiting.inj (controller_unique single waiting selected rfl rfl)
      exact ⟨input,reads,source,event.operation,resume,rfl,Or.inr ⟨event,rfl,picked,valid,result⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine
