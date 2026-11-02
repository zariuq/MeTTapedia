import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshots
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactInteractionExecution

/-!
# Ordinary resource rules for call-time-choice store operations

Allocation, one-cell memo updates and trace emission inspect only their
affected rows. A linear command occurrence is consumed and renewed; these
are components to be joined to instruction controls. Updating a private
copy preserves snapshots with other identities. Publication and permissions
are separate obligations of that join.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations

open SnapshotCopy
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

inductive Operation where
  | allocate (code : Comp) (environment : List (Val Nat))
  | memo (index : Nat) (value : Memo)
  | emit (event : Nat)
  deriving DecidableEq

def Operation.apply : Operation → Store → Store
  | .allocate code environment, store => store.alloc code environment
  | .memo index value, store => store.setMemo index value
  | .emit event, store => store.emit event

inductive Event where
  | allocate (count : Nat) (trace : List Nat) (code : Comp) (environment : List (Val Nat))
  | memo (index : Nat) (old : Suspension) (value : Memo)
  | memoOutside (index count : Nat) (trace : List Nat) (outside : count ≤ index) (value : Memo)
  | emit (count : Nat) (trace : List Nat) (event : Nat)

def Event.operation : Event → Operation
  | .allocate _ _ code environment => .allocate code environment
  | .memo index _ value | .memoOutside index _ _ _ value => .memo index value
  | .emit _ _ event => .emit event

def Event.rule (job snapshot : Nat) : Event → RuleInstance (Row Suspension)
  | .allocate count trace code environment =>
      ⟨[.reply job snapshot,.metadata snapshot count trace],[.ready snapshot],[],[],
        [.reply job snapshot,.metadata snapshot (count+1) trace,
          .cell snapshot count ⟨code,environment,.pending⟩]⟩
  | .memo index old value =>
      ⟨[.reply job snapshot,.cell snapshot index old],[.ready snapshot],[],[],
        [.reply job snapshot,.cell snapshot index {old with memo := value}]⟩
  | .memoOutside _ count trace _ _ =>
      ⟨[.reply job snapshot],[.ready snapshot,.metadata snapshot count trace],[],[],[.reply job snapshot]⟩
  | .emit count trace event =>
      ⟨[.reply job snapshot,.metadata snapshot count trace],[.ready snapshot],[],[],
        [.reply job snapshot,.metadata snapshot count (trace++[event])]⟩

/-- These are local data premises, recovered from selected rows. The
out-of-bounds update keeps the source's `List.modify` no-op behavior. -/
def Event.Matches (store : Store) : Event → Prop
  | .allocate count trace _ _ | .memoOutside _ count trace _ _ | .emit count trace _ =>
      count = store.cells.length ∧ trace = store.trace
  | .memo index old _ => store.cells[index]? = some old

structure Editable (world : Finset (Occurrence Suspension)) (job snapshotId : Nat) (store : Store) : Prop where
  snapshot : Snapshot world snapshotId store.cells store.trace
  metadataUnique : UniqueRow world (.metadata snapshotId store.cells.length store.trace)
  command : Has world (.reply job snapshotId)
  commandUnique : UniqueRow world (.reply job snapshotId)

theorem editable_of_completed {world : World Suspension} {job source destination : Nat} {store : Store}
    (completed : Completed world job source destination store.cells store.trace) :
    Editable world.present job destination store :=
  ⟨completed.destinationSnapshot,completed.destinationMetadataUnique,completed.reply,completed.replyUnique⟩

namespace Ground

variable {rule : RuleInstance (Row Suspension)} {picked : Selection (Occurrence Suspension)}
  {before : World Suspension}

theorem input_labels (valid : picked.Valid action label rule before) :
    picked.taken.map label = rule.take ∧ picked.read.map label = rule.read :=
  ExactInteractionExecution.rigid_input_labels action (by intros; rfl) valid

theorem taken_rows (valid : picked.Valid action label rule before) (row : Row Suspension)
    (member : row ∈ rule.take) : Has before.present row := by
  rw [← (input_labels valid).1] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,valid.occurrences.taken_subset (by simpa [Selection.commit] using selected),same⟩

theorem read_rows (valid : picked.Valid action label rule before) (row : Row Suspension)
    (member : row ∈ rule.read) : Has before.present row := by
  rw [← (input_labels valid).2] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence,valid.occurrences.kept_subset (by simpa [Selection.commit] using selected),same⟩

theorem taken_labels (valid : picked.Valid action label rule before) {occurrence : Occurrence Suspension}
    (taken : occurrence ∈ picked.taken) : label occurrence ∈ rule.take := by
  rw [← (input_labels valid).1]
  exact List.mem_map.mpr ⟨occurrence,taken,rfl⟩

theorem made_labels (valid : picked.Valid action label rule before) {occurrence : Occurrence Suspension}
    (made : occurrence ∈ picked.made) : label occurrence ∈ rule.produce := by
  rw [← valid.outputs]
  exact List.mem_map.mpr ⟨occurrence,made,rfl⟩

theorem present_iff (occurrence : Occurrence Suspension) :
    occurrence ∈ (picked.result label rule before).present ↔
      (occurrence ∈ before.present ∧ occurrence ∉ picked.taken) ∨ occurrence ∈ picked.made := by
  simp [Selection.result,fire,Selection.commit]

theorem every_matching_take_is_selected (valid : picked.Valid action label rule before)
    (unique : ∀ row ∈ rule.take, UniqueRow before.present row)
    {occurrence : Occurrence Suspension} (present : occurrence ∈ before.present)
    (atTake : label occurrence ∈ rule.take) : occurrence ∈ picked.taken := by
  have member := atTake
  rw [← (input_labels valid).1] at member
  obtain ⟨selected,selection,same⟩ := List.mem_map.mp member
  have old := valid.occurrences.taken_subset (by simpa [Selection.commit] using selection)
  have equal := unique _ atTake occurrence present selected old rfl same
  exact equal ▸ selection

theorem rows_after (valid : picked.Valid action label rule before)
    (unique : ∀ row ∈ rule.take, UniqueRow before.present row) (row : Row Suspension) :
    Has (picked.result label rule before).present row ↔
      (Has before.present row ∧ row ∉ rule.take) ∨ row ∈ rule.produce := by
  constructor
  · rintro ⟨occurrence,present,same⟩
    rcases (present_iff occurrence).mp present with old | made
    · refine Or.inl ⟨⟨occurrence,old.1,same⟩,?_⟩
      intro member
      exact old.2 (every_matching_take_is_selected valid unique old.1 (same ▸ member))
    · exact Or.inr (same ▸ made_labels valid made)
  · rintro (⟨⟨occurrence,old,same⟩,notTaken⟩ | produced)
    · refine ⟨occurrence,(present_iff occurrence).mpr (Or.inl ⟨old,?_⟩),same⟩
      intro selected
      exact notTaken (same ▸ taken_labels valid selected)
    · rw [← valid.outputs] at produced
      obtain ⟨occurrence,made,same⟩ := List.mem_map.mp produced
      exact ⟨occurrence,(present_iff occurrence).mpr (Or.inr made),same⟩

end Ground

theorem Editable.metadata_iff {world : Finset (Occurrence Suspension)} {job snapshot : Nat} {store : Store}
    (represented : Editable world job snapshot store) (count : Nat) (trace : List Nat) :
    Has world (.metadata snapshot count trace) ↔ count = store.cells.length ∧ trace = store.trace := by
  constructor
  · exact represented.snapshot.metadata.agreement count trace
  · rintro ⟨rfl,rfl⟩
    exact represented.snapshot.metadata.present

theorem matches_of_step {before after : World Suspension} {job snapshot : Nat} {store : Store}
    (represented : Editable before.present job snapshot store) (event : Event)
    (step : Step action label (event.rule job snapshot) before after) : event.Matches store := by
  obtain ⟨picked,valid,_⟩ := step
  cases event with
  | allocate count trace code environment =>
      exact represented.snapshot.metadata.agreement count trace
        (Ground.taken_rows valid _ (by simp [Event.rule]))
  | memo index old value =>
      exact (represented.snapshot.cells.exact index old).mp
        (Ground.taken_rows valid _ (by simp [Event.rule]))
  | memoOutside index count trace outside value =>
      exact represented.snapshot.metadata.agreement count trace
        (Ground.read_rows valid _ (by simp [Event.rule]))
  | emit count trace event =>
      exact represented.snapshot.metadata.agreement count trace
        (Ground.taken_rows valid _ (by simp [Event.rule]))

theorem Editable.unique_taken {world : Finset (Occurrence Suspension)} {job snapshot : Nat} {store : Store}
    (represented : Editable world job snapshot store) (event : Event) (matched : event.Matches store) :
    ∀ row ∈ (event.rule job snapshot).take, UniqueRow world row := by
  intro row member
  cases event with
  | allocate count trace code environment =>
      rcases matched with ⟨rfl,rfl⟩
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact represented.commandUnique
      · exact represented.metadataUnique
  | memo index old value =>
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact represented.commandUnique
      · intro first firstHere second secondHere atFirst atSecond
        exact represented.snapshot.cells.unique first firstHere second secondHere index old old atFirst atSecond
  | memoOutside index count trace outside value =>
      have only : row = .reply job snapshot := List.mem_singleton.mp member
      subst row
      exact represented.commandUnique
  | emit count trace event =>
      rcases matched with ⟨rfl,rfl⟩
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact represented.commandUnique
      · exact represented.metadataUnique

theorem step_exists {before : World Suspension} {job snapshot : Nat} {store : Store}
    (represented : Editable before.present job snapshot store) (event : Event) (matched : event.Matches store)
    (consistent : action.Consistent before.equations) :
    ∃ after, Step action label (event.rule job snapshot) before after := by
  have takeAvailable : ∀ row ∈ (event.rule job snapshot).take, Has before.present row := by
    intro row member
    cases event with
    | allocate count trace code environment | emit count trace event =>
        rcases matched with ⟨rfl,rfl⟩
        simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact represented.command
        · exact represented.snapshot.metadata.present
    | memo index old value =>
        simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact represented.command
        · exact (represented.snapshot.cells.exact index old).mpr matched
    | memoOutside index count trace outside value =>
        have same : row = .reply job snapshot := List.mem_singleton.mp member
        subst row
        exact represented.command
  have readAvailable : ∀ row ∈ (event.rule job snapshot).read, Has before.present row := by
    intro row member
    cases event with
    | allocate count trace code environment | memo index old value | emit count trace event =>
        have same : row = .ready snapshot := List.mem_singleton.mp member
        subst row
        exact represented.snapshot.ready
    | memoOutside index count trace outside value =>
        rcases matched with ⟨rfl,rfl⟩
        simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact represented.snapshot.ready
        · exact represented.snapshot.metadata.present
  obtain ⟨taken,takePresent,takeLabels⟩ := GuardedMultisetRewriting.exists_list_of_mem label before.present
    (event.rule job snapshot).take takeAvailable
  have distinct : taken.Nodup := List.Nodup.of_map label
    (takeLabels.symm ▸ (by cases event <;> simp [Event.rule]))
  have apart : ∀ row ∈ (event.rule job snapshot).take, row ∉ (event.rule job snapshot).read := by
    cases event <;> simp [Event.rule]
  obtain ⟨picked,_,valid⟩ := ExactInteractionExecution.selection action
    (event.rule job snapshot).take (event.rule job snapshot).read (event.rule job snapshot).produce
    before consistent taken distinct takePresent takeLabels readAvailable
    (by intro occurrence _ read taken
        have valueTaken : label occurrence ∈ (event.rule job snapshot).take := by
          rw [← takeLabels]
          exact List.mem_map.mpr ⟨occurrence,taken,rfl⟩
        exact apart _ valueTaken read)
  have exactRule : (⟨(event.rule job snapshot).take,(event.rule job snapshot).read,[],[],
      (event.rule job snapshot).produce⟩ : RuleInstance (Row Suspension)) = event.rule job snapshot := by
    cases event <;> rfl
  change picked.Valid action label ⟨(event.rule job snapshot).take,(event.rule job snapshot).read,[],[],
    (event.rule job snapshot).produce⟩ before at valid
  rw [exactRule] at valid
  exact ⟨picked.result label _ before,⟨picked,valid,rfl⟩⟩

theorem admission_iff_matches {before : World Suspension} {job snapshot : Nat} {store : Store}
    (represented : Editable before.present job snapshot store) (event : Event)
    (consistent : action.Consistent before.equations) :
    (∃ after, Step action label (event.rule job snapshot) before after) ↔ event.Matches store := by
  constructor
  · rintro ⟨after,step⟩
    exact matches_of_step represented event step
  · intro matched
    exact step_exists represented event matched consistent

namespace Ground

variable {rule : RuleInstance (Row Suspension)} {picked : Selection (Occurrence Suspension)}
  {before : World Suspension}

theorem unique_after (valid : picked.Valid action label rule before)
    (unique : ∀ row ∈ rule.take, UniqueRow before.present row) (row : Row Suspension)
    (oldUnique : UniqueRow before.present row) (distinct : rule.produce.Nodup)
    (replaceOld : row ∈ rule.produce → Has before.present row → row ∈ rule.take) :
    UniqueRow (picked.result label rule before).present row := by
  intro first firstHere second secondHere firstLabel secondLabel
  have newUnique : ∀ left ∈ picked.made, ∀ right ∈ picked.made,
      label left = label right → left = right := by
    exact List.inj_on_of_nodup_map (valid.outputs.symm ▸ distinct)
  rcases (present_iff first).mp firstHere with oldFirst | newFirst
  · rcases (present_iff second).mp secondHere with oldSecond | newSecond
    · exact oldUnique first oldFirst.1 second oldSecond.1 firstLabel secondLabel
    · have atTake := replaceOld (secondLabel ▸ made_labels valid newSecond) ⟨first,oldFirst.1,firstLabel⟩
      exact False.elim (oldFirst.2 (every_matching_take_is_selected valid unique oldFirst.1 (firstLabel ▸ atTake)))
  · rcases (present_iff second).mp secondHere with oldSecond | newSecond
    · have atTake := replaceOld (firstLabel ▸ made_labels valid newFirst) ⟨second,oldSecond.1,secondLabel⟩
      exact False.elim (oldSecond.2 (every_matching_take_is_selected valid unique oldSecond.1 (secondLabel ▸ atTake)))
    · exact newUnique first newFirst second newSecond (firstLabel.trans secondLabel.symm)

end Ground

private theorem append_lookup_iff (values : List Suspension) (value result : Suspension) (index : Nat) :
    (values++[value])[index]? = some result ↔
      values[index]? = some result ∨ index = values.length ∧ result = value := by
  by_cases inside : index < values.length
  · rw [List.getElem?_append_left inside]
    simp [Nat.ne_of_lt inside]
  · have outside : values.length ≤ index := by omega
    rw [List.getElem?_append_right outside]
    have missing : values[index]? = none := List.getElem?_eq_none_iff.mpr outside
    by_cases last : index = values.length
    · subst index
      simp [eq_comm]
    · have difference : index-values.length ≠ 0 := by omega
      simp [missing,last,difference]

theorem cells_after {before : World Suspension} {job snapshot : Nat} {store : Store}
    {picked : Selection (Occurrence Suspension)} (represented : Editable before.present job snapshot store)
    (event : Event) (matched : event.Matches store)
    (valid : picked.Valid action label (event.rule job snapshot) before) (index : Nat) (value : Suspension) :
    Has (picked.result label (event.rule job snapshot) before).present (.cell snapshot index value) ↔
      (event.operation.apply store).cells[index]? = some value := by
  rw [Ground.rows_after valid (represented.unique_taken event matched)]
  cases event with
  | allocate count trace code environment =>
      rcases matched with ⟨rfl,rfl⟩
      simp [Event.rule,Event.operation,Operation.apply,Store.alloc,represented.snapshot.cells.exact,append_lookup_iff]
  | memo position old memo =>
      change store.cells[position]? = some old at matched
      by_cases same : index = position
      · subst index
        simp [Event.rule,Event.operation,Operation.apply,Store.setMemo,represented.snapshot.cells.exact,
          matched,eq_comm]
      · simp [Event.rule,Event.operation,Operation.apply,Store.setMemo,represented.snapshot.cells.exact,
          Ne.symm same,same]
  | memoOutside position count trace outside memo =>
      rcases matched with ⟨rfl,rfl⟩
      simp [Event.rule,Event.operation,Operation.apply,Store.setMemo,represented.snapshot.cells.exact,
        List.modify_eq_self outside]
  | emit count trace event =>
      simp [Event.rule,Event.operation,Operation.apply,Store.emit,represented.snapshot.cells.exact]

theorem metadata_after {before : World Suspension} {job snapshot : Nat} {store : Store}
    {picked : Selection (Occurrence Suspension)} (represented : Editable before.present job snapshot store)
    (event : Event) (matched : event.Matches store)
    (valid : picked.Valid action label (event.rule job snapshot) before) (count : Nat) (trace : List Nat) :
    Has (picked.result label (event.rule job snapshot) before).present (.metadata snapshot count trace) ↔
      count = (event.operation.apply store).cells.length ∧ trace = (event.operation.apply store).trace := by
  rw [Ground.rows_after valid (represented.unique_taken event matched)]
  cases event with
  | allocate oldCount oldTrace code environment =>
      rcases matched with ⟨rfl,rfl⟩
      simp [Event.rule,Event.operation,Operation.apply,Store.alloc,represented.metadata_iff]
  | memo position old memo =>
      simp [Event.rule,Event.operation,Operation.apply,Store.setMemo,represented.metadata_iff]
  | memoOutside position oldCount oldTrace outside memo =>
      simp [Event.rule,Event.operation,Operation.apply,Store.setMemo,represented.metadata_iff]
  | emit oldCount oldTrace event =>
      rcases matched with ⟨rfl,rfl⟩
      simp [Event.rule,Event.operation,Operation.apply,Store.emit,represented.metadata_iff]

theorem Editable.cell_unique {world : Finset (Occurrence Suspension)} {job snapshot : Nat} {store : Store}
    (represented : Editable world job snapshot store) (index : Nat) (value : Suspension) :
    UniqueRow world (.cell snapshot index value) := by
  intro first firstHere second secondHere firstLabel secondLabel
  exact represented.snapshot.cells.unique first firstHere second secondHere index value value firstLabel secondLabel

theorem Editable.metadata_unique {world : Finset (Occurrence Suspension)} {job snapshot : Nat} {store : Store}
    (represented : Editable world job snapshot store) (count : Nat) (trace : List Nat) :
    UniqueRow world (.metadata snapshot count trace) := by
  intro first firstHere second secondHere firstLabel secondLabel
  obtain ⟨rfl,rfl⟩ := represented.snapshot.metadata.agreement count trace ⟨first,firstHere,firstLabel⟩
  exact represented.metadataUnique first firstHere second secondHere firstLabel secondLabel

theorem produced_old_is_taken {world : Finset (Occurrence Suspension)} {job snapshot : Nat} {store : Store}
    (represented : Editable world job snapshot store) (event : Event) (matched : event.Matches store)
    (row : Row Suspension) (produced : row ∈ (event.rule job snapshot).produce) (old : Has world row) :
    row ∈ (event.rule job snapshot).take := by
  cases event with
  | allocate count trace code environment =>
      rcases matched with ⟨rfl,rfl⟩
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at produced
      rcases produced with rfl | rfl | rfl
      · simp [Event.rule]
      · have impossible := (represented.metadata_iff _ _).mp old
        omega
      · have impossible := (represented.snapshot.cells.exact _ _).mp old
        simp at impossible
  | memo index record memo =>
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at produced
      rcases produced with rfl | rfl
      · simp [Event.rule]
      · have found := (represented.snapshot.cells.exact _ _).mp old
        have same : {record with memo := memo} = record := Option.some.inj (found.symm.trans matched)
        simp [Event.rule,same]
  | memoOutside index count trace outside memo =>
      simpa [Event.rule] using produced
  | emit count trace event =>
      rcases matched with ⟨rfl,rfl⟩
      simp only [Event.rule,List.mem_cons,List.not_mem_nil,or_false] at produced
      rcases produced with rfl | rfl
      · simp [Event.rule]
      · have impossible := (represented.metadata_iff _ _).mp old
        have lengths := congrArg List.length impossible.2
        simp at lengths

/-- Actual firings produce exactly the source operation's store and retain
the uniqueness needed by the next edit. The result is not supplied as a
premise or reconstructed in place of the ordinary firing result. -/
theorem preserves {before after : World Suspension} {job snapshot : Nat} {store : Store}
    (represented : Editable before.present job snapshot store) (event : Event)
    (step : Step action label (event.rule job snapshot) before after) :
    Editable after.present job snapshot (event.operation.apply store) := by
  have matched := matches_of_step represented event step
  obtain ⟨picked,valid,rfl⟩ := step
  have unique := represented.unique_taken event matched
  have distinct : (event.rule job snapshot).produce.Nodup := by cases event <;> simp [Event.rule]
  have replaced := produced_old_is_taken represented event matched
  refine ⟨⟨?_,⟨?_,?_⟩,?_,⟨cells_after represented event matched valid,?_⟩⟩,?_,?_,?_⟩
  · exact (Ground.rows_after valid unique _).mpr
      (Or.inl ⟨represented.snapshot.allocated,by cases event <;> simp [Event.rule]⟩)
  · exact (metadata_after represented event matched valid _ _).mpr ⟨rfl,rfl⟩
  · intro count trace present
    exact (metadata_after represented event matched valid count trace).mp present
  · exact (Ground.rows_after valid unique _).mpr
      (Or.inl ⟨represented.snapshot.ready,by cases event <;> simp [Event.rule]⟩)
  · intro first firstHere second secondHere index firstValue secondValue firstLabel secondLabel
    have firstFound := (cells_after represented event matched valid index firstValue).mp ⟨first,firstHere,firstLabel⟩
    have secondFound := (cells_after represented event matched valid index secondValue).mp ⟨second,secondHere,secondLabel⟩
    have same := Option.some.inj (firstFound.symm.trans secondFound)
    subst secondValue
    exact Ground.unique_after valid unique _ (represented.cell_unique index firstValue) distinct (replaced _)
      first firstHere second secondHere firstLabel secondLabel
  · exact Ground.unique_after valid unique _ (represented.metadata_unique _ _) distinct (replaced _)
  · exact (Ground.rows_after valid unique _).mpr (Or.inr (by cases event <;> simp [Event.rule]))
  · exact Ground.unique_after valid unique _ represented.commandUnique distinct (replaced _)

theorem Event.location {job snapshot : Nat} (event : Event) {row : Row Suspension}
    (member : row ∈ (event.rule job snapshot).take ++ (event.rule job snapshot).produce) :
    row.mentions = {snapshot} := by
  cases event <;>
    simp only [Event.rule,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member <;>
    rcases member with (rfl | rfl) | (rfl | rfl | rfl) <;> rfl

namespace Ground

variable {rule : RuleInstance (Row Suspension)} {picked : Selection (Occurrence Suspension)}
  {before : World Suspension}

theorem occurrence_untouched (valid : picked.Valid action label rule before) (occurrence : Occurrence Suspension)
    (notTaken : label occurrence ∉ rule.take) (notMade : label occurrence ∉ rule.produce) :
    occurrence ∈ (picked.result label rule before).present ↔ occurrence ∈ before.present := by
  rw [present_iff]
  constructor
  · rintro (⟨old,_⟩ | made)
    · exact old
    · exact False.elim (notMade (made_labels valid made))
  · intro old
    exact Or.inl ⟨old,fun taken => notTaken (taken_labels valid taken)⟩

end Ground

/-- Editing one represented snapshot preserves every other snapshot,
including the physical identities of its retained cells. -/
theorem preserves_other {before after : World Suspension} {job snapshot other : Nat} {store : Store}
    {values : List Suspension} {trace : List Nat}
    (represented : Editable before.present job snapshot store) (event : Event)
    (step : Step action label (event.rule job snapshot) before after) (different : other ≠ snapshot)
    (retained : Snapshot before.present other values trace) : Snapshot after.present other values trace := by
  have matched := matches_of_step represented event step
  obtain ⟨picked,valid,rfl⟩ := step
  have unique := represented.unique_taken event matched
  have outside : ∀ row : Row Suspension, row.mentions = {other} →
      row ∉ (event.rule job snapshot).take ∧ row ∉ (event.rule job snapshot).produce := by
    intro row atOther
    have notAccessed : row ∉ (event.rule job snapshot).take ++ (event.rule job snapshot).produce := by
      intro member
      have same := (event.location member).symm.trans atOther
      exact different (Finset.singleton_injective same).symm
    simpa only [List.mem_append,not_or] using notAccessed
  have rows : ∀ row : Row Suspension, row.mentions = {other} →
      (Has (picked.result label (event.rule job snapshot) before).present row ↔ Has before.present row) := by
    intro row atOther
    have excluded := outside row atOther
    rw [Ground.rows_after valid unique]
    simp [excluded.1,excluded.2]
  refine ⟨(rows _ rfl).mpr retained.allocated,⟨(rows _ rfl).mpr retained.metadata.present,?_⟩,
    (rows _ rfl).mpr retained.ready,⟨?_,?_⟩⟩
  · intro count history present
    exact retained.metadata.agreement count history ((rows _ rfl).mp present)
  · intro index value
    exact (rows _ rfl).trans (retained.cells.exact index value)
  · intro first firstHere second secondHere index firstValue secondValue firstLabel secondLabel
    have firstOutside := outside (label first) (by rw [firstLabel]; rfl)
    have secondOutside := outside (label second) (by rw [secondLabel]; rfl)
    exact retained.cells.unique first
      ((Ground.occurrence_untouched valid first firstOutside.1 firstOutside.2).mp firstHere) second
      ((Ground.occurrence_untouched valid second secondOutside.1 secondOutside.2).mp secondHere)
      index firstValue secondValue firstLabel secondLabel

def Operation.eventFor (operation : Operation) (store : Store) : Event :=
  match operation with
  | .allocate code environment => .allocate store.cells.length store.trace code environment
  | .memo index value =>
      if bound : index < store.cells.length then .memo index store.cells[index] value
      else .memoOutside index store.cells.length store.trace (Nat.le_of_not_gt bound) value
  | .emit event => .emit store.cells.length store.trace event

theorem Operation.eventFor_operation (operation : Operation) (store : Store) :
    (operation.eventFor store).operation = operation := by
  cases operation with
  | allocate => rfl
  | emit => rfl
  | memo index value =>
      by_cases bound : index < store.cells.length <;> simp [eventFor,bound,Event.operation]

theorem Operation.eventFor_matches (operation : Operation) (store : Store) :
    (operation.eventFor store).Matches store := by
  cases operation with
  | allocate => exact ⟨rfl,rfl⟩
  | emit => exact ⟨rfl,rfl⟩
  | memo index value =>
      by_cases bound : index < store.cells.length
      · simpa only [eventFor,dif_pos bound,Event.Matches] using List.getElem?_eq_getElem bound
      · simp [eventFor,bound,Event.Matches]

/-- Every source store operation has an actual ordinary realization,
including out-of-range memo updates. Every admitted result of the chosen
event has the same exact representation by `preserves`. -/
theorem operation_realized {before : World Suspension} {job snapshot : Nat} {store : Store}
    (represented : Editable before.present job snapshot store) (operation : Operation)
    (consistent : action.Consistent before.equations) :
    ∃ event : Event, ∃ after, event.operation = operation ∧ Step action label (event.rule job snapshot) before after ∧
      Editable after.present job snapshot (operation.apply store) := by
  obtain ⟨after,step⟩ := step_exists represented (operation.eventFor store) (operation.eventFor_matches store) consistent
  refine ⟨operation.eventFor store,after,operation.eventFor_operation store,step,?_⟩
  simpa only [operation.eventFor_operation store] using preserves represented (operation.eventFor store) step

/-- Fresh copying supplies exclusive metadata and command occurrences;
these are derived from the protocol, not required of the source snapshot. -/
theorem copy_for_editing (before : World Suspension) (job source destination : Nat) (store : Store)
    (represented : Snapshot before.present source store.cells store.trace) (fresh : Fresh before.present destination)
    (request : Occurrence Suspension) (present : request ∈ before.present)
    (atRequest : label request = .request job source) (consistent : action.Consistent before.equations) :
    ∃ after events, SnapshotCopy.Execution job source destination events before after ∧
      events.length = store.cells.length+2 ∧ Snapshot after.present source store.cells store.trace ∧
      Editable after.present job destination store := by
  obtain ⟨started,⟨firing⟩⟩ := begin_exists before job source destination store.cells store.trace represented fresh
    request present atRequest consistent
  obtain ⟨cursor,progress⟩ := progress_after_begin represented fresh firing
  obtain ⟨after,events,execution,length,parent,child,_⟩ := complete_from_progress store.cells.length progress
  have completed := ((execution.ready_iff_completed progress).mp child.ready).1
  exact ⟨after,.begin store.cells.length store.trace :: events,.cons _ request firing execution,
    by simp [length],parent,editable_of_completed completed⟩

/-- Copying and a source store operation compose through the real retained
world. The old source snapshot survives while the destination has exactly
the edited source store. Instruction control and publication must still be
joined separately to this resource construction. -/
theorem copy_and_operate (before : World Suspension) (job source destination : Nat) (store : Store)
    (operation : Operation) (represented : Snapshot before.present source store.cells store.trace)
    (fresh : Fresh before.present destination) (request : Occurrence Suspension)
    (present : request ∈ before.present) (atRequest : label request = .request job source)
    (consistent : action.Consistent before.equations) :
    ∃ copied after events, ∃ event : Event, SnapshotCopy.Execution job source destination events before copied ∧
      events.length = store.cells.length+2 ∧ event.operation = operation ∧
      Step action label (event.rule job destination) copied after ∧
      Snapshot after.present source store.cells store.trace ∧ Editable after.present job destination (operation.apply store) := by
  obtain ⟨copied,events,copying,length,parent,editable⟩ := copy_for_editing before job source destination store
    represented fresh request present atRequest consistent
  obtain ⟨event,after,atOperation,step,result⟩ := operation_realized editable operation (copying.consistent consistent)
  have different : source ≠ destination := by
    rintro rfl
    exact fresh.not_has (.allocated source) (by simp [Row.mentions]) represented.allocated
  exact ⟨copied,after,events,event,copying,length,atOperation,step,
    preserves_other editable event step different parent,result⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations
