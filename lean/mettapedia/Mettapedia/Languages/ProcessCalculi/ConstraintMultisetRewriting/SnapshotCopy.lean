import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactRequestExecution

/-!
# Snapshot copying by ordinary occurrence rules

Three finite rule families prepare a copy, read one source cell at a time,
and make the completed snapshot available. The payload is closed data: this
is a ground storage/control client of the existing transform calculus, not
an alternative account of higher-order unification. Each copied cell has
its own physical occurrence. No rule calls a whole-store copying function.

Ready source snapshots are immutable in this protocol. A destination is
reserved before its cursor starts and becomes ready only at completion.
The reachable-prefix invariant supplies coverage; a bare cursor or stamp is
not an authentication mechanism for an arbitrary surrounding program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SnapshotCopy

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

inductive Row (Value : Type) where
  | allocated (snapshot : Nat)
  | metadata (snapshot count : Nat) (trace : List Nat)
  | ready (snapshot : Nat)
  | cell (snapshot index : Nat) (value : Value)
  | request (job source : Nat)
  | cursor (job source destination index remaining : Nat)
  | reply (job snapshot : Nat)
  deriving DecidableEq

variable {Value : Type}

def action : SubstitutionAction (Row Value) Unit where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun _ value => value
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ {_ _} same => same

abbrev Occurrence (Value : Type) := IndexedOccurrences.Occurrence (Row Value)
abbrev World (Value : Type) := Configuration (Row Value) (Occurrence Value)
abbrev label : Occurrence Value → Row Value := IndexedOccurrences.label

def Has (world : Finset (Occurrence Value)) (row : Row Value) : Prop :=
  ∃ occurrence ∈ world, label occurrence = row

def UniqueRow (world : Finset (Occurrence Value)) (row : Row Value) : Prop :=
  ∀ first ∈ world, ∀ second ∈ world, label first = row → label second = row → first = second

def Row.mentions : Row Value → Finset Nat
  | .allocated snapshot | .metadata snapshot _ _ | .ready snapshot | .cell snapshot _ _ => {snapshot}
  | .request _ source => {source}
  | .cursor _ source destination _ _ => {source,destination}
  | .reply _ snapshot => {snapshot}

def Fresh (world : Finset (Occurrence Value)) (snapshot : Nat) : Prop :=
  ∀ occurrence ∈ world, snapshot ∉ (label occurrence).mentions

theorem Fresh.not_has {world : Finset (Occurrence Value)} {snapshot : Nat}
    (fresh : Fresh world snapshot) (row : Row Value) (mentions : snapshot ∈ row.mentions) : ¬ Has world row := by
  rintro ⟨occurrence,present,same⟩
  exact fresh occurrence present (same.symm ▸ mentions)

def beginRule (job source destination count : Nat) (trace : List Nat) : RuleInstance (Row Value) :=
  ⟨[.request job source], [.ready source,.metadata source count trace], [],
    [.absent (.allocated destination)],
    [.allocated destination,.metadata destination count trace,.cursor job source destination 0 count]⟩

def copyRule (job source destination index remaining : Nat) (value : Value) : RuleInstance (Row Value) :=
  ⟨[.cursor job source destination index (remaining+1)], [.ready source,.cell source index value], [], [],
    [.cell destination index value,.cursor job source destination (index+1) remaining]⟩

def finishRule (job source destination count : Nat) (trace : List Nat) : RuleInstance (Row Value) :=
  ⟨[.cursor job source destination count 0],
    [.ready source,.metadata source count trace,.metadata destination count trace], [], [],
    [.ready destination,.reply job destination]⟩

variable [DecidableEq Value]

/-- Exact cell contents and one physical occurrence per logical slot.
Duplicate payloads at different indices remain different cells. -/
structure Cells (world : Finset (Occurrence Value)) (snapshot : Nat) (values : List Value) : Prop where
  exact : ∀ index value, Has world (.cell snapshot index value) ↔ values[index]? = some value
  unique : ∀ first ∈ world, ∀ second ∈ world, ∀ index firstValue secondValue,
    label first = .cell snapshot index firstValue → label second = .cell snapshot index secondValue → first = second

/-- Metadata for one snapshot has one count and trace interpretation.
Conflicting headers cannot authenticate the same stored cell family. -/
structure Metadata (world : Finset (Occurrence Value)) (snapshot count : Nat) (trace : List Nat) : Prop where
  present : Has world (.metadata snapshot count trace)
  agreement : ∀ otherCount otherTrace, Has world (.metadata snapshot otherCount otherTrace) →
    otherCount = count ∧ otherTrace = trace

structure Snapshot (world : Finset (Occurrence Value)) (snapshot : Nat)
    (values : List Value) (trace : List Nat) : Prop where
  allocated : Has world (.allocated snapshot)
  metadata : Metadata world snapshot values.length trace
  ready : Has world (.ready snapshot)
  cells : Cells world snapshot values

/-- One actual selected ordinary firing. The chosen request or cursor is
retained as a physical identity, so an old preparation cannot use its replacement. -/
structure Firing (rule : RuleInstance (Row Value)) (token : Occurrence Value)
    (before after : World Value) where
  picked : Selection (Occurrence Value)
  takes : picked.taken = [token]
  valid : picked.Valid action label rule before
  result : after = picked.result label rule before

theorem Firing.ordinary {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) :
    Step action label rule before after := ⟨firing.picked,firing.valid,firing.result⟩

theorem Firing.token_present {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) : token ∈ before.present := by
  exact firing.valid.occurrences.taken_subset (by simp [Selection.commit, firing.takes])

theorem Firing.token_consumed {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) : token ∉ after.present := by
  rw [firing.result]
  exact firing.valid.consumed_removed (by simp [firing.takes])

theorem Firing.output_rows {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (row : Row Value)
    (produced : row ∈ rule.produce) : Has after.present row := by
  rw [← firing.valid.outputs] at produced
  obtain ⟨occurrence,made,rfl⟩ := List.mem_map.mp produced
  refine ⟨occurrence,?_,rfl⟩
  rw [firing.result]
  exact made_subset_fire (by simpa [Selection.commit] using made)

theorem Firing.read_rows {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) :
    ∀ row ∈ rule.read, Has before.present row := by
  obtain ⟨assignment,solved⟩ := firing.valid.consistent
  have matched := (Selection.models_problem action firing.valid solved).2.2.1
  change List.Forall₂ (fun row occurrence => row = label occurrence) rule.read firing.picked.read at matched
  have related : List.Forall₂ Eq rule.read (firing.picked.read.map label) := by
    simpa only [List.forall₂_map_right_iff] using matched
  have sameRows : rule.read = firing.picked.read.map label := by
    simpa only [List.forall₂_eq_eq_eq] using related
  intro row member
  rw [sameRows] at member
  obtain ⟨occurrence,selected,same⟩ := List.mem_map.mp member
  exact ⟨occurrence, firing.valid.occurrences.kept_subset (by simpa [Selection.commit] using selected), same⟩

omit [DecidableEq Value] in
theorem fresh_has_no_cell {world : Finset (Occurrence Value)} {snapshot : Nat} (fresh : Fresh world snapshot)
    (index : Nat) (value : Value) : ¬ Has world (.cell snapshot index value) := by
  rintro ⟨occurrence,present,same⟩
  have forbidden := fresh occurrence present
  rw [same] at forbidden
  exact forbidden (by simp [Row.mentions])

omit [DecidableEq Value] in
theorem fresh_cells_empty {world : Finset (Occurrence Value)} {snapshot : Nat} (fresh : Fresh world snapshot) :
    Cells world snapshot [] := by
  refine ⟨?_,?_⟩
  · intro index value
    simp [fresh_has_no_cell fresh index value]
  · intro first present second other index firstValue secondValue same _
    exact False.elim (fresh_has_no_cell fresh index firstValue ⟨first,present,same⟩)

theorem copy_exists (before : World Value) (job source destination index remaining : Nat) (value : Value)
    (token : Occurrence Value) (present : token ∈ before.present)
    (atToken : label token = .cursor job source destination index (remaining+1))
    (ready : Has before.present (.ready source)) (cell : Has before.present (.cell source index value))
    (consistent : action.Consistent before.equations) :
    ∃ after, Nonempty (Firing (copyRule job source destination index remaining value) token before after) := by
  obtain ⟨picked,takes,valid⟩ := ExactRequestExecution.selection action
    (.cursor job source destination index (remaining+1)) [.ready source,.cell source index value]
    [.cell destination index value,.cursor job source destination (index+1) remaining]
    before consistent token present atToken
    (by intro row member; rcases List.mem_cons.mp member with rfl | member
        · exact ready
        · have same := List.mem_singleton.mp member; subst row; exact cell)
    (by intro occurrence _ member same; subst occurrence
        change (label token : Row Value) ∈ [Row.ready source,Row.cell source index value] at member
        rw [atToken] at member; simp at member)
  exact ⟨picked.result label _ before,⟨⟨picked,takes,valid,rfl⟩⟩⟩

theorem Firing.present_iff {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (occurrence : Occurrence Value) :
    occurrence ∈ after.present ↔
      (occurrence ∈ before.present ∧ occurrence ≠ token) ∨ occurrence ∈ firing.picked.made := by
  simp [firing.result, Selection.result, fire, Selection.commit, firing.takes]

theorem Firing.made_labels {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) {occurrence : Occurrence Value}
    (made : occurrence ∈ firing.picked.made) : label occurrence ∈ rule.produce := by
  rw [← firing.valid.outputs]
  exact List.mem_map.mpr ⟨occurrence,made,rfl⟩

theorem Firing.made_unique {rule : RuleInstance (Row Value)} {token first second : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (distinct : rule.produce.Nodup)
    (firstMade : first ∈ firing.picked.made) (secondMade : second ∈ firing.picked.made)
    (same : label first = label second) : first = second := by
  have labels : (firing.picked.made.map label).Nodup := firing.valid.outputs.symm ▸ distinct
  exact List.inj_on_of_nodup_map labels firstMade secondMade same

theorem Firing.old_of_not_produced {rule : RuleInstance (Row Value)} {token occurrence : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after)
    (present : occurrence ∈ after.present) (old : label occurrence ∉ rule.produce) : occurrence ∈ before.present := by
  rcases (firing.present_iff occurrence).mp present with earlier | made
  · exact earlier.1
  · exact False.elim (old (firing.made_labels made))

theorem Firing.has_iff {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (row : Row Value)
    (notToken : label token ≠ row) :
    Has after.present row ↔ Has before.present row ∨ row ∈ rule.produce := by
  constructor
  · rintro ⟨occurrence,present,same⟩
    rcases (firing.present_iff occurrence).mp present with earlier | made
    · exact Or.inl ⟨occurrence,earlier.1,same⟩
    · exact Or.inr (same ▸ firing.made_labels made)
  · rintro (⟨occurrence,present,same⟩ | made)
    · refine ⟨occurrence,(firing.present_iff occurrence).mpr (Or.inl ⟨present,?_⟩),same⟩
      intro equal
      exact notToken (equal ▸ same)
    · exact firing.output_rows row made

theorem Firing.unique_preserved {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (row : Row Value)
    (unique : UniqueRow before.present row) (notProduced : row ∉ rule.produce) :
    UniqueRow after.present row := by
  intro first firstHere second secondHere firstLabel secondLabel
  exact unique first (firing.old_of_not_produced firstHere (firstLabel ▸ notProduced))
    second (firing.old_of_not_produced secondHere (secondLabel ▸ notProduced)) firstLabel secondLabel

theorem Firing.unique_new {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (row : Row Value)
    (absent : ¬ Has before.present row) (distinct : rule.produce.Nodup) :
    UniqueRow after.present row := by
  intro first firstHere second secondHere firstLabel secondLabel
  have firstMade : first ∈ firing.picked.made := by
    rcases (firing.present_iff first).mp firstHere with old | made
    · exact False.elim (absent ⟨first,old.1,firstLabel⟩)
    · exact made
  have secondMade : second ∈ firing.picked.made := by
    rcases (firing.present_iff second).mp secondHere with old | made
    · exact False.elim (absent ⟨second,old.1,secondLabel⟩)
    · exact made
  exact firing.made_unique distinct firstMade secondMade (firstLabel.trans secondLabel.symm)

theorem Firing.preserved {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (row : Row Value)
    (notToken : label token ≠ row) (notProduced : row ∉ rule.produce) :
    Has after.present row ↔ Has before.present row := by
  rw [firing.has_iff row notToken]
  exact or_iff_left notProduced

theorem Firing.metadata_preserved {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after)
    (snapshot count : Nat) (trace : List Nat) (metadata : Metadata before.present snapshot count trace)
    (notToken : ∀ n history, label token ≠ .metadata snapshot n history)
    (notProduced : ∀ n history, Row.metadata snapshot n history ∉ rule.produce) :
    Metadata after.present snapshot count trace := by
  refine ⟨(firing.preserved _ (notToken _ _) (notProduced _ _)).mpr metadata.present,?_⟩
  intro n history present
  exact metadata.agreement n history ((firing.preserved _ (notToken _ _) (notProduced _ _)).mp present)

theorem Firing.cells_preserved {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (snapshot : Nat) (values : List Value)
    (cells : Cells before.present snapshot values)
    (notToken : ∀ index value, label token ≠ .cell snapshot index value)
    (notProduced : ∀ index value, Row.cell snapshot index value ∉ rule.produce) :
    Cells after.present snapshot values := by
  refine ⟨fun index value => (firing.preserved _ (notToken index value) (notProduced index value)).trans
    (cells.exact index value),?_⟩
  intro first firstHere second secondHere index firstValue secondValue firstLabel secondLabel
  have firstOld := firing.old_of_not_produced firstHere (firstLabel ▸ notProduced index firstValue)
  have secondOld := firing.old_of_not_produced secondHere (secondLabel ▸ notProduced index secondValue)
  exact cells.unique first firstOld second secondOld index firstValue secondValue firstLabel secondLabel

theorem copy_preserves_source {before after : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {value : Value}
    (firing : Firing (copyRule job source destination index remaining value) token before after)
    (atToken : label token = .cursor job source destination index (remaining+1))
    (different : source ≠ destination) (values : List Value) (trace : List Nat)
    (snapshot : Snapshot before.present source values trace) : Snapshot after.present source values trace := by
  refine ⟨(firing.preserved _ (by simp [atToken]) (by simp [copyRule])).mpr snapshot.allocated,
    firing.metadata_preserved source values.length trace snapshot.metadata
      (by intros; simp [atToken]) (by intros; simp [copyRule]),
    (firing.preserved _ (by simp [atToken]) (by simp [copyRule])).mpr snapshot.ready,?_⟩
  exact firing.cells_preserved source values snapshot.cells (by intros; simp [atToken])
    (by intros; simp [copyRule,different])

theorem copy_value_is_source {before after : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {value : Value}
    (firing : Firing (copyRule job source destination index remaining value) token before after)
    (values : List Value) (cells : Cells before.present source values) : values[index]? = some value := by
  apply (cells.exact index value).mp
  exact firing.read_rows _ (by simp [copyRule])

/-- The two produced identities are recovered from the actual output list,
not supplied as a substitute for the commit's result. -/
theorem copy_outputs {before after : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {value : Value}
    (firing : Firing (copyRule job source destination index remaining value) token before after) :
    ∃ cellOut cursorOut : Occurrence Value,
      firing.picked.made = [cellOut,cursorOut] ∧
      label cellOut = .cell destination index value ∧
      label cursorOut = .cursor job source destination (index+1) remaining ∧
      cellOut ∉ before.present ∧ cursorOut ∉ before.present ∧ cellOut ≠ cursorOut := by
  have outputs := firing.valid.outputs
  change firing.picked.made.map label = [.cell destination index value,.cursor job source destination (index+1) remaining] at outputs
  obtain ⟨cellOut,rest,made,atCell,tail⟩ := List.map_eq_cons_iff.mp outputs
  obtain ⟨cursorOut,restEq,atCursor⟩ := List.map_eq_singleton_iff.mp tail
  subst rest
  have fresh : ∀ occurrence ∈ firing.picked.made, occurrence ∉ before.present := by
    intro occurrence created old
    exact Finset.disjoint_left.mp firing.valid.occurrences.fresh
      (by simpa [Selection.commit] using created) old
  refine ⟨cellOut,cursorOut,made,atCell,atCursor,fresh _ (by simp [made]),fresh _ (by simp [made]),?_⟩
  simpa [made] using firing.valid.output_distinct

omit [DecidableEq Value] in
theorem next_prefix_lookup (values : List Value) (index : Nat) (value : Value)
    (found : values[index]? = some value) (position : Nat) (other : Value) :
    (values.take (index+1))[position]? = some other ↔
      (values.take index)[position]? = some other ∨ position = index ∧ other = value := by
  by_cases earlier : position < index
  · have inside : position < index+1 := by omega
    have different : position ≠ index := by omega
    simp [earlier,inside,different]
  · by_cases same : position = index
    · subst position
      simp [found,eq_comm]
    · have outside : ¬ position < index+1 := by omega
      simp [earlier,outside,same]

/-- One copying event extends exactly one indexed destination cell. The
uniqueness clause also rules out duplicate physical records for that slot. -/
theorem copy_extends_prefix {before after : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {value : Value}
    (firing : Firing (copyRule job source destination index remaining value) token before after)
    (atToken : label token = .cursor job source destination index (remaining+1))
    (values : List Value) (found : values[index]? = some value)
    (earlier : Cells before.present destination (values.take index)) :
    Cells after.present destination (values.take (index+1)) := by
  refine ⟨?_,?_⟩
  · intro position other
    rw [firing.has_iff _ (by simp [atToken]),earlier.exact]
    simpa [copyRule] using (next_prefix_lookup values index value found position other).symm
  · intro first firstHere second secondHere position firstValue secondValue firstLabel secondLabel
    have oldAbsent : ∀ occurrence ∈ before.present, ∀ item,
        label occurrence = .cell destination index item → False := by
      intro occurrence present item same
      have old := (earlier.exact index item).mp ⟨occurrence,present,same⟩
      simp at old
    have newIndex : ∀ occurrence ∈ firing.picked.made, ∀ position item,
        label occurrence = .cell destination position item → position = index := by
      intro occurrence made position item same
      have produced := firing.made_labels made
      rw [same] at produced
      have fields : position = index ∧ item = value := by simpa [copyRule] using produced
      exact fields.1
    obtain ⟨cellOut,cursorOut,made,atCell,atCursor,_,_,_⟩ := copy_outputs firing
    have newUnique : ∀ occurrence ∈ firing.picked.made, ∀ position item,
        label occurrence = .cell destination position item → occurrence = cellOut := by
      intro occurrence member position item same
      have choices : occurrence = cellOut ∨ occurrence = cursorOut := by simpa [made] using member
      rcases choices with equal | rfl
      · exact equal
      · rw [atCursor] at same
        cases same
    rcases (firing.present_iff first).mp firstHere with oldFirst | newFirst
    · rcases (firing.present_iff second).mp secondHere with oldSecond | newSecond
      · exact earlier.unique first oldFirst.1 second oldSecond.1 position firstValue secondValue firstLabel secondLabel
      · have positionEq := newIndex second newSecond position secondValue secondLabel
        subst position
        exact False.elim (oldAbsent first oldFirst.1 firstValue firstLabel)
    · rcases (firing.present_iff second).mp secondHere with oldSecond | newSecond
      · have positionEq := newIndex first newFirst position firstValue firstLabel
        subst position
        exact False.elim (oldAbsent second oldSecond.1 secondValue secondLabel)
      · exact (newUnique first newFirst position firstValue firstLabel).trans
          (newUnique second newSecond position secondValue secondLabel).symm

/-- The state of one copy in a possibly larger occurrence frame. The source
snapshot is complete; the destination has precisely the prefix already read. -/
structure Progress (before : World Value) (job source destination : Nat)
    (values : List Value) (trace : List Nat) (index remaining : Nat) (token : Occurrence Value) : Prop where
  sourceSnapshot : Snapshot before.present source values trace
  different : source ≠ destination
  destinationAllocated : Has before.present (.allocated destination)
  destinationMetadata : Metadata before.present destination values.length trace
  prefixCells : Cells before.present destination (values.take index)
  notReady : ¬ Has before.present (.ready destination)
  notReplied : ¬ Has before.present (.reply job destination)
  tokenPresent : token ∈ before.present
  tokenLabel : label token = .cursor job source destination index remaining
  cursorUnique : ∀ occurrence ∈ before.present, ∀ otherJob otherSource position left,
    label occurrence = .cursor otherJob otherSource destination position left → occurrence = token
  length : index + remaining = values.length
  consistent : action.Consistent before.equations
  destinationMetadataUnique : UniqueRow before.present (.metadata destination values.length trace)

/-- Every admitted copying step from a valid prefix reads the next actual
source value and preserves the complete prefix invariant in its real result. -/
theorem progress_after_copy {before after : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {value : Value}
    {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index (remaining+1) token)
    (firing : Firing (copyRule job source destination index remaining value) token before after) :
    ∃ nextToken, Progress after job source destination values trace (index+1) remaining nextToken := by
  have found := copy_value_is_source firing values progress.sourceSnapshot.cells
  have count := progress.length
  obtain ⟨cellOut,cursorOut,made,atCell,atCursor,_,_,_⟩ := copy_outputs firing
  refine ⟨cursorOut,copy_preserves_source firing progress.tokenLabel progress.different values trace progress.sourceSnapshot,
    progress.different,?_,?_,copy_extends_prefix firing progress.tokenLabel values found progress.prefixCells,
    ?_,?_,?_,atCursor,?_,?_,?_,?_⟩
  · exact (firing.preserved _ (by simp [progress.tokenLabel]) (by simp [copyRule])).mpr progress.destinationAllocated
  · exact firing.metadata_preserved destination values.length trace progress.destinationMetadata
      (by intros; simp [progress.tokenLabel]) (by intros; simp [copyRule])
  · intro ready
    exact progress.notReady ((firing.preserved _ (by simp [progress.tokenLabel]) (by simp [copyRule])).mp ready)
  · intro replied
    exact progress.notReplied ((firing.preserved _ (by simp [progress.tokenLabel]) (by simp [copyRule])).mp replied)
  · exact (firing.present_iff cursorOut).mpr (Or.inr (by simp [made]))
  · intro occurrence present otherJob otherSource position left same
    rcases (firing.present_iff occurrence).mp present with old | fresh
    · exact False.elim (old.2 (progress.cursorUnique occurrence old.1 otherJob otherSource position left same))
    · have cases : occurrence = cellOut ∨ occurrence = cursorOut := by simpa [made] using fresh
      rcases cases with rfl | equal
      · rw [atCell] at same
        cases same
      · exact equal
  · omega
  · rw [firing.result]
    exact firing.valid.consistent
  · exact firing.unique_preserved _ progress.destinationMetadataUnique (by simp [copyRule])

theorem progress_has_copy {before : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index (remaining+1) token) :
    ∃ value after, Nonempty (Firing (copyRule job source destination index remaining value) token before after) := by
  have count := progress.length
  have bound : index < values.length := by omega
  let value := values[index]
  have found : values[index]? = some value := List.getElem?_eq_getElem bound
  obtain ⟨after,firing⟩ := copy_exists before job source destination index remaining value token
    progress.tokenPresent progress.tokenLabel progress.sourceSnapshot.ready
    ((progress.sourceSnapshot.cells.exact index value).mpr found) progress.consistent
  exact ⟨value,after,firing⟩

theorem finish_exists {before : World Value} {token : Occurrence Value}
    {job source destination index : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index 0 token) :
    ∃ after, Nonempty (Firing (finishRule job source destination values.length trace) token before after) := by
  have atEnd : index = values.length := by simpa using progress.length
  subst index
  obtain ⟨picked,takes,valid⟩ := ExactRequestExecution.selection action
    (.cursor job source destination values.length 0)
    [.ready source,.metadata source values.length trace,.metadata destination values.length trace]
    [.ready destination,.reply job destination] before progress.consistent token progress.tokenPresent progress.tokenLabel
    (by intro row member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl
        · exact progress.sourceSnapshot.ready
        · exact progress.sourceSnapshot.metadata.present
        · exact progress.destinationMetadata.present)
    (by intro occurrence _ member same; subst occurrence
        change (label token : Row Value) ∈ [Row.ready source,Row.metadata source values.length trace,
          Row.metadata destination values.length trace] at member
        rw [progress.tokenLabel] at member
        simp at member)
  exact ⟨picked.result label _ before,⟨⟨picked,takes,valid,rfl⟩⟩⟩

theorem finish_publishes_complete_snapshot {before after : World Value} {token : Occurrence Value}
    {job source destination index : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index 0 token)
    (firing : Firing (finishRule job source destination values.length trace) token before after) :
    Snapshot after.present destination values trace ∧ Has after.present (.reply job destination) := by
  have atEnd : index = values.length := by simpa using progress.length
  subst index
  refine ⟨⟨?_,?_,firing.output_rows _ (by simp [finishRule]),?_⟩,
    firing.output_rows _ (by simp [finishRule])⟩
  · exact (firing.preserved _ (by simp [progress.tokenLabel]) (by simp [finishRule])).mpr progress.destinationAllocated
  · exact firing.metadata_preserved destination values.length trace progress.destinationMetadata
      (by intros; simp [progress.tokenLabel]) (by intros; simp [finishRule])
  · have cells : Cells before.present destination values := by simpa using progress.prefixCells
    exact firing.cells_preserved destination values cells (by intros; simp [progress.tokenLabel])
      (by intros; simp [finishRule])

theorem finish_preserves_source {before after : World Value} {token : Occurrence Value}
    {job source destination index : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index 0 token)
    (firing : Firing (finishRule job source destination values.length trace) token before after) :
    Snapshot after.present source values trace := by
  refine ⟨(firing.preserved _ (by simp [progress.tokenLabel]) (by simp [finishRule])).mpr progress.sourceSnapshot.allocated,
    firing.metadata_preserved source values.length trace progress.sourceSnapshot.metadata
      (by intros; simp [progress.tokenLabel]) (by intros; simp [finishRule]),
    (firing.preserved _ (by simp [progress.tokenLabel]) (by simp [finishRule,progress.different])).mpr progress.sourceSnapshot.ready,
    firing.cells_preserved source values progress.sourceSnapshot.cells (by intros; simp [progress.tokenLabel])
      (by intros; simp [finishRule])⟩

/-- Actual take equations authenticate the expected control value; changing
a saved cursor's remaining count would be a different occurrence label. -/
theorem Firing.take_value {rule : RuleInstance (Row Value)} {token : Occurrence Value}
    {before after : World Value} (firing : Firing rule token before after) (expected : Row Value)
    (one : rule.take = [expected]) : label token = expected := by
  obtain ⟨assignment,solved⟩ := firing.valid.consistent
  have selected := (Selection.models_problem action firing.valid solved).2.1
  rw [one,firing.takes] at selected
  exact (List.forall₂_cons.mp selected).1.symm

theorem no_premature_finish {before : World Value} {token : Occurrence Value}
    {job source destination index remaining : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index (remaining+1) token)
    (count : Nat) (history : List Nat) :
    ¬ ∃ after, Nonempty (Firing (finishRule job source destination count history) token before after) := by
  rintro ⟨after,⟨firing⟩⟩
  have labelEq := firing.take_value (.cursor job source destination count 0) rfl
  rw [progress.tokenLabel] at labelEq
  have impossible := (Row.cursor.inj labelEq).2.2.2.2
  omega

theorem begin_exists (before : World Value) (job source destination : Nat)
    (values : List Value) (trace : List Nat) (snapshot : Snapshot before.present source values trace)
    (fresh : Fresh before.present destination) (token : Occurrence Value)
    (present : token ∈ before.present) (atToken : label token = .request job source)
    (consistent : action.Consistent before.equations) :
    ∃ after, Nonempty (Firing (beginRule job source destination values.length trace) token before after) := by
  obtain ⟨picked,takes,base⟩ := ExactRequestExecution.selection action
    (.request job source) [.ready source,.metadata source values.length trace]
    [.allocated destination,.metadata destination values.length trace,.cursor job source destination 0 values.length]
    before consistent token present atToken
    (by intro row member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact snapshot.ready
        · exact snapshot.metadata.present)
    (by intro occurrence _ member same; subst occurrence
        change (label token : Row Value) ∈ [Row.ready source,Row.metadata source values.length trace] at member
        rw [atToken] at member; simp at member)
  have valid : picked.Valid action label (beginRule job source destination values.length trace) before := by
    refine ⟨base.take_distinct,base.output_distinct,base.take_length,base.read_length,base.outputs,
      base.occurrences,base.consistent,?_⟩
    intro check member
    have only : check = .absent (.allocated destination) := List.mem_singleton.mp member
    subst check
    intro assignment _ occurrence old same
    apply fresh.not_has (.allocated destination) (by simp [Row.mentions])
    exact ⟨occurrence,old,same.symm⟩
  exact ⟨picked.result label _ before,⟨⟨picked,takes,valid,rfl⟩⟩⟩

theorem progress_after_begin {before after : World Value} {token : Occurrence Value}
    {job source destination : Nat} {values : List Value} {trace : List Nat}
    (snapshot : Snapshot before.present source values trace) (fresh : Fresh before.present destination)
    (firing : Firing (beginRule job source destination values.length trace) token before after) :
    ∃ cursor, Progress after job source destination values trace 0 values.length cursor := by
  have atToken := firing.take_value (.request job source) rfl
  have different : source ≠ destination := by
    intro same
    subst destination
    exact fresh.not_has (.allocated source) (by simp [Row.mentions]) snapshot.allocated
  have sourceAfter : Snapshot after.present source values trace := by
    refine ⟨(firing.preserved _ (by simp [atToken]) (by simp [beginRule,different])).mpr snapshot.allocated,
      firing.metadata_preserved source values.length trace snapshot.metadata
        (by intros; simp [atToken]) (by intros; simp [beginRule,different]),
      (firing.preserved _ (by simp [atToken]) (by simp [beginRule])).mpr snapshot.ready,
      firing.cells_preserved source values snapshot.cells (by intros; simp [atToken]) (by intros; simp [beginRule])⟩
  have cursorProduced : Row.cursor job source destination 0 values.length ∈ firing.picked.made.map label := by
    rw [firing.valid.outputs]
    simp [beginRule]
  obtain ⟨cursor,made,atCursor⟩ := List.mem_map.mp cursorProduced
  refine ⟨cursor,sourceAfter,different,firing.output_rows _ (by simp [beginRule]),?_,?_,?_,?_,
    (firing.present_iff cursor).mpr (Or.inr made),atCursor,?_,by simp,?_,?_⟩
  · refine ⟨firing.output_rows _ (by simp [beginRule]),?_⟩
    intro count history present
    rcases (firing.has_iff _ (by simp [atToken])).mp present with old | produced
    · exact False.elim (fresh.not_has _ (by simp [Row.mentions]) old)
    · simpa [beginRule] using produced
  · have empty := fresh_cells_empty fresh
    simpa using firing.cells_preserved destination [] empty (by intros; simp [atToken]) (by intros; simp [beginRule])
  · intro ready
    rcases (firing.has_iff _ (by simp [atToken])).mp ready with old | produced
    · exact fresh.not_has _ (by simp [Row.mentions]) old
    · simp [beginRule] at produced
  · intro replied
    rcases (firing.has_iff _ (by simp [atToken])).mp replied with old | produced
    · exact fresh.not_has _ (by simp [Row.mentions]) old
    · simp [beginRule] at produced
  · intro occurrence present otherJob otherSource position remaining same
    rcases (firing.present_iff occurrence).mp present with old | produced
    · exact False.elim (fresh.not_has _ (by simp [Row.mentions]) ⟨occurrence,old.1,same⟩)
    · have row := firing.made_labels produced
      rw [same] at row
      have fields : otherJob = job ∧ otherSource = source ∧ position = 0 ∧ remaining = values.length := by
        simpa [beginRule] using row
      rcases fields with ⟨rfl,rfl,rfl,rfl⟩
      exact firing.made_unique (by simp [beginRule]) produced made (same.trans atCursor.symm)
  · rw [firing.result]
    exact firing.valid.consistent
  · exact firing.unique_new _ (fresh.not_has _ (by simp [Row.mentions])) (by simp [beginRule])

inductive Event (Value : Type) where
  | begin (count : Nat) (trace : List Nat)
  | copy (index remaining : Nat) (value : Value)
  | finish (count : Nat) (trace : List Nat)

def Event.rule (job source destination : Nat) : Event Value → RuleInstance (Row Value)
  | .begin count trace => beginRule job source destination count trace
  | .copy index remaining value => copyRule job source destination index remaining value
  | .finish count trace => finishRule job source destination count trace

/-- A trace of actual selected firings from the three rule families. No
snapshot-correctness premise is used to define these executions. -/
inductive Execution (job source destination : Nat) : List (Event Value) → World Value → World Value → Prop where
  | nil (world : World Value) : Execution job source destination [] world world
  | cons {before middle after : World Value} {events : List (Event Value)}
      (event : Event Value) (token : Occurrence Value)
      (firing : Firing (event.rule job source destination) token before middle)
      (rest : Execution job source destination events middle after) :
      Execution job source destination (event :: events) before after

theorem Execution.ordinary_path {job source destination : Nat} {events : List (Event Value)}
    {before after : World Value} (execution : Execution job source destination events before after) :
    Relation.ReflTransGen (fun first second => ∃ event : Event Value,
      Step action label (event.rule job source destination) first second) before after := by
  induction execution with
  | nil => exact .refl
  | cons event token firing rest ih =>
      exact (Relation.ReflTransGen.single ⟨event,firing.ordinary⟩).trans ih

theorem Execution.consistent {job source destination : Nat} {events : List (Event Value)}
    {before after : World Value} (execution : Execution job source destination events before after)
    (background : action.Consistent before.equations) : action.Consistent after.equations := by
  induction execution with
  | nil => exact background
  | cons event token firing rest ih =>
      apply ih
      rw [firing.result]
      exact firing.valid.consistent

/-- The remaining cell count is a complete progress measure. Every valid
prefix can finish in exactly that many copying events and one publication. -/
theorem complete_from_progress (remaining : Nat) {job source destination : Nat}
    {values : List Value} {trace : List Nat} :
    ∀ {before : World Value} {token : Occurrence Value} {index : Nat},
      Progress before job source destination values trace index remaining token →
      ∃ after events, Execution job source destination events before after ∧ events.length = remaining+1 ∧
        Snapshot after.present source values trace ∧ Snapshot after.present destination values trace ∧
          Has after.present (.reply job destination) := by
  induction remaining with
  | zero =>
      intro before token index progress
      obtain ⟨after,⟨firing⟩⟩ := finish_exists progress
      have result := finish_publishes_complete_snapshot progress firing
      exact ⟨after,[.finish values.length trace],.cons _ token firing (.nil after),rfl,
        finish_preserves_source progress firing,result.1,result.2⟩
  | succ remaining ih =>
      intro before token index progress
      obtain ⟨value,middle,⟨firing⟩⟩ := progress_has_copy progress
      obtain ⟨nextToken,nextProgress⟩ := progress_after_copy progress firing
      obtain ⟨after,events,rest,length,sourceCopy,destinationCopy,replied⟩ := ih nextProgress
      refine ⟨after,.copy index remaining value :: events,.cons _ token firing rest,?_,
        sourceCopy,destinationCopy,replied⟩
      simp [length]

/-- An ordinary request is realized without an evaluator or whole-store
copy premise. There is one preparation, one event per indexed cell, and
one event publishing the complete destination and reply. -/
theorem snapshot_can_be_copied (before : World Value) (job source destination : Nat)
    (values : List Value) (trace : List Nat) (snapshot : Snapshot before.present source values trace)
    (fresh : Fresh before.present destination) (request : Occurrence Value)
    (present : request ∈ before.present) (atRequest : label request = .request job source)
    (consistent : action.Consistent before.equations) :
    ∃ after events, Execution job source destination events before after ∧ events.length = values.length+2 ∧
      Snapshot after.present source values trace ∧ Snapshot after.present destination values trace ∧
        Has after.present (.reply job destination) := by
  obtain ⟨started,⟨firing⟩⟩ := begin_exists before job source destination values trace snapshot fresh
    request present atRequest consistent
  obtain ⟨cursor,progress⟩ := progress_after_begin snapshot fresh firing
  obtain ⟨after,events,rest,length,parent,child,replied⟩ := complete_from_progress values.length progress
  refine ⟨after,.begin values.length trace :: events,.cons _ request firing rest,?_,parent,child,replied⟩
  simp [length]

/-- The represented source cells have exactly their original physical
identities after every individual copying event, not just equal payloads. -/
theorem copying_keeps_each_parent_occurrence {before after : World Value} {token occurrence : Occurrence Value}
    {job source destination index remaining position : Nat} {value payload : Value}
    (firing : Firing (copyRule job source destination index remaining value) token before after)
    (present : occurrence ∈ before.present) (atCell : label occurrence = .cell source position payload) :
    occurrence ∈ after.present := by
  apply (firing.present_iff occurrence).mpr
  refine Or.inl ⟨present,?_⟩
  intro same
  have atToken := firing.take_value (.cursor job source destination index (remaining+1)) rfl
  subst occurrence
  rw [atToken] at atCell
  cases atCell

/-- Reservation is checked against the actual pre-state and the event's
consistent equation store. A second request cannot reuse an allocated id. -/
theorem allocated_refuses_begin {before after : World Value} {token : Occurrence Value}
    {job source destination count : Nat} {trace : List Nat}
    (allocated : Has before.present (.allocated destination)) :
    ¬ Nonempty (Firing (beginRule job source destination count trace) token before after) := by
  rintro ⟨firing⟩
  obtain ⟨assignment,solved⟩ := firing.valid.consistent
  obtain ⟨occurrence,present,atAllocated⟩ := allocated
  exact firing.valid.checks (.absent (.allocated destination)) (by simp [beginRule])
    assignment solved occurrence present atAllocated.symm

theorem Progress.copy_reflects {before after : World Value} {token selected : Occurrence Value}
    {job source destination index remaining position left : Nat} {value : Value}
    {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index remaining token)
    (firing : Firing (copyRule job source destination position left value) selected before after) :
    selected = token ∧ position = index ∧ remaining = left+1 := by
  have atSelected := firing.take_value (.cursor job source destination position (left+1)) rfl
  have same := progress.cursorUnique selected firing.token_present job source position (left+1) atSelected
  subst selected
  have fields := Row.cursor.inj (progress.tokenLabel.symm.trans atSelected)
  exact ⟨rfl,fields.2.2.2.1.symm,fields.2.2.2.2⟩

theorem Progress.finish_reflects {before after : World Value} {token selected : Occurrence Value}
    {job source destination index remaining count : Nat} {history : List Nat}
    {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index remaining token)
    (firing : Firing (finishRule job source destination count history) selected before after) :
    selected = token ∧ remaining = 0 ∧ count = values.length ∧ history = trace := by
  have atSelected := firing.take_value (.cursor job source destination count 0) rfl
  have same := progress.cursorUnique selected firing.token_present job source count 0 atSelected
  subst selected
  have fields := Row.cursor.inj (progress.tokenLabel.symm.trans atSelected)
  have header := firing.read_rows (.metadata source count history) (by simp [finishRule])
  exact ⟨rfl,fields.2.2.2.2,progress.sourceSnapshot.metadata.agreement count history header⟩

structure Completed (world : World Value) (job source destination : Nat)
    (values : List Value) (trace : List Nat) : Prop where
  sourceSnapshot : Snapshot world.present source values trace
  destinationSnapshot : Snapshot world.present destination values trace
  reply : Has world.present (.reply job destination)
  noCursor : ∀ otherJob otherSource index remaining,
    ¬ Has world.present (.cursor otherJob otherSource destination index remaining)
  destinationMetadataUnique : UniqueRow world.present (.metadata destination values.length trace)
  replyUnique : UniqueRow world.present (.reply job destination)

theorem finish_completed {before after : World Value} {token : Occurrence Value}
    {job source destination index : Nat} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index 0 token)
    (firing : Firing (finishRule job source destination values.length trace) token before after) :
    Completed after job source destination values trace := by
  have published := finish_publishes_complete_snapshot progress firing
  refine ⟨finish_preserves_source progress firing,published.1,published.2,?_,?_,?_⟩
  · rintro otherJob otherSource position remaining ⟨occurrence,present,same⟩
    rcases (firing.present_iff occurrence).mp present with old | made
    · exact old.2 (progress.cursorUnique occurrence old.1 otherJob otherSource position remaining same)
    · have impossible := firing.made_labels made
      simp [same,finishRule] at impossible
  · exact firing.unique_preserved _ progress.destinationMetadataUnique (by simp [finishRule])
  · exact firing.unique_new _ progress.notReplied (by simp [finishRule])

theorem Completed.no_firing {before after : World Value} {token : Occurrence Value}
    {job source destination : Nat} {values : List Value} {trace : List Nat}
    (completed : Completed before job source destination values trace) (event : Event Value) :
    ¬ Nonempty (Firing (event.rule job source destination) token before after) := by
  rintro ⟨firing⟩
  cases event with
  | begin count history => exact allocated_refuses_begin completed.destinationSnapshot.allocated ⟨firing⟩
  | copy index remaining value =>
      exact completed.noCursor job source index (remaining+1)
        ⟨token,firing.token_present,firing.take_value _ rfl⟩
  | finish count history =>
      exact completed.noCursor job source count 0
        ⟨token,firing.token_present,firing.take_value _ rfl⟩

/-- Remaining protocol work, including the final publication event. This
is a proved invariant of executions, not an extra rule-admission condition. -/
inductive Phase (world : World Value) (job source destination : Nat)
    (values : List Value) (trace : List Nat) : Nat → Prop where
  | copying {index remaining : Nat} {token : Occurrence Value}
      (progress : Progress world job source destination values trace index remaining token) :
      Phase world job source destination values trace (remaining+1)
  | complete (completed : Completed world job source destination values trace) :
      Phase world job source destination values trace 0

/-- Every admitted protocol event consumes exactly one unit of remaining
work. In particular, changing the selected cursor or header cannot skip work. -/
theorem Phase.step {before after : World Value} {token : Occurrence Value}
    {job source destination rank : Nat} {values : List Value} {trace : List Nat}
    (phase : Phase before job source destination values trace rank) (event : Event Value)
    (firing : Firing (event.rule job source destination) token before after) :
    ∃ nextRank, Phase after job source destination values trace nextRank ∧ rank = nextRank+1 := by
  cases phase with
  | complete completed => exact False.elim (completed.no_firing event ⟨firing⟩)
  | copying progress =>
      cases event with
      | begin count history => exact False.elim (allocated_refuses_begin progress.destinationAllocated ⟨firing⟩)
      | copy position left value =>
          obtain ⟨rfl,rfl,rfl⟩ := progress.copy_reflects firing
          obtain ⟨nextToken,nextProgress⟩ := progress_after_copy progress firing
          exact ⟨left+1,.copying nextProgress,rfl⟩
      | finish count history =>
          obtain ⟨rfl,rfl,rfl,rfl⟩ := progress.finish_reflects firing
          exact ⟨0,.complete (finish_completed progress firing),rfl⟩

theorem Execution.phases {before after : World Value} {events : List (Event Value)}
    {job source destination rank : Nat} {values : List Value} {trace : List Nat}
    (execution : Execution job source destination events before after)
    (phase : Phase before job source destination values trace rank) :
    ∃ nextRank, Phase after job source destination values trace nextRank ∧ rank = events.length+nextRank := by
  induction execution generalizing rank with
  | nil => exact ⟨rank,phase,by simp⟩
  | cons event token firing rest ih =>
      obtain ⟨middleRank,middlePhase,firstDecrease⟩ := phase.step event firing
      obtain ⟨nextRank,finalPhase,restDecrease⟩ := ih middlePhase
      exact ⟨nextRank,finalPhase,by simp only [List.length_cons]; omega⟩

/-- There are no arbitrarily long administrative executions from a valid
copy prefix: all choices of physical outputs obey the same finite bound. -/
theorem Execution.length_bound {before after : World Value} {events : List (Event Value)}
    {job source destination index remaining : Nat} {token : Occurrence Value}
    {values : List Value} {trace : List Nat}
    (execution : Execution job source destination events before after)
    (progress : Progress before job source destination values trace index remaining token) :
    events.length ≤ remaining+1 := by
  obtain ⟨nextRank,_,rank⟩ := execution.phases (.copying progress)
  omega

/-- Readiness at the end of any admitted trace from a valid prefix entails
complete contents and exactly the required number of intervening events. -/
theorem Execution.ready_iff_completed {before after : World Value} {events : List (Event Value)}
    {job source destination index remaining : Nat} {token : Occurrence Value}
    {values : List Value} {trace : List Nat}
    (execution : Execution job source destination events before after)
    (progress : Progress before job source destination values trace index remaining token) :
    Has after.present (.ready destination) ↔
      Completed after job source destination values trace ∧ events.length = remaining+1 := by
  obtain ⟨nextRank,phase,rank⟩ := execution.phases (.copying progress)
  constructor
  · intro ready
    cases phase with
    | copying pending => exact False.elim (pending.notReady ready)
    | complete complete => exact ⟨complete,by omega⟩
  · rintro ⟨completed,_⟩
    exact completed.destinationSnapshot.ready

/-- The selected representation includes every ordinary core step of these
rules: their single take port determines the physical request or cursor. -/
theorem firing_of_step {before after : World Value} {job source destination : Nat}
    (event : Event Value) (step : Step action label (event.rule job source destination) before after) :
    ∃ token, Nonempty (Firing (event.rule job source destination) token before after) := by
  obtain ⟨picked,valid,result⟩ := step
  have one : picked.taken.length = 1 := by
    rw [← valid.take_length]
    cases event <;> rfl
  obtain ⟨token,takes⟩ := List.length_eq_one_iff.mp one
  exact ⟨token,⟨⟨picked,takes,valid,result⟩⟩⟩

theorem Execution.append {before middle after : World Value} {first second : List (Event Value)}
    {job source destination : Nat} (left : Execution job source destination first before middle)
    (right : Execution job source destination second middle after) :
    Execution job source destination (first++second) before after := by
  induction left with
  | nil => exact right
  | cons event token firing rest ih => exact .cons event token firing (ih right)

/-- Even an unrestricted choice of the three ordinary core rule families
cannot produce an infinite copying computation from an admitted prefix. -/
theorem no_infinite_copy {before : World Value} {job source destination index remaining : Nat}
    {token : Occurrence Value} {values : List Value} {trace : List Nat}
    (progress : Progress before job source destination values trace index remaining token) :
    ¬ ∃ worlds : Nat → World Value, worlds 0 = before ∧
      ∀ n, ∃ event : Event Value, Step action label (event.rule job source destination) (worlds n) (worlds (n+1)) := by
  rintro ⟨worlds,start,steps⟩
  have prefixes : ∀ n, ∃ events, Execution job source destination events before (worlds n) ∧ events.length = n := by
    intro n
    induction n with
    | zero => exact ⟨[],by rw [start]; exact .nil before,rfl⟩
    | succ n ih =>
        obtain ⟨events,execution,length⟩ := ih
        obtain ⟨event,step⟩ := steps n
        obtain ⟨selected,⟨firing⟩⟩ := firing_of_step event step
        exact ⟨events++[event],execution.append (.cons event selected firing (.nil _)),by simp [length]⟩
  obtain ⟨events,execution,length⟩ := prefixes (remaining+2)
  have bound := execution.length_bound progress
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SnapshotCopy
