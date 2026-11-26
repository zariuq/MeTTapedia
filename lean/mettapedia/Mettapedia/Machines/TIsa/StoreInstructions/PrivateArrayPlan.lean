import Mettapedia.Machines.TIsa.StoreInstructions.StorePublication

/-!
# Word origins for private snapshot preparation

A preparation plan says which old slot feeds each surviving word.
Equal values at different occurrences therefore have different
copy sources. New words and directory metadata are literals. The
plan is evaluated against the old snapshot, not against a stream of
states that can observe its own partial writes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayPlan

open PackedOccurrences (Row)
open StorePublication (Snapshot)

inductive Slot where
  | size
  | nextIdentity
  | identity (ordinal : ℕ)
  | value (ordinal : ℕ)
  | start (key : ℕ)
  | length (key : ℕ)
  | posting (ordinal : ℕ)
  deriving DecidableEq

inductive Operand where
  | copy (source : Slot)
  | literal (value : Word)
  deriving DecidableEq

abbrev Write := Slot × Operand

def read (snapshot : Snapshot) : Slot → Option Word
  | .size => some snapshot.data.sizeWord
  | .nextIdentity => some snapshot.data.nextIdentity
  | .identity i => snapshot.data.occurrences[i]?.map Prod.fst
  | .value i => snapshot.data.occurrences[i]?.map Prod.snd
  | .start k => snapshot.index.directory[k]?.map Prod.fst
  | .length k => snapshot.index.directory[k]?.map Prod.snd
  | .posting i => snapshot.index.postings[i]?

def Operand.get (snapshot : Snapshot) : Operand → Option Word
  | .copy slot => read snapshot slot
  | .literal value => some value

def Write.values (before : Snapshot) (m : Write) : Option (Slot × Word) :=
  (m.2.get before).map (fun word => (m.1, word))

def evaluate (before : Snapshot) (moves : List Write) : Option (List (Slot × Word)) :=
  moves.mapM (Write.values before)

def rows : List Row → ℕ → List (Slot × Word)
  | [], _ => []
  | row :: rest, dst =>
    (.identity dst, row.1) :: (.value dst, row.2) :: rows rest (dst + 1)

def copyRows : List (Row × ℕ) → ℕ → List Write
  | [], _ => []
  | (_, src) :: rest, dst =>
    (.identity dst, .copy (.identity src)) :: (.value dst, .copy (.value src)) :: copyRows rest (dst + 1)

def dataContents (data : PackedOccurrences.Layout) : List (Slot × Word) :=
  [(.size, data.sizeWord), (.nextIdentity, data.nextIdentity)] ++ rows data.occurrences.toList 0

def indexContents (index : PackedIndex.Layout) : List (Slot × Word) :=
  index.directory.toList.zipIdx.flatMap (fun (entry, i) => [(.start i, entry.1), (.length i, entry.2)]) ++
    index.postings.toList.zipIdx.map (fun (value, i) => (.posting i, value))

def contents (snapshot : Snapshot) : List (Slot × Word) :=
  dataContents snapshot.data ++ indexContents snapshot.index

private theorem at_row {data : List Row} {row : Row} (start index : ℕ) (found : data[index]? = some row) :
    (.identity (start + index), row.1) ∈ rows data start ∧
    (.value (start + index), row.2) ∈ rows data start := by
  induction data generalizing index start with
  | nil => cases index <;> cases found
  | cons first later ih =>
    cases index with
    | zero =>
      have same : first = row := Option.some.inj found
      subst row
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
    | succ i =>
      have both := ih (start + 1) i found
      have shift : start + i.succ = start + 1 + i := by omega
      rw [shift]
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ both.1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ both.2)⟩

theorem read_mem_contents {snapshot : Snapshot} {slot : Slot} {word : Word}
    (loaded : read snapshot slot = some word) : (slot, word) ∈ contents snapshot := by
  cases slot with
  | size =>
    have same : snapshot.data.sizeWord = word := Option.some.inj loaded
    exact same ▸ List.mem_append_left _ List.mem_cons_self
  | nextIdentity =>
    have same : snapshot.data.nextIdentity = word := Option.some.inj loaded
    exact same ▸ List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | identity i =>
    obtain ⟨row, ready, rfl⟩ := Option.map_eq_some_iff.mp loaded
    apply List.mem_append_left
    apply List.mem_append_right
    have listed : snapshot.data.occurrences.toList[i]? = some row := by simpa using ready
    simpa only [zero_add] using (at_row 0 i listed).1
  | value i =>
    obtain ⟨row, ready, rfl⟩ := Option.map_eq_some_iff.mp loaded
    apply List.mem_append_left
    apply List.mem_append_right
    have listed : snapshot.data.occurrences.toList[i]? = some row := by simpa using ready
    simpa only [zero_add] using (at_row 0 i listed).2
  | start i =>
    obtain ⟨entry, ready, rfl⟩ := Option.map_eq_some_iff.mp loaded
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨(entry, i), List.mem_zipIdx_iff_getElem?.mpr (by simpa using ready), List.mem_cons_self⟩
  | length i =>
    obtain ⟨entry, ready, rfl⟩ := Option.map_eq_some_iff.mp loaded
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨(entry, i), List.mem_zipIdx_iff_getElem?.mpr (by simpa using ready),
      List.mem_cons_of_mem _ List.mem_cons_self⟩
  | posting i =>
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(word, i), List.mem_zipIdx_iff_getElem?.mpr (by simpa [read] using loaded), rfl⟩

def literals (input : List (Slot × Word)) : List Write :=
  input.map fun (slot, value) => (slot, .literal value)

theorem evaluate_append (before : Snapshot) (first rest : List Write) :
    evaluate before (first ++ rest) =
      (evaluate before first).bind (fun left => (evaluate before rest).map (left ++ ·)) := by
  simp only [evaluate, List.mapM_append, bind, pure]
  cases first.mapM (Write.values before) <;> cases rest.mapM (Write.values before) <;> rfl

theorem evaluate_destinations {before : Snapshot} {plan : List Write} {values : List (Slot × Word)}
    (success : evaluate before plan = some values) : values.map Prod.fst = plan.map Prod.fst := by
  induction plan generalizing values with
  | nil =>
    have empty : ([] : List (Slot × Word)) = values := Option.some.inj success
    rw [← empty]
    rfl
  | cons first rest ih =>
    unfold evaluate at success
    rw [List.mapM_cons] at success
    obtain ⟨head, firstOut, later⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨tail, tailOut, finished⟩ := Option.bind_eq_some_iff.mp later
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp firstOut
    obtain rfl := Option.some.inj finished
    simp only [List.map_cons, ih tailOut]

theorem evaluate_literals (before : Snapshot) (words : List (Slot × Word)) :
    evaluate before (literals words) = some words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    obtain ⟨slot, value⟩ := word
    change (literals rest).mapM (Write.values before) = some rest at ih
    simp only [evaluate, literals, List.map_cons, List.mapM_cons, Write.values, Operand.get, Option.map_some]
    rw [show (List.map (fun (s, v) => (s, Operand.literal v)) rest).mapM (Write.values before) = some rest from ih]
    rfl

theorem evaluate_copyRows (before : Snapshot) (selected : List (Row × ℕ)) (start : ℕ)
    (found : ∀ entry ∈ selected, before.data.occurrences[entry.2]? = some entry.1) :
    evaluate before (copyRows selected start) = some (rows (selected.map Prod.fst) start) := by
  induction selected generalizing start with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨entry, location⟩ := head
    have here := found (entry, location) List.mem_cons_self
    have next := ih (start + 1) (fun e member => found e (List.mem_cons_of_mem _ member))
    change (copyRows tail (start + 1)).mapM (Write.values before) = _ at next
    simp only [copyRows, evaluate, List.mapM_cons, Write.values, Operand.get, read, here, Option.map_some,
      bind, Option.bind_some, next, List.map_cons, rows]
    rfl

theorem rows_append (first rest : List Row) (start : ℕ) :
    rows (first ++ rest) start = rows first start ++ rows rest (start + first.length) := by
  induction first generalizing start with
  | nil => simp [rows]
  | cons row later ih =>
    simp only [List.cons_append, rows, ih, List.length_cons, Nat.add_assoc, Nat.add_comm 1 later.length]

private theorem available (before : Snapshot) (entry : Row × ℕ)
    (member : entry ∈ before.data.occurrences.toList.zipIdx) :
    before.data.occurrences[entry.2]? = some entry.1 := by
  simpa using List.mem_zipIdx_iff_getElem?.mp member

def survivors (data : PackedOccurrences.Layout) (identity : ℕ) : List (Row × ℕ) :=
  data.occurrences.toList.zipIdx.filter (fun entry => entry.1.1.toNat != identity)

theorem survivors_values (data : PackedOccurrences.Layout) (identity : ℕ) :
    (survivors data identity).map Prod.fst = (PackedOccurrences.take data identity).occurrences.toList := by
  have same := List.filter_map (l := data.occurrences.toList.zipIdx) (f := Prod.fst)
    (p := fun row => row.1.toNat != identity)
  rw [List.zipIdx_map_fst] at same
  simp only [PackedOccurrences.take, Array.toList_filter]
  exact same.symm

def takeWords (data : PackedOccurrences.Layout) (identity : ℕ) : List Write :=
  [(.size, .literal (PackedOccurrences.take data identity).sizeWord), (.nextIdentity, .copy .nextIdentity)] ++
    copyRows (survivors data identity) 0

theorem evaluate_take (before : Snapshot) (identity : ℕ) :
    evaluate before (takeWords before.data identity) = some (dataContents (PackedOccurrences.take before.data identity)) := by
  have copied := evaluate_copyRows before (survivors before.data identity) 0
    (fun entry h => available before entry (List.mem_filter.mp h).1)
  rw [survivors_values] at copied
  rw [takeWords, evaluate_append, copied]
  rfl

def appendWords (data : PackedOccurrences.Layout) (size next : Word) (added : Row) : List Write :=
  [(.size, .literal size), (.nextIdentity, .literal next)] ++
    copyRows data.occurrences.toList.zipIdx 0 ++ literals (rows [added] data.occurrences.size)

theorem evaluate_append_row (before : Snapshot) (size next : Word) (added : Row) :
    evaluate before (appendWords before.data size next added) =
      some (dataContents ⟨size, before.data.occurrences.push added, next⟩) := by
  have copied := evaluate_copyRows before before.data.occurrences.toList.zipIdx 0 (available before)
  rw [List.zipIdx_map_fst] at copied
  rw [appendWords, evaluate_append, evaluate_append, copied, evaluate_literals]
  simp only [dataContents, Array.toList_push, rows_append, zero_add, Array.length_toList]
  rfl

variable {V : Type*} {keys : ℕ}

inductive Edit (V : Type*) where
  | take (identity : ℕ)
  | make (value : V)

def Edit.taken : Edit V → List ℕ
  | .take identity => [identity]
  | .make _ => []

def Edit.made : Edit V → List V
  | .take _ => []
  | .make value => [value]

def allocate (codes : PackedOccurrences.Codes V) (before : PackedOccurrences.Layout) :
    Edit V → Option (PackedOccurrences.Layout × List Write)
  | .take identity => some (PackedOccurrences.take before identity, takeWords before identity)
  | .make value =>
    let size := before.occurrences.size + 1
    let next := before.nextIdentity.toNat + 1
    if size < 2 ^ 64 ∧ next < 2 ^ 64 then
      (PackedOccurrences.packRow codes (before.nextIdentity.toNat, value)).map fun newRow =>
        let sizeWord := BitVec.ofNat 64 size
        let nextWord := BitVec.ofNat 64 next
        (⟨sizeWord, before.occurrences.push newRow, nextWord⟩, appendWords before sizeWord nextWord newRow)
    else none

theorem allocate_layout (codes : PackedOccurrences.Codes V) (before : PackedOccurrences.Layout) (change : Edit V) :
    (allocate codes before change).map Prod.fst =
      StorePublication.appendAll codes (StorePublication.removeAll before change.taken) change.made := by
  cases change with
  | take identity => rfl
  | make value =>
    simp only [Edit.taken, Edit.made, StorePublication.removeAll, StorePublication.appendAll, allocate, PackedOccurrences.make?]
    split
    · cases PackedOccurrences.packRow codes (before.nextIdentity.toNat, value) <;> rfl
    · rfl

theorem evaluate_allocated (codes : PackedOccurrences.Codes V) {before : Snapshot} {change : Edit V}
    {after : PackedOccurrences.Layout} {moves : List Write} (ready : allocate codes before.data change = some (after, moves)) :
    evaluate before moves = some (dataContents after) := by
  cases change with
  | take identity =>
    have fields := Prod.mk.inj (Option.some.inj ready)
    rw [← fields.1, ← fields.2]
    exact evaluate_take before identity
  | make value =>
    by_cases room : before.data.occurrences.size + 1 < 2 ^ 64 ∧ before.data.nextIdentity.toNat + 1 < 2 ^ 64
    · simp only [allocate, if_pos room] at ready
      obtain ⟨made, _, equal⟩ := Option.map_eq_some_iff.mp ready
      have fields := Prod.mk.inj equal
      rw [← fields.1, ← fields.2]
      exact evaluate_append_row before _ _ made
    · simp only [allocate, if_neg room, reduceCtorEq] at ready

def assemble (codes : PackedOccurrences.Codes V) (classify : V → Fin keys) (before : Snapshot) (edit : Edit V) :
    Option (Snapshot × List Write) := do
  let (data, wordPlan) ← allocate codes before.data edit
  let target ← StorePublication.indexPrepared codes classify data
  pure (target, wordPlan ++ literals (indexContents target.index))

theorem assemble_exact (codes : PackedOccurrences.Codes V) (classify : V → Fin keys) (before : Snapshot)
    (edit : Edit V) :
    (assemble codes classify before edit).map Prod.fst =
      StorePublication.prepare codes classify before edit.taken edit.made := by
  unfold StorePublication.prepare
  rw [← allocate_layout codes before.data edit]
  cases alloc : allocate codes before.data edit with
  | none => simp [assemble, alloc]
  | some choice =>
    obtain ⟨data, plan⟩ := choice
    cases indexed : StorePublication.indexPrepared codes classify data <;> simp [assemble, alloc, indexed]

theorem evaluate_assembled (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {before target : Snapshot} {edit : Edit V} {moves : List Write}
    (ready : assemble codes classify before edit = some (target, moves)) :
    evaluate before moves = some (contents target) := by
  obtain ⟨⟨data, plan⟩, allocated, remaining⟩ := Option.bind_eq_some_iff.mp ready
  obtain ⟨complete, indexed, returned⟩ := Option.bind_eq_some_iff.mp remaining
  have fields := Prod.mk.inj (Option.some.inj returned)
  rw [← fields.1, ← fields.2]
  rw [evaluate_append, evaluate_literals, evaluate_allocated codes allocated]
  have dataSame : complete.data = data := by
    unfold StorePublication.indexPrepared at indexed
    split at indexed
    · cases indexed
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp indexed
      rfl
  simp [contents, dataSame]

namespace Examples

private def twoCopies : PackedOccurrences.Layout := ⟨2, #[(7, 42), (9, 42)], 10⟩

theorem take_keeps_the_second_copy_source :
    (.value 0, .copy (.value 1)) ∈ takeWords twoCopies 7 ∧
      (.value 0, .copy (.value 0)) ∉ takeWords twoCopies 7 := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayPlan
