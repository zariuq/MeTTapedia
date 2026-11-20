import Mettapedia.Machines.TIsa.Bytes

/-!
# Published word rows over the existing byte memory

The count word determines which complete rows are observable. Preparing a
word beyond that published part cannot change the view. Publishing a new count
exposes exactly the next prepared row. Missing bytes remain missing; they
are never filled with zero by the observer.

These are byte-representation and word-update laws. Native stores, capacity
guards, custody, and concurrent memory ordering require their own contracts.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.RowTableView

structure Layout where
  rows : Nat
  count : Nat
  width : Nat
  deriving DecidableEq, Repr

def word (memory : ByteMemory) (address : Nat) : Option Word :=
  (readBytes memory address 8).map packBytes
def Layout.address (layout : Layout) (row column : Nat) : Nat :=
  layout.rows + 8 * (row * layout.width + column)
def row (layout : Layout) (memory : ByteMemory) (index : Nat) : Option (List Word) :=
  (List.range layout.width).mapM fun column => word memory (layout.address index column)
def rowsBefore (layout : Layout) (memory : ByteMemory) (count : Nat) : Option (List (List Word)) :=
  (List.range count).mapM (row layout memory)
def observe (layout : Layout) (memory : ByteMemory) : Option (List (List Word)) :=
  (word memory layout.count).bind (fun count => rowsBefore layout memory count.toNat)

private theorem sequence_congr {A B : Type} (items : List A) (left right : A → Option B)
    (same : ∀ item ∈ items, left item = right item) : items.mapM left = items.mapM right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons,List.mapM_cons,same head (by simp),ih (by intro item member;exact same item (by simp [member]))]

theorem bytes_congr (before after : ByteMemory) (address count : Nat)
    (same : ∀ offset < count, after (address + offset) = before (address + offset)) :
    readBytes after address count = readBytes before address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
    have head : after address = before address := by simpa using same 0 (by omega)
    have tail := ih (address + 1) (by
      intro offset within
      simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using same (offset + 1) (by omega))
    rw [readBytes,readBytes,head,tail]

theorem word_congr (before after : ByteMemory) (address : Nat)
    (same : ∀ offset < 8, after (address + offset) = before (address + offset)) :
    word after address = word before address := by
  unfold word
  rw [bytes_congr before after address 8 same]

theorem bytes_known (memory : ByteMemory) (address : Nat) (values : List (BitVec 8))
    (known : ∀ index : Fin values.length, memory (address + index.val) = some (values.get index)) :
    readBytes memory address values.length = some values := by
  induction values generalizing address with
  | nil => rfl
  | cons head tail ih =>
    have first : memory address = some head := by
      have seen := known ⟨0,by simp⟩
      change memory (address + 0) = some head at seen
      simpa only [Nat.add_zero] using seen
    have later := ih (address + 1) (by
      intro index
      have seen := known ⟨index.val + 1,by simp only [List.length_cons];omega⟩
      change memory (address + (index.val + 1)) = some (tail.get index) at seen
      simpa only [Nat.add_assoc,Nat.add_comm 1 index.val] using seen)
    rw [List.length_cons,readBytes,first,later]
    rfl

theorem word_known (memory : ByteMemory) (address : Nat) (value : Word)
    (known : ∀ index, ∀ inside : index < 8, memory (address + index) =
      some ((unpackBytes 8 value)[index]'(by rw [unpackBytes_length];exact inside))) :
    word memory address = some value := by
  have loaded := bytes_known memory address (unpackBytes 8 value) (by
    intro index
    simpa only [List.get_eq_getElem] using known index.val (by simpa only [unpackBytes_length] using index.isLt))
  rw [unpackBytes_length] at loaded
  rw [word,loaded,Option.map_some,pack_unpack64]

theorem row_congr (layout : Layout) (before after : ByteMemory) (index : Nat)
    (same : ∀ column < layout.width, word after (layout.address index column) = word before (layout.address index column)) :
    row layout after index = row layout before index :=
  sequence_congr _ _ _ (by intro column member;exact same column (List.mem_range.mp member))

theorem rowsBefore_congr (layout : Layout) (before after : ByteMemory) (count : Nat)
    (same : ∀ index < count, row layout after index = row layout before index) :
    rowsBefore layout after count = rowsBefore layout before count :=
  sequence_congr _ _ _ (by intro index member;exact same index (List.mem_range.mp member))

theorem observe_congr (layout : Layout) (before after : ByteMemory) (count : Word)
    (countBefore : word before layout.count = some count) (countAfter : word after layout.count = some count)
    (same : ∀ index < count.toNat, row layout after index = row layout before index) :
    observe layout after = observe layout before := by
  simp only [observe,countBefore,countAfter,Option.bind_some]
  exact rowsBefore_congr layout before after count.toNat same

theorem rowsBefore_succ (layout : Layout) (memory : ByteMemory) (count : Nat) :
    rowsBefore layout memory (count + 1) =
      (rowsBefore layout memory count).bind (fun earlier => (row layout memory count).map (fun last => earlier ++ [last])) := by
  simp [rowsBefore,List.range_succ,List.mapM_append]
  cases (List.range count).mapM (row layout memory) <;> cases row layout memory count <;> rfl

theorem row_word_inside (layout : Layout) (count index column : Nat)
    (inside : index < count) (columnInside : column < layout.width) :
    layout.rows ≤ layout.address index column ∧
      layout.address index column + 8 ≤ layout.rows + 8 * (count * layout.width) := by
  have bound := Nat.mul_le_mul_right layout.width (show index + 1 ≤ count by omega)
  rw [Nat.add_mul] at bound
  unfold Layout.address
  omega

theorem word_write_separate (memory : ByteMemory) (written valueAt : Nat) (value : Word)
    (apart : written + 8 ≤ valueAt ∨ valueAt + 8 ≤ written) :
    word (writeBytes memory written (unpackBytes 8 value)) valueAt = word memory valueAt := by
  apply word_congr
  intro offset within
  apply word_write_preserves_outside
  rcases apart with before | after <;> omega

theorem prepare_hidden (layout : Layout) (memory : ByteMemory) (count : Word) (written : Nat) (value : Word)
    (countRead : word memory layout.count = some count)
    (beyond : layout.rows + 8 * (count.toNat * layout.width) ≤ written)
    (countApart : written + 8 ≤ layout.count ∨ layout.count + 8 ≤ written) :
    observe layout (writeBytes memory written (unpackBytes 8 value)) = observe layout memory := by
  apply observe_congr layout memory _ count countRead
  · exact (word_write_separate memory written layout.count value countApart).trans countRead
  · intro index inside
    apply row_congr
    intro column columnInside
    exact word_write_separate memory written (layout.address index column) value
      (Or.inr (by have := row_word_inside layout count.toNat index column inside columnInside;omega))

def Layout.countApart (layout : Layout) (count : Nat) : Prop :=
  layout.count + 8 ≤ layout.rows ∨ layout.rows + 8 * (count * layout.width) ≤ layout.count

instance (layout : Layout) (count : Nat) : Decidable (layout.countApart count) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem row_preserved_by_count (layout : Layout) (memory : ByteMemory) (count index : Nat) (value : Word)
    (apart : layout.countApart count) (inside : index < count) :
    row layout (writeBytes memory layout.count (unpackBytes 8 value)) index = row layout memory index := by
  apply row_congr
  intro column columnInside
  apply word_write_separate
  have bounds := row_word_inside layout count index column inside columnInside
  rcases apart with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem commit_count (layout : Layout) (memory : ByteMemory) (count : Word)
    (noWrap : count.toNat + 1 < 2 ^ 64) (apart : layout.countApart (count.toNat + 1)) :
    observe layout (writeBytes memory layout.count (unpackBytes 8 (BitVec.ofNat 64 (count.toNat + 1)))) =
      (rowsBefore layout memory count.toNat).bind
        (fun earlier => (row layout memory count.toNat).map (fun last => earlier ++ [last])) := by
  have updated : word (writeBytes memory layout.count (unpackBytes 8 (BitVec.ofNat 64 (count.toNat + 1)))) layout.count =
      some (BitVec.ofNat 64 (count.toNat + 1)) := word_read_after_write memory layout.count _
  simp only [observe,updated,Option.bind_some,BitVec.toNat_ofNat,Nat.mod_eq_of_lt noWrap]
  rw [rowsBefore_congr layout memory _ (count.toNat + 1)
    (fun index inside => row_preserved_by_count layout memory _ index _ apart inside),rowsBefore_succ]

theorem commit_appends (layout : Layout) (memory : ByteMemory) (count : Word) (earlier : List (List Word)) (made : List Word)
    (countRead : word memory layout.count = some count) (oldRows : observe layout memory = some earlier)
    (ready : row layout memory count.toNat = some made)
    (noWrap : count.toNat + 1 < 2 ^ 64) (apart : layout.countApart (count.toNat + 1)) :
    observe layout (writeBytes memory layout.count (unpackBytes 8 (BitVec.ofNat 64 (count.toNat + 1)))) =
      some (earlier ++ [made]) := by
  have previous : rowsBefore layout memory count.toNat = some earlier := by
    simpa only [observe,countRead,Option.bind_some] using oldRows
  rw [commit_count layout memory count noWrap apart,previous,ready]
  rfl

def zeroTail (layout : Layout) (memory : ByteMemory) (first capacity : Nat) : Prop :=
  ∀ index, first ≤ index → index < capacity → ∀ column < layout.width,
    word memory (layout.address index column) = some 0

theorem zeroTail_write_before (layout : Layout) (memory : ByteMemory) (first capacity written : Nat) (value : Word)
    (zero : zeroTail layout memory first capacity)
    (before : written + 8 ≤ layout.rows + 8 * (first * layout.width)) :
    zeroTail layout (writeBytes memory written (unpackBytes 8 value)) first capacity := by
  intro index later inside column columnInside
  have ordered := Nat.mul_le_mul_right layout.width later
  have apart : written + 8 ≤ layout.address index column := by unfold Layout.address;omega
  rw [word_write_separate memory written _ value (Or.inl apart)]
  exact zero index later inside column columnInside

def writeWords (memory : ByteMemory) : Nat → List Word → ByteMemory
  | _, [] => memory
  | address, value :: later => writeWords (writeBytes memory address (unpackBytes 8 value)) (address + 8) later

theorem writeWords_outside (memory : ByteMemory) (address other : Nat) (values : List Word)
    (outside : other < address ∨ address + 8 * values.length ≤ other) :
    writeWords memory address values other = memory other := by
  induction values generalizing memory address with
  | nil => rfl
  | cons value later ih =>
    rw [writeWords,ih]
    · apply word_write_preserves_outside
      simp only [List.length_cons] at outside
      omega
    · simp only [List.length_cons] at outside
      omega

theorem written_word (memory : ByteMemory) (address : Nat) (values : List Word) (index : Fin values.length) :
    word (writeWords memory address values) (address + 8 * index.val) = some (values.get index) := by
  induction values generalizing memory address with
  | nil => exact Fin.elim0 index
  | cons value later ih =>
    cases index using Fin.cases with
    | zero =>
      have same : word (writeWords (writeBytes memory address (unpackBytes 8 value)) (address + 8) later) address =
          word (writeBytes memory address (unpackBytes 8 value)) address := by
        apply word_congr
        intro offset within
        exact writeWords_outside _ _ _ later (Or.inl (by omega))
      simpa only [writeWords,Fin.val_zero,Nat.mul_zero,Nat.add_zero,List.get_eq_getElem,List.getElem_cons_zero]
        using same.trans (word_read_after_write memory address value)
    | succ index =>
      simpa only [writeWords,Fin.val_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,List.get_eq_getElem,
        List.getElem_cons_succ,Nat.add_comm 8 (8 * index.val)] using
        ih (writeBytes memory address (unpackBytes 8 value)) (address + 8) index

theorem row_after_writeWords (layout : Layout) (memory : ByteMemory) (index : Nat) (values : List Word)
    (sized : values.length = layout.width) :
    row layout (writeWords memory (layout.address index 0) values) index = some values := by
  unfold row
  have allReads : (List.range layout.width).mapM
      (fun column => word (writeWords memory (layout.address index 0) values) (layout.address index column)) =
      (List.range layout.width).mapM (fun column => some (values[column]?.getD 0)) := by
    apply sequence_congr
    intro column member
    have inside : column < values.length := by rw [sized];exact List.mem_range.mp member
    have position : layout.address index column = layout.address index 0 + 8 * column := by
      simp [Layout.address,Nat.mul_add,Nat.add_assoc]
    rw [position,written_word memory _ values ⟨column,inside⟩]
    simp only [List.get_eq_getElem,List.getElem?_eq_getElem inside,Option.getD_some]
  rw [allReads]
  have collect : (List.range layout.width).mapM (fun column => some (values[column]?.getD 0)) =
      some ((List.range layout.width).map (fun column => values[column]?.getD 0)) := List.mapM_pure
  rw [collect]
  congr 1
  apply List.ext_getElem (by simp [sized])
  intro column left right
  have inside : column < values.length := right
  simp [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem inside]

theorem prepare_row (layout : Layout) (memory : ByteMemory) (count : Word) (values : List Word)
    (sized : values.length = layout.width) (countRead : word memory layout.count = some count)
    (apart : layout.countApart (count.toNat + 1)) :
    let after := writeWords memory (layout.address count.toNat 0) values
    word after layout.count = some count ∧ observe layout after = observe layout memory ∧
      row layout after count.toNat = some values := by
  have start : layout.address count.toNat 0 = layout.rows + 8 * (count.toNat * layout.width) := by simp [Layout.address]
  have countUnchanged : word (writeWords memory (layout.address count.toNat 0) values) layout.count = word memory layout.count := by
    apply word_congr
    intro offset within
    apply writeWords_outside
    rcases apart with before | after
    · exact Or.inl (by rw [start];omega)
    · exact Or.inr (by rw [start,sized];rw [Nat.add_mul] at after;omega)
  refine ⟨countUnchanged.trans countRead,?_,row_after_writeWords layout memory count.toNat values sized⟩
  apply observe_congr layout memory _ count countRead (countUnchanged.trans countRead)
  intro index inside
  apply row_congr
  intro column columnInside
  apply word_congr
  intro offset within
  apply writeWords_outside
  have bounds := row_word_inside layout count.toNat index column inside columnInside
  exact Or.inl (by rw [start];omega)

#print axioms prepare_hidden
#print axioms commit_count
#print axioms commit_appends
#print axioms zeroTail_write_before
#print axioms prepare_row
end Mettapedia.Machines.TIsa.RowTableView
