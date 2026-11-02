import Mettapedia.Machines.RelationHoldReceipts
import Init.Data.UInt.Lemmas

/-!
# Finite-word realization of relation ownership counters

The worker uses UInt32 post-increment and pre-decrement tests, as the relation
implementations do. Its interpretation is the existing natural column-count
model. Increment refinement requires enough room for every occurrence of an
ID in the inserted row; removal requires the existing row's positive demand.

An executable preflight checks the entire row before any update. This is a
permission law for admission, not a claim that the current C code performs
this check. The controls expose wrapping and the repeated-column boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationWordOwnership

open RelationColumnOwnership

variable {Id : Type} [DecidableEq Id]

def modulus : Nat := 4294967296

structure Words (Id : Type) where
  uses : Id → UInt32
  owned : Finset Id

def interpret (state : Words Id) : Counters Id :=
  ⟨fun id => (state.uses id).toNat, state.owned⟩

def holdWord (state : Words Id) (id : Id) : Words Id :=
  ⟨Function.update state.uses id (state.uses id + 1),
    if state.uses id = 0 then insert id state.owned else state.owned⟩

def unholdWord (state : Words Id) (id : Id) : Words Id :=
  let next := state.uses id - 1
  ⟨Function.update state.uses id next,
    if next = 0 then state.owned.erase id else state.owned⟩

def holdWords : Words Id → List Id → Words Id
  | state, [] => state
  | state, id :: rest => holdWords (holdWord state id) rest

def unholdWords : Words Id → List Id → Words Id
  | state, [] => state
  | state, id :: rest => unholdWords (unholdWord state id) rest

def acquireWords : Words Id → List Id → List Id
  | _, [] => []
  | state, id :: rest =>
      (if state.uses id = 0 then [id] else []) ++ acquireWords (holdWord state id) rest

def releaseWords : Words Id → List Id → List Id
  | _, [] => []
  | state, id :: rest =>
      (if state.uses id - 1 = 0 then [id] else []) ++ releaseWords (unholdWord state id) rest

theorem word_zero (word : UInt32) : word = 0 ↔ word.toNat = 0 := by
  rw [← UInt32.toNat_inj]
  rfl

theorem word_increment (word : UInt32) (room : word.toNat + 1 < modulus) :
    (word + 1).toNat = word.toNat + 1 := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt room

theorem word_decrement (word : UInt32) (positive : 0 < word.toNat) :
    (word - 1).toNat = word.toNat - 1 := by
  apply UInt32.toNat_sub_of_le
  rw [UInt32.le_iff_toNat_le]
  exact positive

theorem decremented_zero (word : UInt32) (positive : 0 < word.toNat) :
    word - 1 = 0 ↔ word.toNat = 1 := by
  rw [word_zero, word_decrement word positive]
  omega

theorem interpret_update (uses : Id → UInt32) (id : Id) (value : UInt32) :
    (fun key => (Function.update uses id value key).toNat) =
      Function.update (fun key => (uses key).toNat) id value.toNat := by
  funext key
  by_cases same : key = id <;> simp [same]

theorem holdWord_refines (state : Words Id) (id : Id)
    (room : (state.uses id).toNat + 1 < modulus) :
    interpret (holdWord state id) = hold (interpret state) id := by
  simp only [interpret, holdWord, hold, interpret_update, word_increment _ room, word_zero]
  rfl

theorem unholdWord_refines (state : Words Id) (id : Id) (positive : 0 < (state.uses id).toNat) :
    interpret (unholdWord state id) = unhold (interpret state) id := by
  simp only [interpret, unholdWord, unhold, interpret_update,
    word_decrement _ positive, decremented_zero _ positive]
  rfl

def FitsAddition (state : Words Id) (row : List Id) : Prop :=
  ∀ id, (state.uses id).toNat + row.count id < modulus

theorem addition_head_room (state : Words Id) (id : Id) (rest : List Id)
    (room : FitsAddition state (id :: rest)) : (state.uses id).toNat + 1 < modulus := by
  have bound := room id
  simp only [List.count_cons_self] at bound
  omega

theorem addition_tail_room (state : Words Id) (id : Id) (rest : List Id)
    (room : FitsAddition state (id :: rest)) : FitsAddition (holdWord state id) rest := by
  intro key
  have bound := room key
  have head := addition_head_room state id rest room
  by_cases same : key = id
  · subst key
    simp only [holdWord, Function.update_self, word_increment _ head]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
  · simpa [holdWord, same, Ne.symm same] using bound

theorem holdWords_refines (state : Words Id) (row : List Id) (room : FitsAddition state row) :
    interpret (holdWords state row) = holdColumns (interpret state) row := by
  induction row generalizing state with
  | nil => rfl
  | cons id rest ih =>
      rw [holdWords, ih _ (addition_tail_room state id rest room),
        holdWord_refines state id (addition_head_room state id rest room)]
      rfl

theorem acquireWords_refines (state : Words Id) (row : List Id) (room : FitsAddition state row) :
    acquireWords state row = RelationHoldReceipts.acquired (interpret state) row := by
  induction row generalizing state with
  | nil => rfl
  | cons id rest ih =>
      rw [acquireWords, ih _ (addition_tail_room state id rest room),
        holdWord_refines state id (addition_head_room state id rest room), RelationHoldReceipts.acquired]
      simp [interpret, word_zero]
      rfl

theorem unholdWords_refines (state : Words Id) (row : List Id)
    (safe : SafeRemoval (interpret state) row) :
    interpret (unholdWords state row) = unholdColumns (interpret state) row := by
  induction row generalizing state with
  | nil => rfl
  | cons id rest ih =>
      have head : 0 < (state.uses id).toNat := safe.1
      have tail : SafeRemoval (interpret (unholdWord state id)) rest := by
        rw [unholdWord_refines state id head]
        exact safe.2
      rw [unholdWords, ih _ tail, unholdWord_refines state id head]
      rfl

theorem releaseWords_refines (state : Words Id) (row : List Id)
    (safe : SafeRemoval (interpret state) row) :
    releaseWords state row = RelationHoldReceipts.released (interpret state) row := by
  induction row generalizing state with
  | nil => rfl
  | cons id rest ih =>
      have head : 0 < (state.uses id).toNat := safe.1
      have tail : SafeRemoval (interpret (unholdWord state id)) rest := by
        rw [unholdWord_refines state id head]
        exact safe.2
      rw [releaseWords, ih _ tail, unholdWord_refines state id head, RelationHoldReceipts.released]
      simp only [decremented_zero _ head, interpret]
      rfl

/-- Count repeated columns in the preflight; checking each against the old
counter plus one would miss their combined demand. The test uses natural
arithmetic, so the admission test itself cannot wrap. -/
def checkAddition (state : Words Id) (row : List Id) : Bool :=
  row.all (fun id => decide ((state.uses id).toNat + row.count id < modulus))

theorem checkAddition_iff (state : Words Id) (row : List Id) : checkAddition state row = true ↔ FitsAddition state row := by
  simp only [checkAddition, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro known id
    by_cases member : id ∈ row
    · exact known id member
    · have zero : row.count id = 0 := List.count_eq_zero.mpr member
      simpa [zero, modulus] using (state.uses id).toNat_lt_size
  · intro room id _
    exact room id

def prepare (state : Words Id) (row : List Id) : Option (Words Id) :=
  if checkAddition state row then some (holdWords state row) else none

theorem prepare_refines (state : Words Id) (row : List Id) (after : Words Id)
    (prepared : prepare state row = some after) :
    interpret after = holdColumns (interpret state) row := by
  unfold prepare at prepared
  split at prepared
  · rename_i accepted
    cases Option.some.inj prepared
    exact holdWords_refines state row ((checkAddition_iff state row).mp accepted)
  · simp at prepared

theorem represented_insertion (state : Words Id) (rows : List (List Id)) (row : List Id)
    (valid : (⟨rows, interpret state⟩ : State Id).Valid) (room : FitsAddition state row) :
    (⟨row :: rows, interpret (holdWords state row)⟩ : State Id).Valid := by
  rw [holdWords_refines state row room]
  exact insertRow_valid ⟨rows, interpret state⟩ valid row

theorem represented_removal (state : Words Id) (rows : List (List Id)) (row : List Id)
    (valid : (⟨rows, interpret state⟩ : State Id).Valid) (member : row ∈ rows) :
    (⟨rows.erase row, interpret (unholdWords state row)⟩ : State Id).Valid := by
  rw [unholdWords_refines state row (removeRow_safe ⟨rows, interpret state⟩ valid row member)]
  simpa only [removeRow, member, ↓reduceIte] using removeRow_valid ⟨rows, interpret state⟩ valid row

theorem represented_release_receipt (state : Words Id) (rows : List (List Id)) (row : List Id)
    (valid : (⟨rows, interpret state⟩ : State Id).Valid) (member : row ∈ rows) :
    releaseWords state row = RelationHoldReceipts.released (interpret state) row :=
  releaseWords_refines state row (removeRow_safe ⟨rows, interpret state⟩ valid row member)

/-- A representable addition is checked by subtraction from the maximum,
not by first performing the potentially overflowing addition. -/
def wordBudget (old : UInt32) (added : Nat) : Bool :=
  if added < modulus then decide (UInt32.ofNat added ≤ 4294967295 - old) else false

theorem wordBudget_iff (old : UInt32) (added : Nat) :
    wordBudget old added = true ↔ old.toNat + added < modulus := by
  have bounded := old.toNat_lt_size
  have below : old ≤ (4294967295 : UInt32) := by
    rw [UInt32.le_iff_toNat_le]
    change old.toNat ≤ 4294967295
    change old.toNat < 4294967296 at bounded
    omega
  by_cases fits : added < modulus
  · simp only [wordBudget, fits, ↓reduceIte, decide_eq_true_eq, UInt32.le_iff_toNat_le,
      UInt32.toNat_ofNat_of_lt' fits, UInt32.toNat_sub_of_le _ _ below]
    change added ≤ 4294967295 - old.toNat ↔ old.toNat + added < 4294967296
    change old.toNat < 4294967296 at bounded
    omega
  · simp only [wordBudget, fits, ↓reduceIte, Bool.false_eq_true, false_iff]
    omega

def admitWords (state : Words Id) (row : List Id) : Bool :=
  row.all (fun id => wordBudget (state.uses id) (row.count id))

theorem admitWords_iff (state : Words Id) (row : List Id) :
    admitWords state row = true ↔ FitsAddition state row := by
  rw [← checkAddition_iff state row]
  simp only [admitWords, checkAddition, List.all_eq_true, wordBudget_iff, decide_eq_true_eq]

namespace Controls

def nearlyFull : Words Nat := ⟨fun id => if id = 7 then 4294967294 else 0, {7}⟩

theorem repeated_column_is_checked_as_two_uses : checkAddition nearlyFull [7, 7, 9] = false := by decide

theorem one_remaining_use_is_admitted : checkAddition nearlyFull [7, 9] = true := by decide

theorem unchecked_wrap_breaks_counter_support :
    ((holdWords nearlyFull [7, 7, 9]).uses 7).toNat = 0 ∧
      7 ∈ (holdWords nearlyFull [7, 7, 9]).owned := by decide

theorem preflight_refuses_before_the_updates : prepare nearlyFull [7, 7, 9] = none := by decide

theorem decrementing_zero_does_not_mean_zero : ((0 : UInt32) - 1).toNat = 4294967295 := by decide

theorem wrapped_count_can_release_before_the_last_fact :
    let logical : Counters Nat :=
      ⟨fun id => if id = 7 then 4294967299 else if id = 8 then 1 else 0, {7, 8}⟩
    let words : Words Nat :=
      ⟨fun id => if id = 7 then UInt32.ofNat 4294967299 else if id = 8 then 1 else 0, {7, 8}⟩
    releaseWords words [7, 7, 7, 7, 7, 7, 7, 8] = [7, 8] ∧
      RelationHoldReceipts.released logical [7, 7, 7, 7, 7, 7, 7, 8] = [8] := by decide

end Controls
end Mettapedia.Machines.RelationWordOwnership
