import Mettapedia.Machines.OrderedDependencyClassification

/-!
# Classified removal with and without a tail move

Some storage kinds close a hole by moving the last occurrence into it.
When deciding whether a projected clock can stay fixed, the classifier
must consider the erased occurrence and the one moved across intervening
rows. The stable case considers only the erased occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyRemoval

open OrderedDependencyClassification OrderedDependencyProjection

universe u v w
variable {Entry : Type u} {Projection : Type v} {Value : Type w} {size : Nat}

def movedTail (rows : List Entry) (index : Nat) : Option Entry :=
  if index + 1 < rows.length then rows.getLast? else none

def swapErase : List Entry → Nat → List Entry
  | [], _ => []
  | _ :: suffix, 0 => match suffix.getLast? with
    | none => []
    | some tail => tail :: suffix.dropLast
  | first :: suffix, index + 1 => first :: swapErase suffix index

def erase (stable : Bool) (rows : List Entry) (index : Nat) : List Entry :=
  if stable then rows.eraseIdx index else swapErase rows index

def affected (stable : Bool) (rows : List Entry) (index : Nat) : List Entry :=
  rows[index]?.toList ++ (if stable then [] else (movedTail rows index).toList)

theorem length_swapErase (rows : List Entry) (index : Nat) (within : index < rows.length) :
    (swapErase rows index).length = rows.length - 1 := by
  induction rows generalizing index with
  | nil => simp at within
  | cons first rest ih =>
    cases index with
    | zero =>
      cases rest with
      | nil => rfl
      | cons second rest =>
        rw [swapErase, List.getLast?_eq_some_getLast (by simp)]
        simp
    | succ index =>
      have inner : index < rest.length := by simpa using within
      simp only [swapErase, List.length_cons, ih index inner]
      omega

theorem length_erase (stable : Bool) (rows : List Entry) (index : Nat)
    (within : index < rows.length) : (erase stable rows index).length = rows.length - 1 := by
  cases stable
  · exact length_swapErase rows index within
  · exact List.length_eraseIdx_of_lt within

private theorem eraseIdx_retains (view : Entry → Option Value) (rows : List Entry) (index : Nat)
    (invisible : ∀ row ∈ rows[index]?.toList, view row = none) :
    (rows.eraseIdx index).filterMap view = rows.filterMap view := by
  induction rows generalizing index with
  | nil => cases index <;> rfl
  | cons first rest ih =>
    cases index with
    | zero =>
      have erased := invisible first (by simp)
      simp [erased]
    | succ index =>
      have later := ih index (fun row present => invisible row (by simpa using present))
      simp [List.filterMap_cons, later]

private theorem moved_tail_succ (first : Entry) (rest : List Entry) (index : Nat) :
    movedTail (first :: rest) (index + 1) = movedTail rest index := by
  cases rest with
  | nil => simp [movedTail]
  | cons next rest => simp [movedTail]

private theorem swapErase_retains (view : Entry → Option Value) (rows : List Entry) (index : Nat)
    (erased : ∀ row ∈ rows[index]?.toList, view row = none)
    (moved : ∀ row ∈ (movedTail rows index).toList, view row = none) :
    (swapErase rows index).filterMap view = rows.filterMap view := by
  induction rows generalizing index with
  | nil => cases index <;> rfl
  | cons first rest ih =>
    cases index with
    | zero =>
      have dropped := erased first (by simp)
      cases rest with
      | nil => simp [swapErase, dropped]
      | cons second suffix =>
        have nonempty : second :: suffix ≠ [] := by simp
        let tail := (second :: suffix).getLast nonempty
        have tailLast : (second :: suffix).getLast? = some tail :=
          List.getLast?_eq_some_getLast nonempty
        have invisible : view tail = none := moved tail (by simp [movedTail, tailLast])
        have accounting : (second :: suffix).dropLast ++ [tail] = second :: suffix :=
          List.dropLast_concat_getLast nonempty
        have viewEq := congrArg (List.filterMap view) accounting
        simp only [List.filterMap_append, List.filterMap_cons, invisible, List.filterMap_nil,
          List.append_nil] at viewEq
        simpa only [swapErase, tailLast, List.filterMap_cons, dropped, invisible] using viewEq
    | succ index =>
      have remaining := ih index
        (fun row present => erased row (by simpa using present))
        (fun row present => moved row (by simpa only [moved_tail_succ] using present))
      simp [swapErase, List.filterMap_cons, remaining]

theorem erase_retains (view : Entry → Option Value) (stable : Bool)
    (rows : List Entry) (index : Nat)
    (invisible : ∀ row ∈ affected stable rows index, view row = none) :
    (erase stable rows index).filterMap view = rows.filterMap view := by
  have erased : ∀ row ∈ rows[index]?.toList, view row = none := by
    intro row member
    exact invisible row (List.mem_append_left _ member)
  cases stable with
  | true => exact eraseIdx_retains view rows index erased
  | false =>
    refine swapErase_retains view rows index erased ?_
    intro row member
    exact invisible row (List.mem_append_right _ member)

def publishErase (rowBump : Projection → Entry → Bool)
    (s : State Entry Projection size) (writer : Fin size) (stable : Bool) (index : Nat) :
    State Entry Projection size :=
  let rows := (s.store.members writer).own
  publish s writer (erase stable rows index) true
    (fun slot => (affected stable rows index).any (rowBump slot))

theorem covers_erase (project : Projection → Entry → Option Value)
    (rowBump : Projection → Entry → Bool)
    (coversRow : ∀ slot row, rowBump slot row = false → project slot row = none)
    (s : State Entry Projection size) (writer : Fin size) (stable : Bool) (index : Nat) :
    let rows := (s.store.members writer).own
    Covers project s writer (erase stable rows index)
      (fun slot => (affected stable rows index).any (rowBump slot)) := by
  dsimp only
  intro slot skipped
  apply erase_retains
  intro row member
  exact coversRow slot row (Bool.eq_false_iff.mpr (List.any_eq_false.mp skipped row member))

end Mettapedia.Machines.OrderedDependencyRemoval
