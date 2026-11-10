import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Counted ordered deletion and bounded selection

The source operation removes at most a requested number of matching list
occurrences. The independently computed selection records those occurrences
and stops inspecting the list once the quota is met. Exact-quota deletion is
a separate policy; shortage refuses without exposing a partial result.

The predicate is pure and completed. A failed or interrupted matcher is not a
false predicate value, and effectful predicate evaluation needs another model.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.CountedErase

universe u v
variable {Row : Type u}

def eraseUpTo (select : Row → Bool) : Nat → List Row → List Row
  | 0, rows => rows
  | _ + 1, [] => []
  | count + 1, row :: rest =>
      if select row then eraseUpTo select count rest
      else row :: eraseUpTo select (count + 1) rest

/-- The second component counts predicate inspections, not CPU instructions. -/
def scan (select : Row → Bool) : Nat → List Row → List Row × Nat
  | 0, _ => ([], 0)
  | _ + 1, [] => ([], 0)
  | count + 1, row :: rest =>
      if select row then
        let later := scan select count rest
        (row :: later.1, later.2 + 1)
      else
        let later := scan select (count + 1) rest
        (later.1, later.2 + 1)

theorem prefix_values (select : Row → Bool) (count : Nat) (rows : List Row) :
    (scan select count rows).1 = (rows.filter select).take count := by
  induction rows generalizing count with
  | nil => cases count <;> rfl
  | cons row rest ih =>
      cases count with
      | zero => rfl
      | succ count =>
          cases selected : select row <;> simp [scan, selected, ih]

theorem prefix_sublist (select : Row → Bool) (count : Nat) (rows : List Row) :
    (scan select count rows).1.Sublist rows := by
  rw [prefix_values]
  exact (List.take_sublist count _).trans List.filter_sublist

theorem prefix_length (select : Row → Bool) (count : Nat) (rows : List Row) :
    (scan select count rows).1.length = min count (rows.filter select).length := by
  rw [prefix_values, List.length_take]

theorem prefix_inspections_le_length (select : Row → Bool) (count : Nat) (rows : List Row) :
    (scan select count rows).2 ≤ rows.length := by
  induction rows generalizing count with
  | nil => cases count <;> simp [scan]
  | cons row rest ih =>
      cases count with
      | zero => simp [scan]
      | succ count =>
          cases selected : select row <;> simp only [scan, selected, Bool.false_eq_true,
            if_false, if_true, List.length_cons]
          · exact Nat.add_le_add_right (ih (count + 1)) 1
          · exact Nat.add_le_add_right (ih count) 1

theorem partition_length (select : Row → Bool) (count : Nat) (rows : List Row) :
    (eraseUpTo select count rows).length + (scan select count rows).1.length = rows.length := by
  induction rows generalizing count with
  | nil => cases count <;> rfl
  | cons row rest ih =>
      cases count with
      | zero => simp [eraseUpTo, scan]
      | succ count =>
          cases selected : select row with
          | false =>
              have counts := ih (count + 1)
              simp [eraseUpTo, scan, selected]
              omega
          | true =>
              have counts := ih count
              simp [eraseUpTo, scan, selected]
              omega

theorem erase_preserves_order (select : Row → Bool) (count : Nat) (rows : List Row) :
    (eraseUpTo select count rows).Sublist rows := by
  induction rows generalizing count with
  | nil => cases count <;> exact .slnil
  | cons row rest ih =>
      cases count with
      | zero => exact .refl _
      | succ count =>
          cases selected : select row with
          | false => simpa [eraseUpTo, selected] using (ih (count + 1)).cons_cons row
          | true => simpa [eraseUpTo, selected] using (ih count).cons row

/-- Exact quota is explicitly distinct from removing as much as possible. -/
def eraseExactly (select : Row → Bool) (count : Nat) (rows : List Row) : Option (List Row) :=
  if (scan select count rows).1.length = count then some (eraseUpTo select count rows) else none

theorem exact_accepted_iff (select : Row → Bool) (count : Nat) (rows kept : List Row) :
    eraseExactly select count rows = some kept ↔
      count ≤ (rows.filter select).length ∧ eraseUpTo select count rows = kept := by
  simp [eraseExactly, prefix_length]

theorem shortage_refuses (select : Row → Bool) (count : Nat) (rows : List Row)
    (short : (rows.filter select).length < count) : eraseExactly select count rows = none := by
  simp [eraseExactly, prefix_length, Nat.min_eq_right (Nat.le_of_lt short), Nat.ne_of_lt short]

theorem exact_count (select : Row → Bool) (count : Nat) (rows kept : List Row)
    (accepted : eraseExactly select count rows = some kept) : kept.length + count = rows.length := by
  obtain ⟨enough, rfl⟩ := (exact_accepted_iff select count rows kept).mp accepted
  simpa only [prefix_length, Nat.min_eq_left enough] using partition_length select count rows

/-- Once the quota has been met, an arbitrary tail is not inspected. -/
theorem full_prefix_stops_before_tail (select : Row → Bool) (before after : List Row) (count : Nat)
    (met : count ≤ (before.filter select).length) :
    scan select count (before ++ after) = scan select count before := by
  induction before generalizing count with
  | nil =>
      have zero : count = 0 := by simpa using met
      subst count
      simp [scan]
  | cons row rest ih =>
      cases count with
      | zero => rfl
      | succ count =>
          cases selected : select row with
          | false =>
              have enough : count + 1 ≤ (rest.filter select).length := by simpa [selected] using met
              simp [scan, selected, ih _ enough]
          | true =>
              have enough : count ≤ (rest.filter select).length := by simpa [selected] using met
              simp [scan, selected, ih _ enough]

/-- Decoding values commutes with the independent source deletion. -/
theorem erase_map {Other : Type v} (decode : Row → Other) (select : Other → Bool)
    (count : Nat) (rows : List Row) :
    (eraseUpTo (fun row => select (decode row)) count rows).map decode =
      eraseUpTo select count (rows.map decode) := by
  induction rows generalizing count with
  | nil => cases count <;> rfl
  | cons row rest ih =>
      cases count with
      | zero => rfl
      | succ count =>
          cases selected : select (decode row) <;> simp [eraseUpTo, selected, ih]

/-- For unique physical identities, stable contraction by the selected
identities equals the source deletion. Payload values need not be unique. -/
theorem filter_selected [DecidableEq Row] (select : Row → Bool) (count : Nat) (rows : List Row)
    (unique : rows.Nodup) :
    (rows.filter fun row => decide (row ∉ (scan select count rows).1)) = eraseUpTo select count rows := by
  induction rows generalizing count with
  | nil => cases count <;> rfl
  | cons row rest ih =>
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      cases count with
      | zero => simp [scan, eraseUpTo]
      | succ count =>
          cases selected : select row with
          | false =>
              have notSelected : row ∉ (scan select (count + 1) rest).1 :=
                fun member => absent ((prefix_sublist select (count + 1) rest).subset member)
              simpa [scan, eraseUpTo, selected, notSelected] using
                congrArg (List.cons row) (ih (count + 1) uniqueRest)
          | true =>
              simp only [scan, eraseUpTo, selected, if_true]
              have tailFilter :
                  (rest.filter fun other => decide (other ∉ row :: (scan select count rest).1)) =
                    rest.filter (fun other => decide (other ∉ (scan select count rest).1)) := by
                apply List.filter_congr
                intro other member
                have different : other ≠ row := by
                  intro same
                  subst other
                  exact absent member
                simp [different]
              calc
                ((row :: rest).filter fun other => decide (other ∉ row :: (scan select count rest).1)) =
                    rest.filter (fun other => decide (other ∉ row :: (scan select count rest).1)) := by simp
                _ = rest.filter (fun other => decide (other ∉ (scan select count rest).1)) := tailFilter
                _ = eraseUpTo select count rest := ih count uniqueRest

namespace Controls

theorem equal_payloads_are_counted_separately :
    eraseUpTo (· == 7) 1 [7, 8, 7] = [8, 7] ∧
      eraseUpTo (· == 7) 2 [7, 8, 7] = [8] := by decide

theorem exact_and_up_to_differ_on_shortage :
    eraseExactly (· == 7) 2 [7, 8] = none ∧
      eraseUpTo (· == 7) 2 [7, 8] = [8] := by decide

theorem first_match_skips_the_unused_tail :
    scan (· == 7) 1 [7, 8, 9, 10] = ([7], 1) ∧
      scan (· == 7) 1 [8, 9, 7, 10] = ([7], 3) := by decide

end Controls
end Mettapedia.Data.List.CountedErase
