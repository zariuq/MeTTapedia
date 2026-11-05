import Mettapedia.Algebra.TropicalAffineSummary
import Mathlib.Data.Finset.Option
import Mathlib.Tactic

/-!
# A source-shaped remove/add improvement and its keyed realization

A logical slot is absent or holds one value. A strictly better candidate
publishes a replacement and one changed event. The independent row operation
inserts an absent row, or erases its observed old row and inserts the new one.
Its correspondence with the keyed map holds at the completed publication
boundary, on the encoded functional relation. It does not make the two row
mutations atomic or erase intermediate observations, failure or occurrence IDs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement

variable {Key Value : Type} [DecidableEq Key] [LinearOrder Value]

abbrev Store (Key Value : Type) := Key → Option Value

def improve (store : Store Key Value) (key : Key) (candidate : Value) : Store Key Value × Bool :=
  match store key with
  | none => (Function.update store key (some candidate), true)
  | some old => if candidate < old then (Function.update store key (some candidate), true)
      else (store, false)

def denote (store : Store Key Value) (key : Key) : WithTop Value :=
  match store key with
  | none => ⊤
  | some value => value

def lower (store : Key → WithTop Value) (key : Key) (candidate : WithTop Value) : Key → WithTop Value :=
  Function.update store key (min (store key) candidate)

omit [DecidableEq Key] [LinearOrder Value] in
theorem denote_injective : Function.Injective (denote (Key := Key) (Value := Value)) := by
  intro first second same
  funext key
  have point := congrFun same key
  cases a : first key <;> cases b : second key <;> simp_all [denote]

theorem changed_iff (store : Store Key Value) (key : Key) (candidate : Value) :
    (improve store key candidate).2 = true ↔ (candidate : WithTop Value) < denote store key := by
  cases held : store key with
  | none => simp [improve, denote, held]
  | some old => by_cases better : candidate < old <;> simp [improve, denote, held, better]

omit [DecidableEq Key] in
theorem present_of_denote_le (before after : Store Key Value) (bounded : denote after ≤ denote before)
    (key : Key) (value : Value) (present : before key = some value) : ∃ next, after key = some next := by
  cases found : after key with
  | none =>
      have bound := bounded key
      simp [denote, found, present] at bound
  | some next => exact ⟨next, rfl⟩

theorem denote_improve (store : Store Key Value) (key : Key) (candidate : Value) :
    denote (improve store key candidate).1 = lower (denote store) key candidate := by
  funext other
  by_cases same : other = key
  · subst other
    cases held : store key with
    | none => simp [improve, denote, lower, held]
    | some old =>
        by_cases better : candidate < old
        · have h : (candidate : WithTop Value) ≤ old := by exact_mod_cast le_of_lt better
          simp [improve, denote, lower, held, better, min_eq_right h]
        · have h : (old : WithTop Value) ≤ candidate := by exact_mod_cast le_of_not_gt better
          simp [improve, denote, lower, held, better, min_eq_left h]
  · cases held : store key with
    | none => simp [improve, denote, lower, held, same]
    | some old => by_cases better : candidate < old <;> simp [improve, denote, lower, held, better, same]

theorem other_key_unchanged (store : Store Key Value) (key other : Key) (candidate : Value)
    (apart : other ≠ key) : (improve store key candidate).1 other = store other := by
  cases held : store key with
  | none => simp [improve, held, apart]
  | some old => by_cases better : candidate < old <;> simp [improve, held, better, apart]

theorem lower_commutes (store : Key → WithTop Value) (first second : Key)
    (a b : WithTop Value) : lower (lower store first a) second b = lower (lower store second b) first a := by
  funext key
  by_cases same : first = second
  · subst second
    by_cases atKey : key = first <;>
      simp [lower, atKey, min_comm, min_left_comm]
  · by_cases left : key = first <;> by_cases right : key = second <;>
      simp_all [lower, Function.update]

/-- Fixed candidate updates commute on final values, not their changed events. -/
theorem improve_values_commute (store : Store Key Value) (first second : Key) (a b : Value) :
    (improve (improve store first a).1 second b).1 =
      (improve (improve store second b).1 first a).1 := by
  apply denote_injective
  simp only [denote_improve]
  exact lower_commutes _ _ _ _ _

def rowImprove (rows : Finset (Key × Value)) (key : Key) (candidate : Value)
    (observed : Option Value) : Finset (Key × Value) × Bool :=
  match observed with
  | none => (insert (key, candidate) rows, true)
  | some old => if candidate < old then (insert (key, candidate) (rows.erase (key, old)), true)
      else (rows, false)

section FiniteKeys

variable [Fintype Key]

def rows (store : Store Key Value) : Finset (Key × Value) :=
  Finset.univ.biUnion fun key => match store key with
    | none => ∅
    | some value => {(key, value)}

omit [DecidableEq Key] [LinearOrder Value] [Fintype Key] in
theorem mem_fiber (key : Key) (value : Option Value) (entry : Key × Value) :
    entry ∈ (match value with | none => (∅ : Finset (Key × Value)) | some v => {(key, v)}) ↔
      entry.1 = key ∧ value = some entry.2 := by
  cases value <;> cases entry <;> simp [eq_comm]

@[simp] theorem mem_rows (store : Store Key Value) (key : Key) (value : Value) :
    (key, value) ∈ rows store ↔ store key = some value := by
  simp only [rows, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_fiber]
  simp

theorem rows_functional (store : Store Key Value) (key : Key) (left right : Value)
    (hl : (key, left) ∈ rows store) (hr : (key, right) ∈ rows store) : left = right := by
  exact Option.some.inj ((mem_rows store key left).1 hl |>.symm.trans ((mem_rows store key right).1 hr))

theorem rows_update_none (store : Store Key Value) (key : Key) (candidate : Value)
    (empty : store key = none) :
    rows (Function.update store key (some candidate)) = insert (key, candidate) (rows store) := by
  ext entry
  rcases entry with ⟨other, value⟩
  by_cases same : other = key
  · subst other
    simp [empty, eq_comm]
  · simp [same, Function.update]

theorem rows_update_some (store : Store Key Value) (key : Key) (candidate old : Value)
    (held : store key = some old) :
    rows (Function.update store key (some candidate)) = insert (key, candidate) ((rows store).erase (key, old)) := by
  ext entry
  rcases entry with ⟨other, value⟩
  by_cases same : other = key
  · subst other
    simp [held, eq_comm]
  · simp [same, Function.update]

/-- One completed source-style update preserves the entire functional relation
and the exact strict-improvement publication flag. -/
theorem row_improve_refines (store : Store Key Value) (key : Key) (candidate : Value) :
    rowImprove (rows store) key candidate (store key) =
      (rows (improve store key candidate).1, (improve store key candidate).2) := by
  cases held : store key with
  | none => simp [rowImprove, improve, held, rows_update_none store key candidate held]
  | some old =>
      by_cases better : candidate < old <;>
        simp [rowImprove, improve, held, better, rows_update_some store key candidate old held]

end FiniteKeys

theorem nat_lower_is_tropical_cap (store : Key → WithTop Nat) (key : Key) (candidate : WithTop Nat) :
    Tropical.trop (lower store key candidate key) =
      (Mettapedia.Algebra.AffineSummary.minPlus (0 : Nat) candidate).act (Tropical.trop (store key)) := by
  rw [Mettapedia.Algebra.AffineSummary.act_minPlus]
  simp [lower]

namespace Controls

def ten : Store Unit Nat := fun _ => some 10

theorem same_final_different_changed_events :
    (improve (improve ten () 7).1 () 5).1 () = some 5 ∧
    (improve (improve ten () 5).1 () 7).1 () = some 5 ∧
    [(improve ten () 7).2, (improve (improve ten () 7).1 () 5).2] = [true, true] ∧
    [(improve ten () 5).2, (improve (improve ten () 5).1 () 7).2] = [true, false] := by decide

theorem removal_has_visible_intermediate_absence :
    (((), 10) ∈ rows ten) ∧ (rows ten).erase ((), 10) = ∅ ∧
      rowImprove (rows ten) () 7 (some 10) = ({((), 7)}, true) := by decide

theorem stale_observation_breaks_single_value_invariant :
    rowImprove {((), 7)} () 5 (some 10) = ({((), 5), ((), 7)}, true) := by decide

end Controls

end Mettapedia.Machines.KeyedImprovement
