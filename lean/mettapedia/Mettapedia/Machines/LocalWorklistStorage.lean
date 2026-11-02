import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Local scratch worklists and owned spills

The live prefix, rather than the spare capacity, is the logical worklist.
A fallible spill overwrites a fresh allocation one cell at a time, preserving
that prefix and its order. Allocation failure retains the original buffer and
ownership. Native allocation sizes, memcpy/realloc and pointer lifetime are
separate C correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.LocalWorklistStorage

variable {A : Type}

def overwrite : List A → List A → Option (List A)
  | [], destination => some destination
  | head :: rest, _ :: tail => (overwrite rest tail).map (head :: ·)
  | _ :: _, [] => none

theorem overwrite_exact (source destination : List A)
    (fits : source.length ≤ destination.length) :
    overwrite source destination = some (source ++ destination.drop source.length) := by
  induction source generalizing destination with
  | nil => simp [overwrite]
  | cons head rest ih =>
      cases destination with
      | nil => simp at fits
      | cons first tail =>
          have smaller : rest.length ≤ tail.length := by simpa using fits
          simp [overwrite, ih tail smaller]

structure Buffer (A : Type) where
  storage : List A
  live : Nat
  owned : Bool
  deriving DecidableEq, Repr

def view (buffer : Buffer A) : List A := buffer.storage.take buffer.live

def reserve (needed : Nat) (allocation : Option (List A)) (before : Buffer A) :
    Except (Buffer A) (Buffer A) :=
  if needed ≤ before.storage.length then .ok before
  else match allocation with
    | none => .error before
    | some fresh =>
        if needed ≤ fresh.length then
          match overwrite (view before) fresh with
          | none => .error before
          | some written => .ok ⟨written, before.live, true⟩
        else .error before

theorem local_avoids_allocation (needed : Nat) (before : Buffer A)
    (fits : needed ≤ before.storage.length) :
    reserve needed none before = .ok before := by
  simp [reserve, fits]

theorem failed_spill_retains_owner (needed : Nat) (before : Buffer A)
    (mustGrow : before.storage.length < needed) :
    reserve needed none before = .error before := by
  simp [reserve, Nat.not_le_of_lt mustGrow]

theorem successful_spill (needed : Nat) (before : Buffer A) (fresh : List A)
    (valid : before.live ≤ before.storage.length)
    (mustGrow : before.storage.length < needed) (enough : needed ≤ fresh.length) :
    reserve needed (some fresh) before =
      .ok ⟨view before ++ fresh.drop before.live, before.live, true⟩ := by
  have prefixLength : (view before).length = before.live := by simp [view, valid]
  have prefixFits : (view before).length ≤ fresh.length := by omega
  simp [reserve, Nat.not_le_of_lt mustGrow, enough,
    overwrite_exact _ _ prefixFits, prefixLength]

theorem spill_preserves_work (needed : Nat) (before : Buffer A) (fresh : List A)
    (valid : before.live ≤ before.storage.length)
    (mustGrow : before.storage.length < needed) (enough : needed ≤ fresh.length) :
    (reserve needed (some fresh) before).map view = .ok (view before) := by
  rw [successful_spill needed before fresh valid mustGrow enough]
  have prefixLength : (view before).length = before.live := by simp [view, valid]
  change Except.ok ((view before ++ fresh.drop before.live).take before.live) = _
  rw [← prefixLength, List.take_left]

theorem spill_preserves_capacity (needed : Nat) (before : Buffer A) (fresh : List A)
    (valid : before.live ≤ before.storage.length)
    (mustGrow : before.storage.length < needed) (enough : needed ≤ fresh.length) :
    (reserve needed (some fresh) before).map (fun after => after.storage.length) =
      .ok fresh.length := by
  rw [successful_spill needed before fresh valid mustGrow enough]
  have prefixLength : (view before).length = before.live := by simp [view, valid]
  simp only [Except.map, List.length_append, List.length_drop, prefixLength]
  have liveFits : before.live ≤ fresh.length := by omega
  congr 1
  omega

namespace Controls

def initial : Buffer Nat := ⟨[7, 9, 99, 88], 2, false⟩

theorem padding_is_not_work : view initial = [7, 9] := by rfl

theorem spill_keeps_live_order :
    reserve 6 (some [0, 0, 0, 0, 0, 0]) initial = .ok ⟨[7, 9, 0, 0, 0, 0], 2, true⟩ := by decide

theorem failed_spill_is_not_inequality : reserve 6 none initial = .error initial := by decide

end Controls
end Mettapedia.Machines.LocalWorklistStorage
