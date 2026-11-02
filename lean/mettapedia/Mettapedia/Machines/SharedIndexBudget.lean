import Mathlib.Tactic

/-!
# A shared retained-storage budget for optional indexes

The cache is in retirement order, oldest first. Trimming discards whole
indexes until their retained byte weights fit the available allowance.
Every retained entry still comes from the original cache. A sound index
offers candidates with the same completed answers as the authoritative
source; a miss uses that source. Retirement therefore changes neither the
answers nor their multiplicity.

The allowance concerns retained cache storage. Native allocation peaks,
candidate-array ownership, scope validation and the producer's index-soundness
law remain separate obligations. Native bookkeeping must keep its running
byte ledger equal to these weights for each constant-time budget check.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedIndexBudget

structure Entry (K C : Type) where
  offer : K → Option (List C)
  bytes : ℕ

variable {K C A : Type}

def retained : List (Entry K C) → ℕ
  | [] => 0
  | entry :: rest => entry.bytes + retained rest

def trim (allowance : ℕ) : List (Entry K C) → List (Entry K C)
  | [] => []
  | entry :: rest =>
      if retained (entry :: rest) ≤ allowance then entry :: rest
      else trim allowance rest

theorem trim_bound (allowance : ℕ) (cache : List (Entry K C)) :
    retained (trim allowance cache) ≤ allowance := by
  induction cache with
  | nil => simp [trim, retained]
  | cons entry rest ih =>
    simp only [trim]
    split_ifs with fits
    · exact fits
    · exact ih

theorem trim_sublist (allowance : ℕ) (cache : List (Entry K C)) :
    List.Sublist (trim allowance cache) cache := by
  induction cache with
  | nil => exact List.Sublist.refl _
  | cons entry rest ih =>
    simp only [trim]
    split_ifs
    · exact List.Sublist.refl _
    · exact ih.cons entry

theorem fixed_and_retained_bound (fixed allowance : ℕ) (cache : List (Entry K C))
    (fixed_fits : fixed ≤ allowance) :
    fixed + retained (trim (allowance - fixed) cache) ≤ allowance := by
  have bound := trim_bound (allowance - fixed) cache
  omega

def read (unify : C → Option A) (source : K → List C) :
    List (Entry K C) → K → List A
  | [], key => (source key).filterMap unify
  | entry :: rest, key => match entry.offer key with
      | none => read unify source rest key
      | some rows => rows.filterMap unify

def Sound (unify : C → Option A) (source : K → List C)
    (cache : List (Entry K C)) : Prop :=
  ∀ entry ∈ cache, ∀ key rows, entry.offer key = some rows →
    rows.filterMap unify = (source key).filterMap unify

theorem read_source (unify : C → Option A) (source : K → List C)
    (cache : List (Entry K C)) (sound : Sound unify source cache) (key : K) :
    read unify source cache key = (source key).filterMap unify := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
    have tail : Sound unify source rest := by
      intro e present
      exact sound e (List.mem_cons_of_mem _ present)
    cases found : entry.offer key with
    | none => simpa [read, found] using ih tail
    | some rows =>
      simpa [read, found] using sound entry (List.mem_cons_self ..) key rows found

theorem trim_sound (unify : C → Option A) (source : K → List C)
    (cache : List (Entry K C)) (sound : Sound unify source cache) (allowance : ℕ) :
    Sound unify source (trim allowance cache) := by
  intro entry present
  exact sound entry ((trim_sublist allowance cache).subset present)

theorem retirement_preserves_answers (unify : C → Option A) (source : K → List C)
    (cache : List (Entry K C)) (sound : Sound unify source cache)
    (allowance : ℕ) (key : K) :
    read unify source (trim allowance cache) key = read unify source cache key := by
  rw [read_source unify source _ (trim_sound unify source cache sound allowance),
      read_source unify source cache sound]

example : retained (trim 5 [Entry.mk (fun _ : ℕ => some [1]) 4,
                            Entry.mk (fun _ : ℕ => some [1]) 4]) = 4 := by decide

/-- An incorrect hit is not repaired by falling back only on misses. -/
example : read (fun n : ℕ => some n) (fun _ : ℕ => [1])
    [Entry.mk (fun _ => some [2]) 4] 0 ≠ [1] := by decide

/-- Forgetting that incorrect entry recovers the authoritative answer. -/
example : read (fun n : ℕ => some n) (fun _ : ℕ => [1])
    (trim 0 [Entry.mk (fun _ => some [2]) 4]) 0 = [1] := by decide

end Mettapedia.Machines.SharedIndexBudget
