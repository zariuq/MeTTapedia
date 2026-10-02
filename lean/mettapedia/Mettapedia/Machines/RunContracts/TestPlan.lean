import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-!
# Test plans checked by occurrence identity

The specification is a bag equation: the resolved test identities are exactly
the declared identities, each once, and every resolved verdict passes. The
implementation consumes a finite set of outstanding identities incrementally.
Its correspondence is proved for every residual set, not just successful runs.

Only *resolved* test scopes enter this protocol. A caught or expected exception
is resolved by that scope before publication. Ordinary language answers and
the spelling of their payloads do not enter this checker. Test discovery is
explicit; an empty plan requires explicit permission. A missing terminal run
record and execution/output failures are handled by the enclosing runner.
Raw declaration lists pass through `fromList`, which rejects repeated identities
before set conversion. Discovery completeness, runtime identity assignment and
verdict authenticity remain external obligations; a set alone cannot check them.

Finite sets here specify identity lookup, not a native data structure or cost
claim. The module does not assert that arbitrary effectful tests commute, only
that checking already resolved verdicts is independent of arrival order.
-/

namespace Mettapedia.Machines.RunContracts.TestPlan

structure Result (Id : Type*) where
  id : Id
  passed : Bool
  deriving DecidableEq, Repr

structure Plan (Id : Type*) where
  expected : Finset Id
  allowEmpty : Bool := false

variable {Id : Type*}

/-- Validate the raw declaration occurrences before forming the lookup set.
An empty declaration list is structurally admissible; `allowEmpty` separately
controls whether a resulting empty test run can be accepted. -/
def fromList [DecidableEq Id] (ids : List Id) (allowEmpty : Bool := false) :
    Option (Plan Id) :=
  if ids.Nodup then some ⟨ids.toFinset, allowEmpty⟩ else none

/-- Admission requires distinct declared identities; set conversion cannot
silently turn duplicate declarations into a valid plan. -/
theorem fromList_isSome_iff [DecidableEq Id] (ids : List Id) (allowEmpty : Bool) :
    (fromList ids allowEmpty).isSome = true ↔ ids.Nodup := by
  simp [fromList]

theorem fromList_none_iff [DecidableEq Id] (ids : List Id) (allowEmpty : Bool) :
    fromList ids allowEmpty = none ↔ ¬ids.Nodup := by
  simp [fromList]

/-- Every admitted declaration occurrence survives exactly once, as a bag. -/
theorem fromList_exact_bag [DecidableEq Id] (ids : List Id) (allowEmpty : Bool)
    (plan : Plan Id) (admitted : fromList ids allowEmpty = some plan) :
    plan.expected.val = (ids : Multiset Id) := by
  unfold fromList at admitted
  split at admitted
  next distinct =>
    cases admitted
    simp [List.toFinset_val, List.dedup_eq_self.mpr distinct]
  next => cases admitted

theorem fromList_preserves_empty_policy [DecidableEq Id] (ids : List Id)
    (allowEmpty : Bool) (plan : Plan Id) (admitted : fromList ids allowEmpty = some plan) :
    plan.allowEmpty = allowEmpty := by
  unfold fromList at admitted
  split at admitted <;> cases admitted
  rfl

def identities (results : List (Result Id)) : Multiset Id :=
  results.map Result.id

def AllPassed (results : List (Result Id)) : Prop :=
  ∀ r ∈ results, r.passed = true

/-- Global, order-free specification. The bag equation rejects missing,
duplicate, and undeclared identities, even when the total count is right. -/
def Satisfied (plan : Plan Id) (results : List (Result Id)) : Prop :=
  (plan.allowEmpty = true ∨ plan.expected.Nonempty) ∧
  plan.expected.val = identities results ∧ AllPassed results

/-- The incremental checker retains only identities not yet accounted for.
A failed verdict or a duplicate/undeclared identity rejects the ledger. -/
def consume [DecidableEq Id] (pending : Finset Id) : List (Result Id) → Option (Finset Id)
  | [] => some pending
  | r :: rest =>
      if r.id ∈ pending ∧ r.passed = true then
        consume (pending.erase r.id) rest
      else none

def accepts [DecidableEq Id] (plan : Plan Id) (results : List (Result Id)) : Bool :=
  (plan.allowEmpty || decide plan.expected.Nonempty) &&
    decide (consume plan.expected results = some ∅)

@[simp] theorem identities_nil : identities ([] : List (Result Id)) = 0 := rfl

@[simp] theorem identities_cons (r : Result Id) (rs : List (Result Id)) :
    identities (r :: rs) = r.id ::ₘ identities rs := rfl

@[simp] theorem allPassed_nil : AllPassed ([] : List (Result Id)) := by
  simp [AllPassed]

@[simp] theorem allPassed_cons (r : Result Id) (rs : List (Result Id)) :
    AllPassed (r :: rs) ↔ r.passed = true ∧ AllPassed rs := by
  simp [AllPassed]

variable [DecidableEq Id]

/-- Each checked prefix accounts for precisely its occurrences; no identity
can be consumed twice. This is the implementation/specification invariant. -/
theorem consume_eq_some_iff (pending remaining : Finset Id)
    (results : List (Result Id)) :
    consume pending results = some remaining ↔
      pending.val = identities results + remaining.val ∧ AllPassed results := by
  induction results generalizing pending with
  | nil => simp [consume, Finset.val_inj]
  | cons r rest ih =>
      constructor
      · intro h
        simp only [consume] at h
        split at h
        next guard =>
          obtain ⟨hid, hpass⟩ := guard
          obtain ⟨heq, hrest⟩ := (ih _).mp h
          refine ⟨?_, (allPassed_cons r rest).mpr ⟨hpass, hrest⟩⟩
          calc
            pending.val = r.id ::ₘ (pending.erase r.id).val := by
              simpa only [Finset.erase_val] using
                (Multiset.cons_erase (show r.id ∈ pending.val from hid)).symm
            _ = r.id ::ₘ (identities rest + remaining.val) := by rw [heq]
            _ = identities (r :: rest) + remaining.val := by simp
        next => simp at h
      · rintro ⟨heq, hpass⟩
        have hid : r.id ∈ pending := by
          change r.id ∈ pending.val
          rw [heq]
          simp
        have htail : (pending.erase r.id).val = identities rest + remaining.val := by
          rw [Finset.erase_val, heq]
          simp
        rw [consume, if_pos ⟨hid, ((allPassed_cons r rest).mp hpass).1⟩]
        exact (ih _).mpr ⟨htail, ((allPassed_cons r rest).mp hpass).2⟩

theorem accepts_iff (plan : Plan Id) (results : List (Result Id)) :
    accepts plan results = true ↔ Satisfied plan results := by
  simp [accepts, consume_eq_some_iff, Satisfied, Finset.nonempty_iff_ne_empty]

/-- Prefix delivery, suspension between batches, and concatenated delivery
use the same residual ledger. Rejected prefixes remain rejected. -/
theorem consume_append (pending : Finset Id)
    (first second : List (Result Id)) :
    consume pending (first ++ second) =
      (consume pending first).bind (fun rest => consume rest second) := by
  induction first generalizing pending with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.cons_append, consume]
      split <;> simp_all

omit [DecidableEq Id] in
theorem identities_perm {xs ys : List (Result Id)} (h : xs.Perm ys) :
    identities xs = identities ys := by
  exact Multiset.coe_eq_coe.mpr (h.map Result.id)

omit [DecidableEq Id] in
theorem allPassed_perm {xs ys : List (Result Id)} (h : xs.Perm ys) :
    AllPassed xs ↔ AllPassed ys := by
  constructor <;> intro hp r hr
  · exact hp r (h.mem_iff.mpr hr)
  · exact hp r (h.mem_iff.mp hr)

/-- Arrival order is not part of the contract for independent resolved tests. -/
theorem accepts_perm (plan : Plan Id) {xs ys : List (Result Id)}
    (h : xs.Perm ys) : accepts plan xs = accepts plan ys := by
  apply Bool.eq_iff_iff.mpr
  rw [accepts_iff, accepts_iff]
  simp only [Satisfied, identities_perm h, allPassed_perm h]

theorem accepted_identities_nodup (plan : Plan Id) (rs : List (Result Id))
    (h : accepts plan rs = true) : (rs.map Result.id).Nodup := by
  have heq := ((accepts_iff plan rs).mp h).2.1
  apply Multiset.coe_nodup.mp
  change (identities rs).Nodup
  rw [← heq]
  exact plan.expected.nodup

theorem failed_result_rejects (plan : Plan Id) (rs : List (Result Id))
    (r : Result Id) (hr : r ∈ rs) (hfail : r.passed = false) :
    accepts plan rs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hp := ((accepts_iff plan rs).mp h).2.2 r hr
  simp [hfail] at hp

theorem duplicate_identity_rejects (plan : Plan Id) (rs : List (Result Id))
    (hdup : ¬(rs.map Result.id).Nodup) : accepts plan rs = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h => hdup (accepted_identities_nodup plan rs h)

theorem missing_identity_rejects (plan : Plan Id) (rs : List (Result Id))
    (id : Id) (required : id ∈ plan.expected)
    (missing : id ∉ identities rs) : accepts plan rs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq := ((accepts_iff plan rs).mp h).2.1
  exact missing (heq ▸ (show id ∈ plan.expected.val from required))

theorem unknown_identity_rejects (plan : Plan Id) (rs : List (Result Id))
    (id : Id) (unlisted : id ∉ plan.expected)
    (reported : id ∈ identities rs) : accepts plan rs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq := ((accepts_iff plan rs).mp h).2.1
  apply unlisted
  change id ∈ plan.expected.val
  rw [heq]
  exact reported

/-- A later passing test cannot overwrite a previously resolved failure. -/
theorem failed_prefix_stays_failed (plan : Plan Id)
    (first second : List (Result Id)) (r : Result Id)
    (hr : r ∈ first) (hfail : r.passed = false) :
    accepts plan (first ++ second) = false :=
  failed_result_rejects plan _ r (List.mem_append_left _ hr) hfail

namespace Controls

def two : Plan Nat := ⟨{1, 2}, false⟩

theorem distinct_declarations_admitted :
    (fromList [1, 2] false).isSome = true := by decide

theorem duplicate_declarations_rejected :
    fromList [1, 1] false = none := by simp [fromList]

theorem empty_permission_does_not_allow_duplicates :
    fromList [1, 1] true = none := by simp [fromList]

/-- Validation preserves the raw count instead of accepting the deduplicated set. -/
theorem admitted_declaration_bag :
    (fromList [2, 1] false).map (fun p => p.expected.val) = some (↑[2, 1] : Multiset Nat) := by
  decide

example : accepts two [⟨2, true⟩, ⟨1, true⟩] = true := by decide

/-- Two successes are not enough: one identity was duplicated, another lost. -/
example : accepts two [⟨1, true⟩, ⟨1, true⟩] = false := by decide

example : accepts two [⟨1, false⟩, ⟨2, true⟩] = false := by decide

example : accepts two [⟨1, true⟩] = false := by decide

example : accepts two [⟨1, true⟩, ⟨3, true⟩] = false := by decide

example : accepts (⟨∅, false⟩ : Plan Nat) [] = false := by decide

/-- An explicitly authorized empty/skip plan is distinguishable from a
mistaken empty discovery. -/
example : accepts (⟨∅, true⟩ : Plan Nat) [] = true := by decide

end Controls

end Mettapedia.Machines.RunContracts.TestPlan
