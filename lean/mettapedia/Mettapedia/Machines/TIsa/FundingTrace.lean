import Mettapedia.Machines.TIsa.Funding

/-!
# Prefix observations of source-grade payments

This is a proof view over `Funding.charge`. A stopped payment trace retains
the receipt and the number of payments completed before exhaustion. The
`complete` observation records that every listed payment succeeded. Program
outcomes, native instruction counts and effects between payment points have
their own contracts.

The trace view follows cost-label preservation in CerCo and the credit/receipt
distinction of Mevel, Jourdan and Pottier. It adds no runtime representation.
The cutpoint laws describe finite stopped prefixes, following the partial
big-step and big-stop approach of Hoffmann/Hofmann and Kahn/Hoffmann/Li.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.FundingTrace

open Funding

def cost : List Grade → Nat
  | [] => 0
  | grade :: rest => grade.units.toNat + cost rest

theorem cost_replicate (grade : Grade) (count : Nat) :
    cost (List.replicate count grade) = count * grade.units.toNat := by
  induction count with
  | zero => simp [cost]
  | succ count induction =>
    simp [List.replicate_succ, cost, induction, Nat.add_mul, Nat.add_comm]

inductive Observation where
  | complete (receipt : Word)
  | exhausted (paid : Nat) (receipt : Word)
  | invalidReceipt (receipt : Word)
  deriving DecidableEq, Repr

def Observation.afterPayment : Observation → Observation
  | .exhausted paid receipt => .exhausted (paid + 1) receipt
  | other => other

@[simp] theorem Observation.afterPayment_complete_iff (observed : Observation) (receipt : Word) :
    observed.afterPayment = .complete receipt ↔ observed = .complete receipt := by
  cases observed <;> simp [afterPayment]

def run (allowance receipt : Word) : List Grade → Observation
  | [] => if allowance.toNat < receipt.toNat then .invalidReceipt receipt else .complete receipt
  | grade :: rest => match charge allowance receipt grade with
    | .invalidReceipt => .invalidReceipt receipt
    | .exhausted => .exhausted 0 receipt
    | .paid next => (run allowance next rest).afterPayment

def Observation.prepend (count : Nat) : Observation → Observation
  | .exhausted paid receipt => .exhausted (count + paid) receipt
  | other => other

@[simp] theorem Observation.prepend_zero (observed : Observation) : observed.prepend 0 = observed := by
  cases observed <;> simp [prepend]

theorem Observation.prepend_succ (count : Nat) (observed : Observation) :
    observed.prepend (count + 1) = (observed.prepend count).afterPayment := by
  cases observed <;> simp [prepend, afterPayment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def Observation.follow (prefixLength : Nat) (next : Word → Observation) : Observation → Observation
  | .complete receipt => (next receipt).prepend prefixLength
  | other => other

theorem Observation.follow_afterPayment (count : Nat) (next : Word → Observation)
    (observed : Observation) :
    observed.afterPayment.follow (count + 1) next =
      (observed.follow count next).afterPayment := by
  cases observed <;> simp [Observation.follow, afterPayment, prepend_succ]

theorem run_invalid (allowance receipt : Word) (grades : List Grade)
    (invalid : allowance.toNat < receipt.toNat) :
    run allowance receipt grades = .invalidReceipt receipt := by
  cases grades with
  | nil => simp [run, invalid]
  | cons grade rest =>
    have payment := (Funding.invalid_iff allowance receipt grade).mpr invalid
    simp [run, payment]

/-- A cutpoint summary composes without replaying its completed prefix. -/
theorem run_append (allowance receipt : Word) (before after : List Grade) :
    run allowance receipt (before ++ after) =
      (run allowance receipt before).follow before.length (fun next => run allowance next after) := by
  induction before generalizing receipt with
  | nil =>
    by_cases invalid : allowance.toNat < receipt.toNat
    · rw [List.nil_append, run_invalid allowance receipt after invalid]
      simp [run, invalid, Observation.follow]
    · simp [run, invalid, Observation.follow]
  | cons grade before induction =>
    cases payment : charge allowance receipt grade with
    | invalidReceipt => simp [run, payment, Observation.follow]
    | exhausted => simp [run, payment, Observation.follow]
    | paid next =>
      simp only [List.cons_append, run, payment, List.length_cons, induction,
        Observation.follow_afterPayment]

theorem complete_iff (allowance receipt final : Word) (grades : List Grade) :
    run allowance receipt grades = .complete final ↔
      receipt.toNat + cost grades ≤ allowance.toNat ∧
      final.toNat = receipt.toNat + cost grades := by
  induction grades generalizing receipt with
  | nil =>
    by_cases invalid : allowance.toNat < receipt.toNat
    · have impossible : ¬ receipt.toNat ≤ allowance.toNat := by omega
      simp [run, cost, invalid, impossible]
    · simp only [run, invalid, if_false, Observation.complete.injEq, cost, Nat.add_zero]
      constructor
      · intro same
        subst final
        exact ⟨by omega, rfl⟩
      · rintro ⟨_, same⟩
        exact (BitVec.eq_of_toNat_eq same).symm
  | cons grade rest induction =>
    cases payment : charge allowance receipt grade with
    | invalidReceipt =>
      have invalid := (invalid_iff allowance receipt grade).mp payment
      have impossible : ¬ receipt.toNat + (grade.units.toNat + cost rest) ≤ allowance.toNat := by omega
      simp [run, payment, cost, impossible]
    | exhausted =>
      have exhausted := (exhausted_iff allowance receipt grade).mp payment
      have impossible : ¬ receipt.toNat + (grade.units.toNat + cost rest) ≤ allowance.toNat := by omega
      simp [run, payment, cost, impossible]
    | paid next =>
      have nextNat := (paid_no_wrap allowance receipt next grade payment).1
      simp only [run, payment, Observation.afterPayment_complete_iff, induction, cost]
      simp only [nextNat, Nat.add_assoc]

theorem complete_same_cost (allowance receipt final : Word) (left right : List Grade)
    (same : cost left = cost right) :
    run allowance receipt left = .complete final ↔ run allowance receipt right = .complete final := by
  rw [complete_iff, complete_iff, same]

/-- A clipped machine-word bound cannot certify payment of an oversized trace. -/
theorem no_complete_of_cost_overflow (allowance receipt final : Word) (grades : List Grade)
    (overflow : 2 ^ 64 ≤ receipt.toNat + cost grades) :
    run allowance receipt grades ≠ .complete final := by
  intro complete
  have fits := ((complete_iff allowance receipt final grades).mp complete).1
  have bounded := allowance.isLt
  omega

/-- Two payment points have three exact budget regions, including stopped receipts. -/
theorem two_frontiers (allowance receipt : Word) (first second : Grade)
    (valid : receipt.toNat ≤ allowance.toNat) :
    run allowance receipt [first, second] =
      if allowance.toNat < receipt.toNat + first.units.toNat then .exhausted 0 receipt
      else if allowance.toNat < receipt.toNat + first.units.toNat + second.units.toNat then
        .exhausted 1 (receipt + first.word)
      else .complete (receipt + first.word + second.word) := by
  by_cases firstShort : allowance.toNat < receipt.toNat + first.units.toNat
  · have firstFails : charge allowance receipt first = .exhausted :=
      (exhausted_iff _ _ _).mpr ⟨valid, firstShort⟩
    simp [run, firstFails, firstShort]
  · have firstPaid : charge allowance receipt first = .paid (receipt + first.word) :=
      (paid_iff _ _ _ _).mpr ⟨by omega, rfl⟩
    obtain ⟨nextNat, nextValid⟩ := paid_no_wrap _ _ _ _ firstPaid
    by_cases secondShort : allowance.toNat < receipt.toNat + first.units.toNat + second.units.toNat
    · have secondFails : charge allowance (receipt + first.word) second = .exhausted :=
        (exhausted_iff _ _ _).mpr ⟨nextValid, by omega⟩
      simp [run, firstPaid, secondFails, firstShort, secondShort, Observation.afterPayment]
    · have secondPaid : charge allowance (receipt + first.word) second =
          .paid (receipt + first.word + second.word) :=
        (paid_iff _ _ _ _).mpr ⟨by omega, rfl⟩
      have finalValid := (paid_no_wrap _ _ _ _ secondPaid).2
      have notInvalid : ¬ allowance.toNat < (receipt + first.word + second.word).toNat := by omega
      simp only [run, firstPaid, secondPaid, firstShort, secondShort, notInvalid, if_false,
        Observation.afterPayment]

open Funding

theorem cost_append (left right : List Grade) : cost (left ++ right) = cost left + cost right := by
  induction left with
  | nil => simp [cost]
  | cons grade rest induction => simp [cost, induction, Nat.add_assoc]

/-- A remaining-cost certificate removes a check without moving its payment. -/
theorem charge_of_remaining_bound (allowance entry current : Word) (grade : Grade)
    (bound spent : Nat)
    (valid : entry.toNat ≤ allowance.toNat)
    (covered : bound ≤ (allowance - entry).toNat)
    (receipt : current.toNat = entry.toNat + spent)
    (within : spent + grade.units.toNat ≤ bound) :
    charge allowance current grade = .paid (current + grade.word) := by
  have difference : (allowance - entry).toNat = allowance.toNat - entry.toNat :=
    BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using valid)
  apply (paid_iff _ _ _ _).mpr
  exact ⟨by rw [receipt]; rw [difference] at covered; omega, rfl⟩

/-- Sufficient allowance makes every retained payment point affordable. -/
theorem paid_at_prefix (allowance entry : Word) (before after : List Grade) (grade : Grade)
    (covered : entry.toNat + cost (before ++ grade :: after) ≤ allowance.toNat) :
    ∃ current,
      run allowance entry before = .complete current ∧
      charge allowance current grade = .paid (current + grade.word) := by
  have costs : cost (before ++ grade :: after) = cost before + (grade.units.toNat + cost after) := by
    rw [cost_append, cost]
  have fits : entry.toNat + cost before < 2 ^ 64 := by
    have := allowance.isLt
    rw [costs] at covered
    omega
  let current : Word := BitVec.ofNat 64 (entry.toNat + cost before)
  have receipt : current.toNat = entry.toNat + cost before := by
    exact Nat.mod_eq_of_lt fits
  refine ⟨current, (complete_iff _ _ _ _).mpr ⟨?_, receipt⟩, ?_⟩
  · rw [costs] at covered
    omega
  · apply (paid_iff _ _ _ _).mpr
    rw [receipt]
    exact ⟨by rw [costs] at covered; omega, rfl⟩

/-- Exhaustion is witnessed by a completed prefix and its first unpaid point. -/
theorem exhausted_iff_cutpoint (allowance entry final : Word) (grades : List Grade)
    (paid : Nat) :
    run allowance entry grades = .exhausted paid final ↔
      ∃ before grade after,
        grades = before ++ grade :: after ∧ before.length = paid ∧
        run allowance entry before = .complete final ∧
        charge allowance final grade = .exhausted := by
  constructor
  · intro observed
    induction grades generalizing entry paid final with
    | nil =>
        by_cases invalid : allowance.toNat < entry.toNat
        · simp [run, invalid] at observed
        · simp [run, invalid] at observed
    | cons first rest induction =>
        cases payment : charge allowance entry first with
        | invalidReceipt => simp [run, payment] at observed
        | exhausted =>
            simp only [run, payment] at observed
            cases observed
            have valid := (Funding.exhausted_iff allowance entry first).mp payment
            exact ⟨[], first, rest, rfl, rfl,
              by simp [run, Nat.not_lt.mpr valid.1], payment⟩
        | paid next =>
            cases tail : run allowance next rest with
            | complete value => simp [run, payment, tail, Observation.afterPayment] at observed
            | invalidReceipt value => simp [run, payment, tail, Observation.afterPayment] at observed
            | exhausted count value =>
                simp only [run, payment, tail, Observation.afterPayment] at observed
                cases observed
                obtain ⟨before, grade, after, split, length, complete, failed⟩ :=
                  induction next final count tail
                refine ⟨first :: before, grade, after, ?_, ?_, ?_, failed⟩
                · simp [split]
                · simp [length]
                · simp [run, payment, complete, Observation.afterPayment]
  · rintro ⟨before, grade, after, rfl, length, complete, failed⟩
    rw [run_append, complete]
    simp [Observation.follow, run, failed, Observation.prepend, length]

/-- Natural prefix sums give the exact allowance interval for a stopped receipt. -/
theorem exhausted_iff_frontier (allowance entry final : Word) (grades : List Grade)
    (paid : Nat) :
    run allowance entry grades = .exhausted paid final ↔
      ∃ before grade after,
        grades = before ++ grade :: after ∧ before.length = paid ∧
        entry.toNat + cost before ≤ allowance.toNat ∧
        allowance.toNat < entry.toNat + cost before + grade.units.toNat ∧
        final.toNat = entry.toNat + cost before := by
  rw [exhausted_iff_cutpoint]
  constructor
  · rintro ⟨before, grade, after, split, length, complete, failed⟩
    obtain ⟨fits, receipt⟩ := (complete_iff allowance entry final before).mp complete
    have short := ((Funding.exhausted_iff allowance final grade).mp failed).2
    exact ⟨before, grade, after, split, length, fits, by omega, receipt⟩
  · rintro ⟨before, grade, after, split, length, fits, short, receipt⟩
    exact ⟨before, grade, after, split, length,
      (complete_iff allowance entry final before).mpr ⟨fits, receipt⟩,
      (Funding.exhausted_iff allowance final grade).mpr ⟨by omega, by omega⟩⟩

/-- Payment observations do not inspect the suffix after the first unpaid point. -/
theorem exhausted_suffix_irrelevant (allowance entry final : Word)
    (before after replacement : List Grade) (grade : Grade)
    (complete : run allowance entry before = .complete final)
    (failed : charge allowance final grade = .exhausted) :
    run allowance entry (before ++ grade :: after) =
      run allowance entry (before ++ grade :: replacement) := by
  have left := (exhausted_iff_cutpoint allowance entry final
    (before ++ grade :: after) before.length).mpr ⟨before, grade, after, rfl, rfl, complete, failed⟩
  have right := (exhausted_iff_cutpoint allowance entry final
    (before ++ grade :: replacement) before.length).mpr
      ⟨before, grade, replacement, rfl, rfl, complete, failed⟩
  exact left.trans right.symm

namespace CutpointControls

private def two : Grade := ⟨2, by decide⟩
private def three : Grade := ⟨3, by decide⟩
private def four : Grade := ⟨4, by decide⟩

theorem stop_after_two : run 5 0 [two, three, four] = .exhausted 2 5 := by decide
theorem entry_receipt_retained : run 12 7 [two, three, four] = .exhausted 2 12 := by decide
theorem larger_budget_finishes : run 9 0 [two, three, four] = .complete 9 := by decide
theorem cannot_move_stop_to_entry : run 5 0 [two, three, four] ≠ .exhausted 0 0 := by decide
theorem invalid_is_not_exhausted : run 5 6 [two, three, four] ≠ .exhausted 0 6 := by decide

end CutpointControls

namespace BoundControls

private def three : Grade := ⟨3, by decide⟩

theorem all_checks_covered :
    charge (6#64) (3#64) three = .paid (6#64) := by
  exact charge_of_remaining_bound 6 0 3 three 6 3 (by decide) (by decide) rfl (by decide)

theorem underfunded_test_requires_fallback :
    ¬ (6 : Nat) ≤ ((3#64) - (0#64)).toNat ∧
      run 3 0 [three, three] = .exhausted 1 3 := by decide

theorem moving_payments_changes_receipt :
    run 3 0 [three, three] ≠ run 3 0 [⟨6, by decide⟩] := by decide

end BoundControls

namespace Controls

private def two : Grade := ⟨2, by decide⟩
private def three : Grade := ⟨3, by decide⟩
private def six : Grade := ⟨6, by decide⟩

theorem sufficient_allowance : run 6 0 [three, three] = .complete 6 := by decide
theorem zero_allowance : run 0 0 [three, three] = .exhausted 0 0 := by decide
theorem initial_invalid_receipt : run 3 4 [] = .invalidReceipt 4 := by decide
theorem same_total : cost [three, three] = cost [six] := by decide
theorem merging_changes_exhaustion : run 3 0 [three, three] ≠ run 3 0 [six] := by decide
theorem reordering_changes_exhaustion : run 3 0 [three, two] ≠ run 3 0 [two, three] := by decide
theorem nested_loop_cost_overflows : 2 ^ 64 ≤ 2 * (4294967295 : Nat) ^ 2 := by decide
theorem nested_payment_trace_cannot_complete (allowance final : Word) :
    run allowance 0 (List.replicate ((4294967295 : Nat) ^ 2) two) ≠ .complete final := by
  apply no_complete_of_cost_overflow
  rw [cost_replicate]
  change 2 ^ 64 ≤ 0 + (4294967295 : Nat) ^ 2 * 2
  decide

end Controls
end Mettapedia.Machines.TIsa.FundingTrace

#print axioms Mettapedia.Machines.TIsa.FundingTrace.complete_iff
#print axioms Mettapedia.Machines.TIsa.FundingTrace.run_append
#print axioms Mettapedia.Machines.TIsa.FundingTrace.no_complete_of_cost_overflow
#print axioms Mettapedia.Machines.TIsa.FundingTrace.two_frontiers
#print axioms Mettapedia.Machines.TIsa.FundingTrace.Controls.merging_changes_exhaustion
#print axioms Mettapedia.Machines.TIsa.FundingTrace.Controls.nested_payment_trace_cannot_complete
