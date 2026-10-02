import Mettapedia.Algorithms.CertifiedFiniteChoice

/-!
# Checked resumable finite interval comparisons

A receipt contains an ordinary checked prefix and pending competitors. Resuming
validates that it covers the original candidates in order, and rechecks the
prefix against the current interval data. Budget exhaustion retains pending
work. Establishment requires an empty remainder and enclosing real scores.
-/

namespace Mettapedia.Algorithms.ResumableComparison

variable {C : Type*} [DecidableEq C]

structure Receipt (C : Type*) where
  checked : List C
  pending : List C
  deriving DecidableEq

def passes (lower upper : C → ℚ) (selected candidate : C) : Prop :=
  candidate = selected ∨ upper candidate ≤ lower selected

instance (lower upper : C → ℚ) (selected candidate : C) :
    Decidable (passes lower upper selected candidate) := by
  unfold passes
  infer_instance

def Valid (all : List C) (lower upper : C → ℚ) (selected : C) (receipt : Receipt C) : Prop :=
  selected ∈ all ∧ receipt.checked ++ receipt.pending = all ∧
    ∀ c ∈ receipt.checked, passes lower upper selected c

instance (all : List C) (lower upper : C → ℚ) (selected : C) (receipt : Receipt C) :
    Decidable (Valid all lower upper selected receipt) := by
  unfold Valid
  infer_instance

def advance (lower upper : C → ℚ) (selected : C) : ℕ → Receipt C → Receipt C
  | 0, receipt => receipt
  | n + 1, receipt => match receipt.pending with
    | [] => receipt
    | c :: cs => if passes lower upper selected c then
        advance lower upper selected n ⟨receipt.checked ++ [c], cs⟩
      else receipt

theorem advance_valid (all : List C) (lower upper : C → ℚ) (selected : C)
    (budget : ℕ) (receipt : Receipt C)
    (valid : Valid all lower upper selected receipt) :
    Valid all lower upper selected (advance lower upper selected budget receipt) := by
  induction budget generalizing receipt with
  | zero => exact valid
  | succ n ih =>
      unfold advance
      cases pending : receipt.pending with
      | nil => exact valid
      | cons c cs =>
          dsimp only
          split_ifs with good
          · apply ih
            refine ⟨valid.1, ?_, ?_⟩
            · simpa [List.append_assoc, pending] using valid.2.1
            · intro other member
              rcases List.mem_append.mp member with old | added
              · exact valid.2.2 other old
              · have same := List.mem_singleton.mp added
                subst other
                exact good
          · exact valid

/-- Resume ordinary receipt data only after validating coverage and every prior comparison. -/
def resume (all : List C) (lower upper : C → ℚ) (selected : C)
    (budget : ℕ) (receipt : Receipt C) : Option (Receipt C) :=
  if Valid all lower upper selected receipt then
    some (advance lower upper selected budget receipt)
  else none

theorem resume_valid (all : List C) (lower upper : C → ℚ) (selected : C)
    (budget : ℕ) (receipt output : Receipt C)
    (accepted : resume all lower upper selected budget receipt = some output) :
    Valid all lower upper selected output := by
  unfold resume at accepted
  split_ifs at accepted with valid
  · cases Option.some.inj accepted
    exact advance_valid all lower upper selected budget receipt valid

/-- Completed comparisons certify optimality for independently supplied enclosing scores. -/
theorem completed_sound (all : List C) (lower upper : C → ℚ) (selected : C)
    (budget : ℕ) (receipt output : Receipt C) (actual : C → ℝ)
    (encloses : ∀ c ∈ all, (lower c : ℝ) ≤ actual c ∧ actual c ≤ (upper c : ℝ))
    (accepted : resume all lower upper selected budget receipt = some output)
    (complete : output.pending = []) :
    selected ∈ all ∧ ∀ c ∈ all, actual c ≤ actual selected := by
  obtain ⟨member, covers, checkedValid⟩ := resume_valid all lower upper selected budget receipt output accepted
  have entire : output.checked = all := by simpa [complete] using covers
  refine ⟨member, ?_⟩
  intro c hc
  have good := checkedValid c (entire.symm ▸ hc)
  rcases good with rfl | ordered
  · exact le_rfl
  · have orderedR : (upper c : ℝ) ≤ (lower selected : ℝ) := by exact_mod_cast ordered
    exact (encloses c hc).2.trans (orderedR.trans (encloses selected member).1)

theorem zero_budget_preserves (lower upper : C → ℚ) (selected : C) (receipt : Receipt C) :
    advance lower upper selected 0 receipt = receipt := rfl

/-- Enough comparison steps consume a suffix whose comparisons all pass. -/
theorem advance_complete (lower upper : C → ℚ) (selected : C)
    (checked pending : List C)
    (good : ∀ c ∈ pending, passes lower upper selected c) :
    (advance lower upper selected pending.length ⟨checked, pending⟩).pending = [] := by
  induction pending generalizing checked with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.length_cons, advance]
      rw [if_pos (good c List.mem_cons_self)]
      exact ih (checked ++ [c]) (fun other member => good other (List.mem_cons_of_mem _ member))

/-- Incorrect prior comparisons are refused, including a forged empty remainder. -/
theorem invalid_refused (all : List C) (lower upper : C → ℚ) (selected : C)
    (budget : ℕ) (receipt : Receipt C) (invalid : ¬ Valid all lower upper selected receipt) :
    resume all lower upper selected budget receipt = none := by
  simp [resume, invalid]

end Mettapedia.Algorithms.ResumableComparison
