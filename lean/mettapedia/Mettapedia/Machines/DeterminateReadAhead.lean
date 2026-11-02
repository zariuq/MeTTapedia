import Mathlib.Tactic

/-!
# A lazy match's read-ahead passes over candidates that cannot unify

A lazy match reads its next candidate ahead, and its frame goes before the
last candidate runs: the candidate's body then runs without the frame, its
cursor or what the cursor holds.  The candidates offered are an index's
selection, read by its first bound column, so a match whose candidate was
not the last of its column's candidates kept its frame open while its body
ran.  Under a recursion in the body, that is a frame per level: the history
counter kept a frame, a cursor and a relation snapshot per level, about
1.4 per level once its state head had taken its relation.

The read-ahead now passes over a candidate that a conservative check shows
cannot unify with the pattern.  The check is sound: it rejects only
candidates whose unification fails.

The model: candidates, a unification that answers or fails, and the
read-ahead keeping candidates by a test (every candidate before, those that
may unify now).  This file proves:
* `answers_filter`: passing over the candidates a sound check rejects
  leaves the answers, in order, as they were;
* `held_filter_le`: a frame is held during a body no more often than
  before;
* `last_released`: during the body of the last candidate that may unify,
  no frame is held.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeterminateReadAhead

variable {κ β : Type}

/-- The answers of a match: each candidate whose unification answers. -/
def answers (unify : κ → Option β) (cands : List κ) : List β :=
  cands.filterMap unify

/-- Passing over candidates whose unification fails leaves the answers as
they were. -/
theorem answers_filter (unify : κ → Option β) (may : κ → Bool)
    (sound : ∀ c, may c = false → unify c = none) (cands : List κ) :
    answers unify (cands.filter may) = answers unify cands := by
  induction cands with
  | nil => rfl
  | cons c cs ih =>
    unfold answers at ih ⊢
    by_cases h : may c = true
    · simp [h, List.filterMap_cons, ih]
    · have hnone : unify c = none := sound c (by simpa using h)
      simp [h, hnone, ih]

/-- Whether the frame is still held while the body of the candidate at the
head of a match's remaining candidates runs: some later candidate the
read-ahead keeps. -/
def held (keep : κ → Bool) (later : List κ) : Bool := later.any keep

/-- The read-ahead that keeps every candidate holds the frame whenever a
later candidate remains; the one that keeps those that may unify, only when
one of them remains, so never more often. -/
theorem held_filter_le (may : κ → Bool) (later : List κ) :
    held may later = true → held (fun _ => true) later = true := by
  intro h
  simp only [held, List.any_eq_true] at h ⊢
  obtain ⟨x, hx, _⟩ := h
  exact ⟨x, hx, trivial⟩

/-- During the body of the last candidate that may unify, the read-ahead
that passes over the others holds no frame. -/
theorem last_released (may : κ → Bool) (later : List κ)
    (none_later : ∀ x ∈ later, may x = false) :
    held may later = false := by
  simp only [held, List.any_eq_false]
  intro x hx
  simp [none_later x hx]

/-- Inspect only a bounded prefix. The uninspected suffix remains eligible,
so exhausting the physical allowance cannot discard a possible answer. -/
def boundedCandidates (allowance : ℕ) (may : κ → Bool) (cands : List κ) : List κ :=
  (cands.take allowance).filter may ++ cands.drop allowance

theorem answers_bounded (unify : κ → Option β) (may : κ → Bool)
    (sound : ∀ c, may c = false → unify c = none) (allowance : ℕ)
    (cands : List κ) :
    answers unify (boundedCandidates allowance may cands) = answers unify cands := by
  unfold boundedCandidates
  simp only [answers, List.filterMap_append]
  have h := answers_filter unify may sound (cands.take allowance)
  unfold answers at h
  rw [h, ← List.filterMap_append, List.take_append_drop]

/-- Candidate inspections are bounded independently of the number rejected. -/
theorem inspected_le (allowance : ℕ) (cands : List κ) :
    (cands.take allowance).length ≤ allowance := by
  simp only [List.length_take]
  exact Nat.min_le_left _ _

example : boundedCandidates 2 (fun r : ℕ => r == 4) [0, 1, 2, 3, 4] = [2, 3, 4] := by
  decide

/-- Exhausting the allowance leaves a later successful candidate available. -/
example : answers (fun r : ℕ => if r = 4 then some r else none)
    (boundedCandidates 2 (fun r => r == 4) [0, 1, 2, 3, 4]) = [4] := by
  decide

/-! ## Examples -/

/-- A counter's state: registers 0 to 4 at one step.  The match for
register 2 reads them by their step; before, its frame was held while the
body of register 2's fact ran, with registers 3 and 4 still to read. -/
example : held (fun _ => true) [3, 4] = true := by decide

/-- With the check, registers 3 and 4 cannot unify with register 2's
pattern, so the frame goes before the body runs. -/
example : held (fun r : ℕ => r == 2) [3, 4] = false := by decide

/-- The answers stay: register 2's fact answers either way. -/
example :
    answers (fun r : ℕ => if r = 2 then some r else none) ([0, 1, 2, 3, 4].filter (· == 2)) =
      answers (fun r : ℕ => if r = 2 then some r else none) [0, 1, 2, 3, 4] := by decide

end Mettapedia.Machines.DeterminateReadAhead
