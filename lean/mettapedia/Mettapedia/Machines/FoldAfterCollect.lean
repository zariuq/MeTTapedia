import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Folding after collecting

SWI's foldall/4 runs its generator and folds each answer into a state as the
answer comes: a step without an answer keeps the state.  The generator may
change the world as it runs.  When the step is pure, a function of the answer
and the state alone, the generator's run cannot see the state, so collecting
every answer first and folding them afterwards gives the same state, and
leaves the world as the generator alone leaves it (`interleaved_eq_collect`).

A step that also changes the world the generator reads has no such law
(`Controls.world_step_breaks_collecting`).

Summing one integer over the answers needs only their number: `n` answers,
each `c`, folded by addition from `i`, give `i + n * c`
(`foldAnswers_sum_replicate`), so a sum of a constant over a match's answers
is the constant times the count of rows the match finds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FoldAfterCollect

variable {W A S : Type*}

/-- The answers of a generator, run for at most `fuel` answers from a world,
and the world it leaves. -/
def collect (next : W → Option (A × W)) : ℕ → W → List A × W
  | 0, w => ([], w)
  | fuel + 1, w =>
      match next w with
      | none => ([], w)
      | some (a, w') => ((a :: (collect next fuel w').1), (collect next fuel w').2)

/-- The answers folded in order: a step without an answer keeps the state. -/
def foldAnswers (step : A → S → Option S) (answers : List A) (s : S) : S :=
  answers.foldl (fun state a => (step a state).getD state) s

/-- The generator run with each answer folded as it comes. -/
def interleaved (next : W → Option (A × W)) (step : A → S → Option S) :
    ℕ → W → S → S × W
  | 0, w, s => (s, w)
  | fuel + 1, w, s =>
      match next w with
      | none => (s, w)
      | some (a, w') => interleaved next step fuel w' ((step a s).getD s)

/-- Folding as the answers come is folding after collecting them. -/
theorem interleaved_eq_collect (next : W → Option (A × W)) (step : A → S → Option S) :
    ∀ (fuel : ℕ) (w : W) (s : S),
      interleaved next step fuel w s =
        (foldAnswers step (collect next fuel w).1 s, (collect next fuel w).2)
  | 0, w, s => rfl
  | fuel + 1, w, s => by
      cases h : next w with
      | none => simp [interleaved, collect, foldAnswers, h]
      | some p =>
          obtain ⟨a, w'⟩ := p
          simp only [interleaved, collect, h]
          rw [interleaved_eq_collect next step fuel w' ((step a s).getD s)]
          rfl

/-- Summing one integer over `n` answers from `i` gives `i + n * c`. -/
theorem foldAnswers_sum_replicate (n : ℕ) (c i : ℤ) :
    foldAnswers (fun a s => some (a + s)) (List.replicate n c) i = i + n * c := by
  induction n generalizing i with
  | zero => simp [foldAnswers]
  | succ n ih =>
      have step := ih (c + i)
      simp only [foldAnswers] at step ⊢
      rw [List.replicate_succ, List.foldl_cons, Option.getD_some, step]
      push_cast
      ring

namespace Controls

/-- A generator that answers the flag it reads, twice, and a step that also
sets the flag: folded as the answers come, the second answer sees the step's
change; collected first, it does not. -/
def next : Bool × ℕ → Option (Bool × (Bool × ℕ))
  | (_, 0) => none
  | (flag, n + 1) => some (flag, (flag, n))

/-- The world-changing step, folded as the answers come: it counts the answers
that were `true` and turns the flag on. -/
def interleavedWorld : ℕ → Bool × ℕ → ℕ → ℕ × (Bool × ℕ)
  | 0, w, s => (s, w)
  | fuel + 1, w, s =>
      match next w with
      | none => (s, w)
      | some (a, (_, n)) => interleavedWorld fuel (true, n) (if a then s + 1 else s)

theorem world_step_breaks_collecting :
    (interleavedWorld 2 (false, 2) 0).1 ≠
      foldAnswers (fun a s => some (if a then s + 1 else s))
        (collect next 2 (false, 2)).1 0 := by
  decide

end Controls

end Mettapedia.Machines.FoldAfterCollect
