import Mettapedia.Logic.BDD.StateTransducer
import Mettapedia.Algebra.Order.FixedPointIteration

/-!
# Resumable symbolic fixed points

A symbolic operator is connected locally to an independent monotone set
operator. The driver tests semantic equality through the checked BDD test.
Every page retains its diagram and counted operator applications; exhaustion
is `paused`, never a negative logical answer. Completion proves a fixed point.
Bottom/top invariants identify it as the least/greatest fixed point, and finite
state spaces guarantee eventual completion when more fuel is supplied.

The operator and its domain remain fixed across a resume. No theorem here
identifies these pass counts with a MeTTa evaluator's source instruction count.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.FixedPointSolver

open StatePredicates
open Mettapedia.Algebra.Order.FixedPointIteration

structure Operator (n : Nat) where
  step : Diagram n → Diagram n
  meaning : Set (State n) →o Set (State n)
  refines : ∀ current, denote (step current) = meaning (denote current)

structure Frame (n : Nat) where
  current : Diagram n
  passes : Nat

inductive Result (n : Nat)
  | paused (frame : Frame n)
  | done (frame : Frame n)

def Result.frame {n : Nat} : Result n → Frame n
  | .paused frame | .done frame => frame

def Result.finished {n : Nat} : Result n → Bool
  | .paused _ => false
  | .done _ => true

def advance {n : Nat} (operator : Operator n) : Nat → Frame n → Result n
  | 0, frame => .paused frame
  | fuel + 1, frame =>
      let next := operator.step frame.current
      if equivalent frame.current next then .done ⟨frame.current, frame.passes + 1⟩
      else advance operator fuel ⟨next, frame.passes + 1⟩

def resume {n : Nat} (operator : Operator n) (fuel : Nat) : Result n → Result n
  | .paused frame => advance operator fuel frame
  | .done frame => .done frame

theorem resume_split {n : Nat} (operator : Operator n) (first later : Nat) (frame : Frame n) :
    resume operator later (advance operator first frame) = advance operator (first + later) frame := by
  induction first generalizing frame with
  | zero => simp [advance, resume]
  | succ first ih =>
    simp only [advance, Nat.succ_add]
    split
    · rfl
    · exact ih _

theorem done_fixed {n : Nat} (operator : Operator n) (fuel : Nat) (initial final : Frame n)
    (finished : advance operator fuel initial = .done final) :
    operator.meaning (denote final.current) = denote final.current := by
  induction fuel generalizing initial with
  | zero => cases finished
  | succ fuel ih =>
    simp only [advance] at finished
    split at finished
    next equal =>
      cases finished
      exact (operator.refines initial.current).symm.trans
        ((equivalent_denote _ _).mp equal).symm
    next => exact ih _ finished

theorem invariant {n : Nat} (operator : Operator n) (property : Set (State n) → Prop)
    (preserved : ∀ set, property set → property (operator.meaning set))
    (fuel : Nat) (initial : Frame n) (valid : property (denote initial.current)) :
    property (denote (advance operator fuel initial).frame.current) := by
  induction fuel generalizing initial with
  | zero => exact valid
  | succ fuel ih =>
    simp only [advance]
    split
    · exact valid
    · apply ih
      rw [operator.refines]
      exact preserved _ valid

theorem bottom_result_below {n : Nat} (operator : Operator n) (fuel : Nat) :
    denote (advance operator fuel ⟨falsity n, 0⟩).frame.current ⊆ operator.meaning.lfp := by
  apply invariant operator (fun set => set ⊆ operator.meaning.lfp)
  · intro set included
    rw [← operator.meaning.map_lfp]
    exact operator.meaning.monotone included
  · simp [denote, falsity, BDD.satSet]

theorem top_result_above {n : Nat} (operator : Operator n) (fuel : Nat) :
    operator.meaning.gfp ⊆ denote (advance operator fuel ⟨truth n, 0⟩).frame.current := by
  apply invariant operator (fun set => operator.meaning.gfp ⊆ set)
  · intro set included
    rw [← operator.meaning.map_gfp]
    exact operator.meaning.monotone included
  · simp [denote, truth, BDD.satSet]

theorem completed_least {n : Nat} (operator : Operator n) (fuel : Nat) (final : Frame n)
    (finished : advance operator fuel ⟨falsity n, 0⟩ = .done final) :
    denote final.current = operator.meaning.lfp := by
  apply le_antisymm
  · simpa only [finished, Result.frame] using bottom_result_below operator fuel
  · exact operator.meaning.lfp_le_fixed (done_fixed operator fuel _ final finished)

theorem completed_greatest {n : Nat} (operator : Operator n) (fuel : Nat) (final : Frame n)
    (finished : advance operator fuel ⟨truth n, 0⟩ = .done final) :
    denote final.current = operator.meaning.gfp := by
  apply le_antisymm
  · exact operator.meaning.le_gfp (done_fixed operator fuel _ final finished).ge
  · simpa only [finished, Result.frame] using top_result_above operator fuel

def walk {n : Nat} (operator : Operator n) (initial : Diagram n) : Nat → Diagram n
  | 0 => initial
  | step + 1 => operator.step (walk operator initial step)

theorem walk_denote {n : Nat} (operator : Operator n) (initial : Diagram n) (steps : Nat) :
    denote (walk operator initial steps) = iterateFrom operator.meaning (denote initial) steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [walk, operator.refines, ih, iterateFrom]

theorem walk_shift {n : Nat} (operator : Operator n) (initial : Diagram n) (steps : Nat) :
    walk operator (operator.step initial) steps = walk operator initial (steps + 1) := by
  induction steps with
  | zero => rfl
  | succ steps ih => exact congrArg operator.step ih

theorem finishes_at_stable_walk {n : Nat} (operator : Operator n) (steps : Nat) (initial : Frame n)
    (stable : equivalent (walk operator initial.current steps)
      (operator.step (walk operator initial.current steps)) = true) :
    (advance operator (steps + 1) initial).finished = true := by
  induction steps generalizing initial with
  | zero =>
    change equivalent initial.current (operator.step initial.current) = true at stable
    simp [advance, stable, Result.finished]
  | succ steps ih =>
    rw [advance]
    split
    · rfl
    · apply ih
      simpa only [walk_shift] using stable

theorem least_eventually_finishes {n : Nat} (operator : Operator n) :
    ∃ fuel, (advance operator fuel ⟨falsity n, 0⟩).finished = true := by
  classical
  obtain ⟨steps, reached⟩ := bottom_eventually_lfp operator.meaning
  refine ⟨steps + 1, finishes_at_stable_walk operator steps _ ?_⟩
  apply (equivalent_denote _ _).mpr
  rw [operator.refines, walk_denote]
  have seed : denote (falsity n) = (⊥ : Set (State n)) := by ext state; simp [denote, falsity, BDD.satSet]
  rw [seed, reached steps le_rfl, operator.meaning.map_lfp]

theorem greatest_eventually_finishes {n : Nat} (operator : Operator n) :
    ∃ fuel, (advance operator fuel ⟨truth n, 0⟩).finished = true := by
  classical
  obtain ⟨steps, reached⟩ := top_eventually_gfp operator.meaning
  refine ⟨steps + 1, finishes_at_stable_walk operator steps _ ?_⟩
  apply (equivalent_denote _ _).mpr
  rw [operator.refines, walk_denote]
  have seed : denote (truth n) = (⊤ : Set (State n)) := by ext state; simp [denote, truth, BDD.satSet]
  rw [seed, reached steps le_rfl, operator.meaning.map_gfp]

end Mettapedia.Logic.BDDCore.FixedPointSolver
