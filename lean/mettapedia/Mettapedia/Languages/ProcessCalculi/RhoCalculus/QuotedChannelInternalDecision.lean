import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelBubbles
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# A non-reflective bubble decides its own equality internally

Control for the reflective diagonal.  The quoted-channel calculus compares
processes as channels but never runs a received process: it has no drop.

* **Internal total decision.**  The open bubble's equality is syntactic
  identity, and the calculus decides it by its own interaction: an output on
  one process beside an input on another can communicate exactly when the two
  are identical (`equalityTest_steps_iff`, `openBubble_equality_iff_test`).
* **No Lawvere fixed point.**  Every step shrinks the size of a process
  (`step_processSize_lt`), so there is no infinite run (`no_infinite_run`) and no
  process reduces to itself in parallel with anything
  (`no_parallel_fixedPoint`): the map `X ↦ X ∣ P` has no fixed point up to
  reduction.  By the contrapositive of the diagonal step, for any way of
  running processes on processes, no process represents the diagonal composite
  of that map up to reduction (`not_representable_parallel`).

The reflective λ-bubble is the opposite case: its codes run, its equality has
no internal decider (`Mettapedia.GSLT.GraphTheory.ReflectiveBeta`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel

open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.AuthorityTheory

/-- The internal equality test: send on the first process, receive on the
second. -/
def equalityTest (first second : Proc) : Proc :=
  .par (.out first .nil) (.inp second .nil)

/-- **The test communicates exactly on identical processes.** -/
theorem equalityTest_steps_iff (first second : Proc) :
    (∃ target, Step (equalityTest first second) target) ↔ first = second := by
  constructor
  · rintro ⟨_, step⟩
    exact channel_eq_of_step_out_inp step
  · rintro rfl
    exact ⟨.nil, .receive first .nil .nil⟩

/-- **The open bubble's equality is decided by the calculus itself.** -/
theorem openBubble_equality_iff_test (first second : Proc) :
    openBubble.authority.Holds (openBubble.equality first second) ↔
      ∃ target, Step (equalityTest first second) target :=
  (relEquiv_quoteFree_iff_eq first second).trans (equalityTest_steps_iff first second).symm

/-- The size of a process. -/
def processSize : Proc → ℕ
  | .nil => 1
  | .par left right => processSize left + processSize right + 1
  | .out channel payload => processSize channel + processSize payload + 1
  | .inp channel body => processSize channel + processSize body + 1
  | .echo channel => processSize channel + 1

theorem processSize_pos (term : Proc) : 0 < processSize term := by
  cases term <;> exact Nat.succ_pos _

/-- **Every step shrinks the size.** -/
theorem step_processSize_lt {source target : Proc} (step : Step source target) :
    processSize target < processSize source := by
  induction step with
  | receive channel payload body => simp only [processSize]; omega
  | echo channel payload =>
      have := processSize_pos channel
      simp only [processSize]
      omega
  | parL right _ ih => simp only [processSize]; omega
  | parR left _ ih => simp only [processSize]; omega

theorem transGen_processSize_lt {source target : Proc}
    (steps : Relation.TransGen Step source target) :
    processSize target < processSize source := by
  induction steps with
  | single step => exact step_processSize_lt step
  | tail _ step ih => exact (step_processSize_lt step).trans ih

/-- **No infinite run.** -/
theorem no_infinite_run : ¬ ∃ run : ℕ → Proc, ∀ index, Step (run index) (run (index + 1)) := by
  rintro ⟨run, steps⟩
  have bound : ∀ index, processSize (run index) + index ≤ processSize (run 0) := by
    intro index
    induction index with
    | zero => simp
    | succ index ih =>
        have := step_processSize_lt (steps index)
        omega
  have := bound (processSize (run 0))
  have := processSize_pos (run (processSize (run 0)))
  omega

/-- **No process reduces to itself in parallel with another**: the map
`X ↦ X ∣ P` has no fixed point up to reduction. -/
theorem no_parallel_fixedPoint (fixed other : Proc) :
    ¬ Relation.TransGen Step fixed (.par fixed other) := by
  intro steps
  have := transGen_processSize_lt steps
  simp only [processSize] at this
  omega

/-- **The Lawvere obstruction in the quoted-channel calculus**: whatever map
runs processes on processes, no process represents the diagonal composite of
`X ↦ X ∣ P` up to reduction. -/
theorem not_representable_parallel (run : Proc → Proc → Proc) (other : Proc) :
    ¬ Mettapedia.Logic.Diagonal.Representable run (Relation.TransGen Step)
      (Mettapedia.Logic.Diagonal.diagonalComposite run fun fixed => .par fixed other) :=
  Mettapedia.Logic.Diagonal.not_representable_of_fixedPointFree run _
    fun fixed => no_parallel_fixedPoint fixed other

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel
