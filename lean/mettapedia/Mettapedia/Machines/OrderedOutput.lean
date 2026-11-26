import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Lean.Elab.Tactic.Omega

/-!
# Ordered publication from a retained result list

The drain's local equations specify the machine's next action for an empty
list and for a physical head occurrence. The completion law appends every
occurrence to the reached history and accounts for the terminal step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine

variable {State Event Verdict Request : Type}
variable {machine : Machine State Event Verdict Request}

structure OrderedOutput (machine : Machine State Event Verdict Request) where
  returning : List Event → List Event → State
  verdict : List Event → Verdict
  finish (emitted : List Event) :
    machine.step (returning [] emitted) = some (.finish (verdict emitted))
  publish (row : Event) (rest emitted : List Event) :
    machine.step (returning (row :: rest) emitted) =
      some (.publish [row] (returning rest (emitted ++ [row])))

theorem OrderedOutput.drain (output : OrderedOutput machine)
    (results emitted : List Event) (later : Nat) :
    machine.run (results.length + 1 + later) (output.returning results emitted) =
      (results, .finished (output.verdict (emitted ++ results))) := by
  induction results generalizing emitted with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Nat.one_add, List.append_nil] using
        machine.run_succ_finish (fuel := later) (output.finish emitted)
  | cons row rest ih =>
      rw [show (row :: rest).length + 1 + later = (rest.length + 1 + later) + 1 by
        simp only [List.length_cons]; omega,
        machine.run_succ_publish (output.publish row rest emitted), ih]
      simp only [List.singleton_append, List.append_assoc]

theorem OrderedOutput.complete (output : OrderedOutput machine)
    {initial : State} {results emitted : List Event}
    (path : Relation.ReflTransGen machine.reading.silent initial (output.returning results emitted)) :
    ∃ budget, ∀ later, machine.run (budget + later) initial =
      (results, .finished (output.verdict (emitted ++ results))) := by
  obtain ⟨silentSteps, arrive⟩ := machine.silent_run path
  refine ⟨silentSteps + results.length + 1, fun later => ?_⟩
  rw [show silentSteps + results.length + 1 + later =
    silentSteps + (results.length + 1 + later) by omega, arrive]
  exact output.drain results emitted later

theorem finished_run_eq
    {initial : State} {actual expected : List Event} {seen wanted : Verdict}
    {first bound : Nat}
    (ran : machine.run first initial = (actual, .finished seen))
    (complete : ∀ later, machine.run (bound + later) initial = (expected, .finished wanted)) :
    actual = expected ∧ seen = wanted := by
  have stable := machine.run_stable first bound initial (by
    intro residual impossible
    rw [ran] at impossible
    cases impossible)
  have same := complete first
  rw [Nat.add_comm bound first, stable, ran] at same
  exact ⟨(Prod.mk.inj same).1, Outcome.finished.inj (Prod.mk.inj same).2⟩

theorem finished_suffix
    {initial saved : State} {first bound : Nat} {before expected : List Event} {finished : Verdict}
    (paused : machine.run first initial = (before, .exhausted saved))
    (complete : ∀ later, machine.run (bound + later) initial = (expected, .finished finished)) :
    ∃ after, machine.run bound saved = (after, .finished finished) ∧ before ++ after = expected := by
  have whole := complete first
  rw [Nat.add_comm bound first, machine.established_and_pending first bound initial saved before paused]
    at whole
  exact ⟨(machine.run bound saved).1, Prod.ext rfl (Prod.mk.inj whole).2, (Prod.mk.inj whole).1⟩

end Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine
