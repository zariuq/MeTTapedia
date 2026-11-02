import Mettapedia.Machines.ResumableSearchRunner

/-! A runner may commit the first published receipt without spending the rest
of its quantum. Prefix growth keeps that receipt first. A tick which publishes
nothing still retains exactly the ordinary resumed search. -/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumableSearchRunner

variable {σ Run Receipt : Type} (S : Search σ Run Receipt)

def resumeUntilPublication : Nat → Run → Run
  | 0, run => run
  | work + 1, run =>
      if (S.publication run).isEmpty then
        resumeUntilPublication work (S.resume run 1)
      else run

theorem resumeUntilPublication_spec (lawful : S.Lawful) (source : σ) (offset work : Nat) :
    resumeUntilPublication S work (S.run source offset) = S.resume (S.run source offset) work ∨
    ∃ receipt early late,
      S.publication (resumeUntilPublication S work (S.run source offset)) = receipt :: early ∧
      S.publication (S.resume (S.run source offset) work) = receipt :: late := by
  induction work generalizing offset with
  | zero =>
      left
      simp [resumeUntilPublication, lawful.resume_run]
  | succ work ih =>
      cases published : S.publication (S.run source offset) with
      | nil =>
          simpa only [resumeUntilPublication, published, List.isEmpty_nil, if_true,
            lawful.resume_run, Nat.add_assoc, Nat.add_comm 1 work] using ih (offset + 1)
      | cons receipt rest =>
          right
          have grown := lawful.publication_prefix source offset (work + 1)
          rw [published] at grown
          obtain ⟨tail, same⟩ := grown
          refine ⟨receipt, rest, rest ++ tail, ?_, ?_⟩
          · simp [resumeUntilPublication, published]
          · rw [lawful.resume_run, ← same]
            rfl

namespace Machine

def tickUntilPublication (machine : Machine σ Run Receipt) (quantum : Nat) : Machine σ Run Receipt :=
  match machine.phase with
  | .running =>
      let resumed := resumeUntilPublication S quantum machine.program
      match S.publication resumed with
      | receipt :: _ =>
          ⟨.running, S.target receipt, S.run (S.target receipt) 0,
            S.target receipt :: machine.states, receipt :: machine.receipts⟩
      | [] => { machine with phase := phaseOf (S.status resumed), program := resumed }
  | .done => machine
  | .blocked => machine

theorem tickUntilPublication_eq_tick (lawful : S.Lawful) (machine : Machine σ Run Receipt)
    (budget : ∃ work, machine.program = S.run machine.state work) (quantum : Nat) :
    tickUntilPublication S machine quantum = tick S machine quantum := by
  obtain ⟨phase, state, program, states, receipts⟩ := machine
  cases phase with
  | done => rfl
  | blocked => rfl
  | running =>
      obtain ⟨offset, exact⟩ := budget
      dsimp only at exact
      subst program
      rcases resumeUntilPublication_spec S lawful state offset quantum with same | published
      · simp only [tickUntilPublication, tick, same]
        rfl
      · obtain ⟨receipt, early, late, first, second⟩ := published
        simp only [tickUntilPublication, tick, first, second]

def advanceUntilPublication : Nat → Nat → Machine σ Run Receipt → Machine σ Run Receipt
  | 0, _, machine => machine
  | ticks + 1, quantum, machine =>
      advanceUntilPublication ticks quantum (tickUntilPublication S machine quantum)

theorem advanceUntilPublication_eq_advance (lawful : S.Lawful) (ticks quantum : Nat)
    (machine : Machine σ Run Receipt) (reached : Reached S machine) :
    advanceUntilPublication S ticks quantum machine = advance S ticks quantum machine := by
  induction ticks generalizing machine with
  | zero => rfl
  | succ ticks ih =>
      simp only [advanceUntilPublication, advance,
        tickUntilPublication_eq_tick S lawful machine reached.budget]
      exact ih _ (tick_reached lawful reached quantum)

end Machine

#print axioms resumeUntilPublication_spec
#print axioms Machine.tickUntilPublication_eq_tick
#print axioms Machine.advanceUntilPublication_eq_advance

end Mettapedia.Machines.ResumableSearchRunner
