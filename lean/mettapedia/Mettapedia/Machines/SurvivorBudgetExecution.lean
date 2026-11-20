import Mettapedia.Machines.SurvivorBudget
import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.CollectorEvacuation

/-!
# Nursery scheduling and the existing register machine

A threshold chooses when to clear dead registers, not what the code means.
The actual register-code liveness pass supplies the retained slots. The graph
evacuator separately preserves ordered roots, children and alias partitions.
No C root scanner, allocation-failure policy or word representation is proved
by this scheduling bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SurvivorBudgetExecution

open RegisterCode

variable {V L O P H : Type}

def trim (live : Finset Nat) (registers : Regs V) : Regs V :=
  fun index => if index ∈ live then registers index else none

theorem trim_keeps_live (live : Finset Nat) (registers : Regs V)
    (index : Nat) (kept : index ∈ live) :
    trim live registers index = registers index := by simp [trim, kept]

theorem trim_clears_dead (live : Finset Nat) (registers : Regs V)
    (index : Nat) (dead : index ∉ live) :
    trim live registers index = none := by simp [trim, dead]

def scheduledRegisters (configured seed retained pressure allocated : Nat)
    (live : Finset Nat) (registers : Regs V) : Regs V :=
  if SurvivorBudget.threshold configured seed retained pressure ≤ allocated
  then trim live registers else registers

theorem scheduled_keeps_live (configured seed retained pressure allocated : Nat)
    (live : Finset Nat) (registers : Regs V) (index : Nat) (kept : index ∈ live) :
    scheduledRegisters configured seed retained pressure allocated live registers index =
      registers index := by
  unfold scheduledRegisters
  split
  · exact trim_keeps_live live registers index kept
  · rfl

/-- Every admitted schedule preserves the existing interpreter's complete
disposition: decline, returned value, or fallthrough on the requested slots. -/
theorem scheduled_execution_agrees (semantics : Sem V L O P H)
    (answer : H → List V → Option V) (code : List (Instr L O P H))
    (out : Finset Nat) (registers : Regs V)
    (configured seed retained pressure allocated : Nat) :
    Option.Rel (Outcome.Agree out)
      (exec semantics answer code
        (scheduledRegisters configured seed retained pressure allocated
          (liveIn semantics.toPatterns code out) registers))
      (exec semantics answer code registers) := by
  apply exec_live
  intro index kept
  exact scheduled_keeps_live _ _ _ _ _ _ _ index kept

theorem answer_eq_of_agree (out : Finset Nat)
    {left right : Option (Outcome V)} (agree : Option.Rel (Outcome.Agree out) left right) :
    RegisterCode.answer left = RegisterCode.answer right := by
  cases agree with
  | none => rfl
  | @some left right same =>
      cases left <;> cases right <;> simp_all [Outcome.Agree, RegisterCode.answer]

theorem scheduled_answer_exact (semantics : Sem V L O P H)
    (answer : H → List V → Option V) (code : List (Instr L O P H))
    (out : Finset Nat) (registers : Regs V)
    (configured seed retained pressure allocated : Nat) :
    RegisterCode.answer (exec semantics answer code
      (scheduledRegisters configured seed retained pressure allocated
        (liveIn semantics.toPatterns code out) registers)) =
      RegisterCode.answer (exec semantics answer code registers) :=
  answer_eq_of_agree out (scheduled_execution_agrees semantics answer code out registers
    configured seed retained pressure allocated)

theorem two_schedules_agree (semantics : Sem V L O P H)
    (answer : H → List V → Option V) (code : List (Instr L O P H))
    (out : Finset Nat) (registers : Regs V)
    (configured₁ seed₁ retained₁ pressure₁ allocated₁
      configured₂ seed₂ retained₂ pressure₂ allocated₂ : Nat) :
    RegisterCode.answer (exec semantics answer code
      (scheduledRegisters configured₁ seed₁ retained₁ pressure₁ allocated₁
        (liveIn semantics.toPatterns code out) registers)) =
      RegisterCode.answer (exec semantics answer code
        (scheduledRegisters configured₂ seed₂ retained₂ pressure₂ allocated₂
          (liveIn semantics.toPatterns code out) registers)) := by
  rw [scheduled_answer_exact, scheduled_answer_exact]

namespace Controls

def held : Regs Int := fun index => if index = 0 then some 7 else some 99

theorem an_unread_temporary_is_really_removed :
    trim {0} held 1 = none ∧ held 1 = some 99 := by decide

theorem two_registers_may_retain_the_same_value :
    let aliases : Regs Int := fun _ => some 7
    trim {0, 1} aliases 0 = trim {0, 1} aliases 1 ∧
      trim {0, 1} aliases 0 = some 7 := by decide

theorem omitting_a_live_slot_changes_its_observation :
    trim ∅ held 0 ≠ held 0 := by decide

end Controls
end Mettapedia.Machines.SurvivorBudgetExecution
