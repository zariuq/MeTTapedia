import Mettapedia.Logic.HMLInstructionJudgments
import Mettapedia.Logic.HMLStackComparison

/-!
# Prepaid programs from independently generated instruction judgments

Each instruction rule removes one unit cell from the available purse before
admitting the remaining program. Finish retains every unused cell. The
derivation records the actual complete intermediate stacks, including gather
prefixes. Its soundness and reconstruction earn the exact acceptance boundary.

Composition combines separately supplied budgets and matches complete stack
interfaces. These judgments concern the declared instruction machine; signing
keys, located authority, compilation work and physical time remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection

open Inspection

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

inductive PrepaidProgram (environment : BooleanEnv State n) :
    List (Instruction State n) → List Bool → List Bool → Nat → Type u where
  | finish (stack : List Bool) (remaining : Nat) : PrepaidProgram environment [] stack stack remaining
  | instruction {opcode : Instruction State n} {rest : List (Instruction State n)}
      {stack middle output : List Bool} {remaining : Nat}
      (judgment : InstructionJudgment environment opcode stack middle)
      (after : PrepaidProgram environment rest middle output remaining) :
      PrepaidProgram environment (opcode :: rest) stack output (remaining + 1)

namespace PrepaidProgram

theorem computed (environment : BooleanEnv State n)
    {program : List (Instruction State n)} {stack output : List Bool} {budget : Nat}
    (accepted : PrepaidProgram environment program stack output budget) :
    execute environment program stack = some output := by
  induction accepted with
  | finish => rfl
  | instruction judgment after inductionHypothesis =>
      rw [execute, judgment.sound environment, Option.bind_some]
      exact inductionHypothesis

theorem funding (environment : BooleanEnv State n)
    {program : List (Instruction State n)} {stack output : List Bool} {budget : Nat}
    (accepted : PrepaidProgram environment program stack output budget) : program.length ≤ budget := by
  induction accepted with
  | finish => exact Nat.zero_le _
  | instruction judgment after inductionHypothesis =>
      simp only [List.length_cons]
      omega

def reconstruct (environment : BooleanEnv State n) (program : List (Instruction State n))
    (stack output : List Bool) (budget : Nat)
    (successful : execute environment program stack = some output)
    (funded : program.length ≤ budget) : PrepaidProgram environment program stack output budget := by
  induction program generalizing stack budget with
  | nil =>
      have same := Option.some.inj successful
      cases same
      exact .finish output budget
  | cons opcode rest inductionHypothesis =>
      cases budget with
      | zero => simp only [List.length_cons] at funded; omega
      | succ budget =>
          cases checked : opcode.execute environment stack with
          | none =>
              simp only [execute, checked, Option.bind_none] at successful
              cases successful
          | some middle =>
              have suffix : execute environment rest middle = some output := by
                simpa only [execute, checked, Option.bind_some] using successful
              have available : rest.length ≤ budget := by
                simp only [List.length_cons] at funded
                omega
              exact .instruction (InstructionJudgment.reconstruct environment opcode stack middle checked)
                (inductionHypothesis middle budget suffix available)

theorem exists_iff (environment : BooleanEnv State n) (program : List (Instruction State n))
    (stack output : List Bool) (budget : Nat) :
    Nonempty (PrepaidProgram environment program stack output budget) ↔
      execute environment program stack = some output ∧ program.length ≤ budget :=
  ⟨fun ⟨accepted⟩ => ⟨accepted.computed environment, accepted.funding environment⟩,
    fun ⟨successful, funded⟩ => ⟨reconstruct environment program stack output budget successful funded⟩⟩

/-- Extra cells remain available without changing any instruction judgment
or complete intermediate stack in the supplied derivation. -/
def grantExtra (environment : BooleanEnv State n) (extra : Nat)
    {program : List (Instruction State n)} {stack output : List Bool} {budget : Nat}
    (accepted : PrepaidProgram environment program stack output budget) :
    PrepaidProgram environment program stack output (budget + extra) :=
  match accepted with
  | .finish stack remaining => .finish stack (remaining + extra)
  | .instruction judgment after => by
      simpa only [Nat.add_right_comm] using
        PrepaidProgram.instruction judgment (grantExtra environment extra after)
termination_by structural accepted

/-- Sequential composition matches the whole supplied stack, and explicitly
combines the two independently supplied resources. -/
def append (environment : BooleanEnv State n)
    {before after : List (Instruction State n)} {stack middle output : List Bool}
    {firstBudget secondBudget : Nat}
    (first : PrepaidProgram environment before stack middle firstBudget)
    (second : PrepaidProgram environment after middle output secondBudget) :
    PrepaidProgram environment (before ++ after) stack output (firstBudget + secondBudget) :=
  match first with
  | .finish _ remaining => by
      simpa only [List.nil_append, Nat.add_comm secondBudget remaining] using
        second.grantExtra environment remaining
  | .instruction judgment rest => by
      simpa only [List.cons_append, Nat.add_right_comm] using
        PrepaidProgram.instruction judgment (append environment rest second)
termination_by structural first

end PrepaidProgram

def compiledPrepayment (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)
    (affordable : (inspect presentation formula admitted environment state).2 ≤ budget) :
    PrepaidProgram environment (compile presentation formula admitted state) stack
      ((inspect presentation formula admitted environment state).1 :: stack) budget :=
  PrepaidProgram.reconstruct environment _ stack _ budget
    (execute_compiled presentation formula admitted environment state stack)
    (by rwa [compiled_length presentation formula admitted environment state])

theorem compiled_prepayment_iff (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat) :
    Nonempty (PrepaidProgram environment (compile presentation formula admitted state) stack
      ((inspect presentation formula admitted environment state).1 :: stack) budget) ↔
      (inspect presentation formula admitted environment state).2 ≤ budget := by
  rw [PrepaidProgram.exists_iff, compiled_length presentation formula admitted environment state]
  simp only [execute_compiled presentation formula admitted environment state stack, true_and]

end Mettapedia.Logic.ModalMuCalculus.StackInspection
