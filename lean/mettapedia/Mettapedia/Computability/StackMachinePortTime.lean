import Mettapedia.Computability.StackMachineSpaceGrowth
import Mettapedia.Computability.StackMachineComposition

/-!
# Physical input and output lengths in original stack-machine time

A finite command can perform several pushes or pops in one TM2 transition.
Their syntactic maxima, chosen before the input, supply the constants. If
input and output are different stacks, a clean completed run has consumed
every input cell and generated every output cell. The corresponding word
lengths are bounded by the actual number of successful transitions.

An in-place identity machine is a counterexample without the distinct-port
condition. These bounds count alphabet cells, not native allocator bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StackMachinePortTime

open Turing StateTransition
open StackMachineSpaceGrowth

universe u v w x

variable {Key : Type u} {Alphabet : Key → Type v} {Label : Type w} {Registers : Type x}

def popCount : TM2.Stmt Alphabet Label Registers → Nat
  | .pop _ _ rest => popCount rest + 1
  | .push _ _ rest | .peek _ _ rest | .load _ rest => popCount rest
  | .branch _ yes no => max (popCount yes) (popCount no)
  | .goto _ | .halt => 0

section Statement

variable [DecidableEq Key]

theorem push_port_bounds (contents : ∀ key, List (Alphabet key))
    (key target : Key) (value : Alphabet key) :
    (contents target).length ≤ (Function.update contents key (value :: contents key) target).length ∧
      (Function.update contents key (value :: contents key) target).length ≤ (contents target).length + 1 := by
  by_cases same : target = key
  · subst target
    simp
  · simp [Function.update_of_ne same]

theorem pop_port_bounds (contents : ∀ key, List (Alphabet key)) (key target : Key) :
    (contents target).length ≤ (Function.update contents key (contents key).tail target).length + 1 ∧
      (Function.update contents key (contents key).tail target).length ≤ (contents target).length := by
  by_cases same : target = key
  · subst target
    simp only [Function.update_self, List.length_tail]
    omega
  · simp [Function.update_of_ne same]

theorem stepAux_port_bounds (statement : TM2.Stmt Alphabet Label Registers)
    (registers : Registers) (contents : ∀ key, List (Alphabet key)) (target : Key) :
    (contents target).length ≤ ((TM2.stepAux statement registers contents).stk target).length + popCount statement ∧
      ((TM2.stepAux statement registers contents).stk target).length ≤
        (contents target).length + pushCount statement := by
  induction statement generalizing registers contents with
  | push key value rest ih =>
      have delta := push_port_bounds contents key target (value registers)
      have later := ih registers (Function.update contents key (value registers :: contents key))
      simp only [TM2.stepAux, popCount, pushCount]
      constructor <;> omega
  | peek key update rest ih => exact ih _ contents
  | pop key update rest ih =>
      have delta := pop_port_bounds contents key target
      have later := ih (update registers (contents key).head?)
        (Function.update contents key (contents key).tail)
      simp only [TM2.stepAux, popCount, pushCount]
      constructor <;> omega
  | load update rest ih => exact ih _ contents
  | branch condition yes no yesIH noIH =>
      cases chosen : condition registers with
      | false =>
          have later := noIH registers contents
          simp only [TM2.stepAux, chosen, Bool.cond_false, popCount, pushCount]
          have pops := le_max_right (popCount yes) (popCount no)
          have pushes := le_max_right (pushCount yes) (pushCount no)
          constructor <;> omega
      | true =>
          have later := yesIH registers contents
          simp only [TM2.stepAux, chosen, Bool.cond_true, popCount, pushCount]
          have pops := le_max_left (popCount yes) (popCount no)
          have pushes := le_max_left (pushCount yes) (pushCount no)
          constructor <;> omega
  | goto label => simp [TM2.stepAux, popCount, pushCount]
  | halt => simp [TM2.stepAux, popCount, pushCount]

end Statement

def machinePopBound (machine : FinTM2) : Nat :=
  (@Finset.univ machine.Λ machine.ΛFin).sup fun label => popCount (machine.m label)

theorem command_le_machinePopBound (machine : FinTM2) (label : machine.Λ) :
    popCount (machine.m label) ≤ machinePopBound machine := by
  let := machine.ΛFin
  exact Finset.le_sup (f := fun selected => popCount (machine.m selected)) (Finset.mem_univ label)

theorem step_port_bounds (machine : FinTM2) (target : machine.K)
    (before after : machine.Cfg) (advanced : machine.step before = some after) :
    (before.stk target).length ≤ (after.stk target).length + machinePopBound machine ∧
      (after.stk target).length ≤ (before.stk target).length + machinePushBound machine := by
  rcases before with ⟨label, registers, contents⟩
  cases label with
  | none => cases advanced
  | some label =>
      have same : TM2.stepAux (machine.m label) registers contents = after := Option.some.inj advanced
      rw [← same]
      dsimp only
      have bounds := stepAux_port_bounds (machine.m label) registers contents target
      have pops := command_le_machinePopBound machine label
      have pushes := command_le_machinePushBound machine label
      constructor <;> omega

theorem iterate_port_bounds (machine : FinTM2) (target : machine.K)
    (count : Nat) (before after : machine.Cfg)
    (ran : (fun state : Option machine.Cfg => state.bind machine.step)^[count] (some before) = some after) :
    (before.stk target).length ≤ (after.stk target).length + machinePopBound machine * count ∧
      (after.stk target).length ≤ (before.stk target).length + machinePushBound machine * count := by
  induction count generalizing before with
  | zero =>
      have same : before = after := Option.some.inj ran
      subst before
      simp
  | succ count ih =>
      rw [Function.iterate_succ_apply] at ran
      cases advanced : machine.step before with
      | none =>
          simp only [Option.bind_some, advanced] at ran
          have empty : (fun state : Option machine.Cfg => state.bind machine.step)^[count] none = none :=
            Function.iterate_fixed (by rfl) count
          rw [empty] at ran
          contradiction
      | some middle =>
          simp only [Option.bind_some, advanced] at ran
          have first := step_port_bounds machine target before middle advanced
          have rest := ih middle ran
          constructor <;> nlinarith

/-- The constants come from the fixed finite transition table. Neither an
output-writing assumption nor a one-symbol-per-macrostep assumption is used. -/
theorem io_lengths_le (machine : FinTM2) (distinct : machine.k₀ ≠ machine.k₁)
    {input : List (machine.Γ machine.k₀)} {output : List (machine.Γ machine.k₁)}
    {time : Nat} (executed : TM2OutputsInTime machine input (some output) time) :
    input.length ≤ machinePopBound machine * time ∧ output.length ≤ machinePushBound machine * time := by
  have inputBound := (iterate_port_bounds machine machine.k₀ executed.steps
    (initList machine input) (haltList machine output) executed.evals_in_steps).1
  have outputBound := (iterate_port_bounds machine machine.k₁ executed.steps
    (initList machine input) (haltList machine output) executed.evals_in_steps).2
  simp only [initList, haltList, dite_true, dite_false, distinct, Ne.symm distinct, List.length_nil, Nat.zero_add] at inputBound outputBound
  exact ⟨inputBound.trans (Nat.mul_le_mul_left _ executed.steps_le_m),
    outputBound.trans (Nat.mul_le_mul_left _ executed.steps_le_m)⟩

/-- The existing physical two-pass composition has a linear time join
when its first program has separate input and output ports. -/
def composition_linear (first second : FinTM2)
    [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
    (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (distinct : first.k₀ ≠ first.k₁)
    {input : List (first.Γ first.k₀)} {middle : List (first.Γ first.k₁)}
    {output : List (second.Γ second.k₁)} {firstTime secondTime : Nat}
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    (secondRun : TM2OutputsInTime second (middle.map bridge) (some output) secondTime) :
    TM2OutputsInTime (StackMachineComposition.machine first second bridge) input (some output)
      ((1 + 2 * machinePushBound first) * firstTime + secondTime + 2) := by
  have combined := StackMachineComposition.outputs first second bridge input middle output
    firstTime secondTime firstRun secondRun
  have bytes := (io_lengths_le first distinct firstRun).2
  exact ⟨combined.toEvalsTo, combined.steps_le_m.trans (by nlinarith)⟩

namespace Controls

def identityRun (word : List Bool) : TM2OutputsInTime (Turing.idComputer Bool) word (some word) 1 := by
  apply StackMachineComposition.oneStep
  rfl

theorem in_place_output_refutes_every_uniform_time_factor (factor : Nat) :
    ∃ word : List Bool, Nonempty (TM2OutputsInTime (Turing.idComputer Bool) word (some word) 1) ∧
      factor * 1 < word.length := by
  exact ⟨List.replicate (factor + 1) true, ⟨identityRun _⟩, by simp⟩

theorem in_place_identity_has_no_push_or_pop_budget :
    machinePushBound (Turing.idComputer Bool) = 0 ∧ machinePopBound (Turing.idComputer Bool) = 0 := by decide

end Controls

end Mettapedia.Computability.StackMachinePortTime
