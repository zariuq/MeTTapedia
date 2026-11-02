import Mettapedia.Computability.BinaryWordComparison
import Mettapedia.Computability.StackMachineCompositionReflection

/-!
# In-place binary countdown with an amortized physical clock

The counter keeps its original width, including high zero bits. A finite borrow
scan changes only the leading zero run and its first one. A Boolean result
prefix distinguishes a successful debit from zero. The pending borrow markers
remain on a physical stack; no represented natural enters the registers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.BinaryCountdownMachine

open Turing StateTransition Turing.TM2.Stmt
open BinaryStackArithmetic

def decrement : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => (decrement rest).map (List.cons true)
  | true :: rest => some (false :: rest)

def clock : List Bool → Nat
  | [] => 2
  | false :: rest => clock rest + 2
  | true :: _rest => 2

def zeros : List Bool → Nat
  | [] => 0
  | false :: rest => zeros rest + 1
  | true :: rest => zeros rest

theorem zeros_le_length (word : List Bool) : zeros word ≤ word.length := by
  induction word with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [zeros] <;> omega

theorem clock_le_length (word : List Bool) : clock word ≤ 2 * word.length + 2 := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => simp only [clock, List.length_cons]; omega
      | true => simp [clock]

theorem decrement_length {before after : List Bool} (changed : decrement before = some after) :
    after.length = before.length := by
  induction before generalizing after with
  | nil => simp [decrement] at changed
  | cons bit rest ih =>
      cases bit with
      | false =>
          cases tail : decrement rest with
          | none => simp [decrement, tail] at changed
          | some next =>
              simp only [decrement, tail, Option.map_some, Option.some.injEq] at changed
              subst after
              simp [ih tail]
      | true =>
          simp only [decrement, Option.some.injEq] at changed
          subst after
          rfl

theorem decrement_value {before after : List Bool} (changed : decrement before = some after) :
    value before = value after + 1 := by
  induction before generalizing after with
  | nil => simp [decrement] at changed
  | cons bit rest ih =>
      cases bit with
      | false =>
          cases tail : decrement rest with
          | none => simp [decrement, tail] at changed
          | some next =>
              simp only [decrement, tail, Option.map_some, Option.some.injEq] at changed
              subst after
              have previous := ih tail
              simp only [BinaryWordComparison.value_cons, bitValue, Bool.false_eq_true, if_false, if_true] at previous ⊢
              omega
      | true =>
          simp only [decrement, Option.some.injEq] at changed
          subst after
          simp [BinaryWordComparison.value_cons, bitValue, Nat.add_comm]

theorem decrement_none_iff (word : List Bool) : decrement word = none ↔ value word = 0 := by
  induction word with
  | nil => simp [decrement]
  | cons bit rest ih => cases bit <;> simp [decrement, BinaryWordComparison.value_cons, bitValue, ih]

/-- One payload-read transition joins each actual debit. The potential pays
for its complete borrow scan and restoration rather than a unit-cost counter. -/
theorem debit_amortized {before after : List Bool} (changed : decrement before = some after) :
    clock before + 1 + 2 * zeros after = 2 * zeros before + 5 := by
  induction before generalizing after with
  | nil => simp [decrement] at changed
  | cons bit rest ih =>
      cases bit with
      | false =>
          cases tail : decrement rest with
          | none => simp [decrement, tail] at changed
          | some next =>
              simp only [decrement, tail, Option.map_some, Option.some.injEq] at changed
              subst after
              have previous := ih tail
              simp only [clock, zeros]
              omega
      | true =>
          simp only [decrement, Option.some.injEq] at changed
          subst after
          simp [clock, zeros]
          omega

inductive Chain : List Bool → List Bool → Nat → Nat → Prop where
  | refl (word : List Bool) : Chain word word 0 0
  | step {before middle after : List Bool} {count work : Nat}
      (changed : decrement before = some middle) (tail : Chain middle after count work) :
      Chain before after (count + 1) (clock before + 1 + work)

theorem Chain.value {before after : List Bool} {count work : Nat} (path : Chain before after count work) :
    BinaryStackArithmetic.value before = BinaryStackArithmetic.value after + count := by
  induction path with
  | refl => simp
  | step changed _ ih => have debit := decrement_value changed; omega

theorem Chain.amortized {before after : List Bool} {count work : Nat} (path : Chain before after count work) :
    work + 2 * zeros after = 2 * zeros before + 5 * count := by
  induction path with
  | refl => omega
  | step changed _ ih => have debit := debit_amortized changed; omega

theorem Chain.work_le {before after : List Bool} {count work : Nat} (path : Chain before after count work) :
    work ≤ 5 * count + 2 * before.length := by
  have actual := path.amortized
  have potential := zeros_le_length before
  omega

abbrev Alphabet : Bool → Type
  | false => Bool
  | true => Unit
abbrev Registers := Option Bool × Bool × Option Unit

def clean (success : Bool) : Registers := (none, success, none)

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ := Alphabet
  Λ := Bool
  main := false
  σ := Registers
  initialState := clean false
  m phase := if phase then
    pop true (fun state marker => (state.1, state.2.1, marker))
      (branch (fun state => state.2.2.isSome)
        (push false (fun state => state.2.1)
          (load (fun state => clean state.2.1) (goto fun _ => true)))
        (push false (fun state => state.2.1) (load (fun _ => clean false) halt)))
    else pop false (fun state bit => (bit, state.2))
      (branch (fun state => state.1.isSome)
        (branch (fun state => state.1.getD false)
          (push false (fun _ => false) (load (fun _ => clean true) (goto fun _ => true)))
          (push true (fun _ => ()) (load (fun _ => clean false) (goto fun _ => false))))
        (load (fun _ => clean false) (goto fun _ => true)))

def config (phase : Option Bool) (success : Bool) (counter : List Bool) (pending : List Unit) : machine.Cfg where
  l := phase
  var := clean success
  stk key := match (show Bool from key) with
    | false => counter
    | true => pending

local macro "count_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, clean, TM2.step, TM2.stepAux, haltList]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]))

theorem scan_false (counter : List Bool) (pending : List Unit) :
    machine.step (config (some false) false (false :: counter) pending) =
      some (config (some false) false counter (() :: pending)) := by count_step

theorem scan_true (counter : List Bool) (pending : List Unit) :
    machine.step (config (some false) false (true :: counter) pending) =
      some (config (some true) true (false :: counter) pending) := by count_step

theorem scan_end (pending : List Unit) :
    machine.step (config (some false) false [] pending) = some (config (some true) false [] pending) := by count_step

theorem restore_marker (success : Bool) (counter : List Bool) (pending : List Unit) :
    machine.step (config (some true) success counter (() :: pending)) =
      some (config (some true) success (success :: counter) pending) := by count_step

theorem restore_end (success : Bool) (counter : List Bool) :
    machine.step (config (some true) success counter []) = some (haltList machine (success :: counter)) := by count_step

def restore_run (pending : List Unit) (counter : List Bool) (success : Bool) :
    EvalsToInTime machine.step (config (some true) success counter pending)
      (some (haltList machine (success :: (List.replicate pending.length success ++ counter)))) (pending.length + 1) := by
  induction pending generalizing counter with
  | nil => simpa using StackMachineComposition.oneStep (restore_end success counter)
  | cons marker rest ih =>
      cases marker
      have first := StackMachineComposition.oneStep (restore_marker success counter rest)
      have finish := ih (success :: counter)
      simpa [List.replicate_succ', List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def resume (pending : Nat) (word : List Bool) : List Bool :=
  match decrement word with
  | none => false :: (List.replicate pending false ++ word)
  | some after => true :: (List.replicate pending true ++ after)

theorem resume_length (word : List Bool) : (resume 0 word).length = word.length + 1 := by
  cases changed : decrement word with
  | none => simp [resume, changed]
  | some after => simp [resume, changed, decrement_length changed]

theorem resume_false (pending : Nat) (word : List Bool) : resume (pending + 1) word = resume pending (false :: word) := by
  cases changed : decrement word <;> simp [resume, decrement, changed, List.replicate_succ', List.append_assoc]

def from_scan (word : List Bool) (pending : List Unit) :
    EvalsToInTime machine.step (config (some false) false word pending)
      (some (haltList machine (resume pending.length word))) (clock word + pending.length) := by
  induction word generalizing pending with
  | nil =>
      have first := StackMachineComposition.oneStep (scan_end pending)
      have finish := restore_run pending [] false
      have joined := EvalsToInTime.trans _ 1 (pending.length + 1) _ _ _ first finish
      have bounded := WordEqualityMachine.within joined (show _ ≤ clock [] + pending.length from by simp only [clock]; omega)
      simpa [resume, decrement] using bounded
  | cons bit rest ih =>
      cases bit with
      | false =>
          have first := StackMachineComposition.oneStep (scan_false rest pending)
          have finish := ih (() :: pending)
          have joined := EvalsToInTime.trans _ 1 (clock rest + (() :: pending).length) _ _ _ first finish
          have bounded := WordEqualityMachine.within joined
            (show _ ≤ clock (false :: rest) + pending.length from by simp only [clock, List.length_cons]; omega)
          simpa only [List.length_cons, resume_false] using bounded
      | true =>
          have first := StackMachineComposition.oneStep (scan_true rest pending)
          have finish := restore_run pending (false :: rest) true
          have joined := EvalsToInTime.trans _ 1 (pending.length + 1) _ _ _ first finish
          have bounded := WordEqualityMachine.within joined
            (show _ ≤ clock (true :: rest) + pending.length from by simp only [clock]; omega)
          simpa [resume, decrement] using bounded

theorem initial_agrees (word : List Bool) : initList machine word = config (some false) false word [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- Success and zero are both completed physical results, with the whole
counter retained at its original width and one explicit result flag. -/
def outputs (word : List Bool) : TM2OutputsInTime machine word (some (resume 0 word)) (clock word) := by
  have run := from_scan word []
  simp only [List.length_nil, Nat.add_zero] at run
  change EvalsToInTime machine.step (initList machine word) (some (haltList machine (resume 0 word))) _
  rw [initial_agrees]
  exact run

def stackCells (state : machine.Cfg) : Nat := (state.stk false).length + (state.stk true).length

/-- A successful internal transition only transfers a cell. Publication adds
the one status bit; it is also the transition that halts the machine. -/
theorem step_stack_cells (before after : machine.Cfg) (advanced : machine.step before = some after) :
    stackCells after = stackCells before + if after.l.isNone then 1 else 0 := by
  cases before with
  | mk label registers contents =>
      cases label with
      | none => cases advanced
      | some phase =>
          cases phase with
          | false =>
              cases counter : contents false with
              | nil =>
                  simp [FinTM2.step, machine, TM2.step, TM2.stepAux, counter] at advanced
                  cases advanced
                  simp [stackCells, counter]
              | cons bit rest =>
                  cases bit <;>
                    simp [FinTM2.step, machine, TM2.step, TM2.stepAux, counter] at advanced <;>
                    cases advanced <;> simp [stackCells, Function.update, counter]
                  all_goals omega
          | true =>
              cases pending : contents true with
              | nil =>
                  simp [FinTM2.step, machine, TM2.step, TM2.stepAux, pending] at advanced
                  cases advanced
                  simp [stackCells, Function.update, pending]
              | cons marker rest =>
                  cases marker
                  simp [FinTM2.step, machine, TM2.step, TM2.stepAux, pending] at advanced
                  cases advanced
                  simp [stackCells, Function.update, pending]
                  all_goals omega

theorem reached_stack_cells (word : List Bool) (state : machine.Cfg)
    (path : Reaches machine.step (initList machine word) state) :
    stackCells state = word.length + if state.l.isNone then 1 else 0 := by
  induction path with
  | refl => simp [stackCells, initList, machine]
  | @tail middle final _path advanced ih =>
      have advancedEq := Option.mem_def.mp advanced
      have active : middle.l ≠ none := by
        intro halted
        have absent := (StackMachineComposition.source_step_none_iff machine middle).mpr halted
        rw [absent] at advancedEq
        cases advancedEq
      have notNone : middle.l.isNone = false := by cases selected : middle.l <;> simp_all
      have changed := step_stack_cells middle final advancedEq
      simp only [notNone, Bool.false_eq_true, if_false, Nat.add_zero] at ih
      omega

theorem reached_stack_cells_le (word : List Bool) (state : machine.Cfg)
    (path : Reaches machine.step (initList machine word) state) : stackCells state ≤ word.length + 1 := by
  rw [reached_stack_cells word state path]
  split <;> omega

end Mettapedia.Computability.BinaryCountdownMachine
