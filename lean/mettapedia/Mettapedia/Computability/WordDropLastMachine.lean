import Mettapedia.Computability.StackMachineComposition

/-!
# Dropping a final physical symbol with a finite buffer

One pending symbol delays publication until the next symbol arrives. At end
of input the pending symbol is discarded, and the temporary stack is reversed
back to the input/output port. No whole word enters the finite registers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.WordDropLastMachine

open Turing StateTransition Turing.TM2.Stmt

variable (Γ : Type) [Fintype Γ] [Inhabited Γ]

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Γ
  Λ := Bool
  main := false
  σ := Option Γ × Option Γ
  initialState := (none, none)
  m phase := if phase then
    pop true (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (push false (fun state => state.2.getD default) (goto fun _ => true))
        (load (fun _ => (none, none)) halt))
    else
    pop false (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (branch (fun state => state.1.isSome)
          (push true (fun state => state.1.getD default)
            (load (fun state => (state.2, none)) (goto fun _ => false)))
          (load (fun state => (state.2, none)) (goto fun _ => false)))
        (load (fun _ => (none, none)) (goto fun _ => true)))

def config (phase : Option Bool) (pending current : Option Γ) (input temporary : List Γ) :
    (machine Γ).Cfg where
  l := phase
  var := (pending, current)
  stk key := if (show Bool from key) then temporary else input

local macro "buffer_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]))

theorem read_symbol (pending current : Option Γ) (head : Γ) (input temporary : List Γ) :
    (machine Γ).step (config Γ (some false) pending current (head :: input) temporary) =
      some (config Γ (some false) (some head) none input (pending.toList ++ temporary)) := by
  cases pending <;> buffer_step

theorem read_end (pending current : Option Γ) (temporary : List Γ) :
    (machine Γ).step (config Γ (some false) pending current [] temporary) =
      some (config Γ (some true) none none [] temporary) := by buffer_step

theorem restore_symbol (pending current : Option Γ) (head : Γ) (input temporary : List Γ) :
    (machine Γ).step (config Γ (some true) pending current input (head :: temporary)) =
      some (config Γ (some true) pending (some head) (head :: input) temporary) := by buffer_step

theorem restore_end (pending current : Option Γ) (input : List Γ) :
    (machine Γ).step (config Γ (some true) pending current input []) =
      some (config Γ none none none input []) := by buffer_step

def scan_run (word : List Γ) (last : Γ) (pending current : Option Γ) (temporary : List Γ) :
    EvalsToInTime (machine Γ).step
      (config Γ (some false) pending current (word ++ [last]) temporary)
      (some (config Γ (some true) none none []
        (word.reverse ++ pending.toList ++ temporary))) (word.length + 2) := by
  induction word generalizing pending current temporary with
  | nil =>
      have first := StackMachineComposition.oneStep (read_symbol Γ pending current last [] temporary)
      have finish := StackMachineComposition.oneStep (read_end Γ (some last) none (pending.toList ++ temporary))
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ first finish
  | cons head rest ih =>
      have first := StackMachineComposition.oneStep
        (read_symbol Γ pending current head (rest ++ [last]) temporary)
      have finish := ih (some head) none (pending.toList ++ temporary)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 2) _ _ _ first finish

def restore_run (temporary input : List Γ) (pending current : Option Γ) :
    EvalsToInTime (machine Γ).step (config Γ (some true) pending current input temporary)
      (some (config Γ none none none (temporary.reverse ++ input) [])) (temporary.length + 1) := by
  induction temporary generalizing input pending current with
  | nil => simpa using StackMachineComposition.oneStep (restore_end Γ pending current input)
  | cons head rest ih =>
      have first := StackMachineComposition.oneStep (restore_symbol Γ pending current head input rest)
      have finish := ih (head :: input) pending (some head)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

theorem initial_agrees (word : List Γ) :
    initList (machine Γ) word = config Γ (some false) none none word [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halted_agrees (word : List Γ) :
    haltList (machine Γ) word = config Γ none none none word [] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The last symbol is physically consumed, not removed by an uncharged host
operation. The statement admits every value of that final symbol. -/
def outputs (word : List Γ) (last : Γ) :
    TM2OutputsInTime (machine Γ) (word ++ [last]) (some word) (2 * word.length + 3) := by
  have scanned := scan_run Γ word last none none []
  simp only [Option.toList_none, List.append_nil] at scanned
  have restored := restore_run Γ word.reverse [] none none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have joined := EvalsToInTime.trans _ (word.length + 2) (word.length + 1) _ _ _ scanned restored
  change EvalsToInTime _ (initList (machine Γ) _) (some (haltList (machine Γ) _)) _
  rw [initial_agrees, halted_agrees]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

def empty_outputs : TM2OutputsInTime (machine Γ) [] (some []) 2 := by
  have first := StackMachineComposition.oneStep (read_end Γ none none [])
  have finish := StackMachineComposition.oneStep (restore_end Γ none none [])
  have joined := EvalsToInTime.trans _ 1 1 _ _ _ first finish
  change EvalsToInTime _ (initList (machine Γ) []) (some (haltList (machine Γ) [])) 2
  rw [initial_agrees, halted_agrees]
  exact joined

end Mettapedia.Computability.WordDropLastMachine
