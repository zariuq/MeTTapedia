import Mettapedia.Computability.FiniteSupportMachine
import Mettapedia.Computability.StackMachineContextCall
import Mettapedia.Machines.PrefixMachine

/-!
# Finite packages for the actual partial-recursive compiler

The existing compiler support fixes the finite label table before every
input. The packaged machine has the same four physical stacks, alphabet,
registers and counted transitions. Source executions and packaged executions
reflect in the same budget; no fast general-purpose compilation law is used.

Canonical input/output words are the existing `trList` representation.
Clean halting is proved at those inputs, not postulated for arbitrary malformed
stack words. Preparing an input and interpreting an output remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.FiniteCompiledMachine

open Turing StateTransition
open Turing.PartrecToTM2
open Mettapedia.Computability

abbrev keys : Fintype K' :=
  ⟨{.main, .rev, .aux, .stack}, by intro key; cases key <;> simp⟩

attribute [local instance] keys

def support (code : ToPartrec.Code) : Finset Λ' := codeSupp code Cont'.halt

def entry (code : ToPartrec.Code) : FiniteSupportMachine.Restricted (support code) :=
  ⟨trNormal code Cont'.halt, (PrefixMachine.compiled_finite_control code).1⟩

def machine (code : ToPartrec.Code) : FinTM2 :=
  FiniteSupportMachine.machine tr (support code) (entry code) (none : Option Γ') K'.main K'.main

attribute [local implicit_reducible] machine FiniteSupportMachine.machine

def embed (code : ToPartrec.Code) (configuration : Cfg') : (machine code).Cfg :=
  FiniteSupportMachine.embed (support code) (entry code) configuration

def erase (code : ToPartrec.Code) (configuration : (machine code).Cfg) : Cfg' :=
  FiniteSupportMachine.erase (support code) configuration

theorem closed (code : ToPartrec.Code) (label : Λ') (present : label ∈ support code) :
    TM2.SupportsStmt (support code) (tr label) :=
  (PrefixMachine.compiled_finite_control code).2 label present

theorem initial_valid (code : ToPartrec.Code) (input : List Nat) :
    FiniteSupportMachine.Valid (support code) (init code input) := by
  exact Finset.some_mem_insertNone.mpr (PrefixMachine.compiled_finite_control code).1

theorem initial_agrees (code : ToPartrec.Code) (input : List Nat) :
    embed code (init code input) = initList (machine code) (trList input) := by
  change TM2.Cfg.mk (some (FiniteSupportMachine.select (support code) (entry code) (entry code).val))
    none (K'.elim (trList input) [] [] []) = _
  rw [FiniteSupportMachine.select_present]
  simp only [initList, machine, FiniteSupportMachine.machine]
  congr 1
  funext key
  cases key <;> rfl

theorem halt_agrees (code : ToPartrec.Code) (output : List Nat) :
    embed code (halt output) = haltList (machine code) (trList output) := by
  simp only [embed, FiniteSupportMachine.embed, halt, Option.map_none, haltList, machine,
    FiniteSupportMachine.machine]
  congr 1
  funext key
  cases key <;> rfl

theorem initial_erases (code : ToPartrec.Code) (input : List Nat) :
    erase code (initList (machine code) (trList input)) = init code input := by
  rw [← initial_agrees]
  exact FiniteSupportMachine.erase_embed (support code) (entry code) _ (initial_valid code input)

theorem halt_erases (code : ToPartrec.Code) (output : List Nat) :
    erase code (haltList (machine code) (trList output)) = halt output := by
  rw [← halt_agrees]
  exact FiniteSupportMachine.erase_embed (support code) (entry code) _ (by simp [FiniteSupportMachine.Valid, halt])

/-- The original machine-transition count is preserved, not merely bounded
by an unspecified effective simulation. -/
def outputs (code : ToPartrec.Code) {input output : List Nat} {time : Nat}
    (original : EvalsToInTime (TM2.step tr) (init code input) (some (halt output)) time) :
    TM2OutputsInTime (machine code) (trList input) (some (trList output)) time := by
  have relabeled := FiniteSupportMachine.lift_execution tr (support code) (entry code) (closed code)
    (initial_valid code input) original
  change EvalsToInTime _ (embed code (init code input)) (some (embed code (halt output))) time at relabeled
  rw [initial_agrees, halt_agrees] at relabeled
  exact relabeled

def reflects_outputs (code : ToPartrec.Code) {input output : List Nat} {time : Nat}
    (packaged : TM2OutputsInTime (machine code) (trList input) (some (trList output)) time) :
    EvalsToInTime (TM2.step tr) (init code input) (some (halt output)) time := by
  have original := FiniteSupportMachine.erase_execution tr (support code) (entry code) (closed code) packaged
  change EvalsToInTime _ (erase code (initList (machine code) (trList input)))
    (some (erase code (haltList (machine code) (trList output)))) time at original
  rwa [initial_erases, halt_erases] at original

/-- The original compiler theorem proves canonical halts for every admitted
encoded input, even when other source computations diverge. -/
theorem clean_halts_at_encoded_input (code : ToPartrec.Code) (input : List Nat) (state : (machine code).Cfg)
    (path : Reaches (machine code).step (initList (machine code) (trList input)) state) (stopped : state.l = none) :
    ∃ output : List Nat, state = haltList (machine code) (trList output) := by
  obtain ⟨counted⟩ := StackMachineComposition.reaches_has_execution path
  let bounded : EvalsToInTime (machine code).step
      (initList (machine code) (trList input)) (some state) counted.steps := ⟨counted, le_rfl⟩
  have raw := FiniteSupportMachine.erase_execution tr (support code) (entry code) (closed code) bounded
  change EvalsToInTime (TM2.step tr) (erase code (initList (machine code) (trList input)))
    (some (erase code state)) counted.steps at raw
  rw [initial_erases] at raw
  have rawStopped : TM2.step tr (erase code state) = none := by
    cases state with
    | mk label registers contents =>
        dsimp only at stopped
        subst label
        rfl
  have evaluated : erase code state ∈ StateTransition.eval (TM2.step tr) (init code input) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches raw.toEvalsTo, rawStopped⟩
  rw [Turing.PartrecToTM2.tr_eval] at evaluated
  obtain ⟨output, _computes, same⟩ := (Part.mem_map_iff halt).mp evaluated
  have represented := congrArg (embed code) same
  have inverse : embed code (erase code state) = state :=
    FiniteSupportMachine.embed_erase (support code) (entry code) state
  rw [halt_agrees, inverse] at represented
  exact ⟨output, represented.symm⟩

abbrev inputInhabited (code : ToPartrec.Code) : Inhabited ((machine code).Γ (machine code).k₀) :=
  inferInstanceAs (Inhabited Γ')
abbrev outputFinite (code : ToPartrec.Code) : Fintype ((machine code).Γ (machine code).k₁) :=
  inferInstanceAs (Fintype Γ')
abbrev outputInhabited (code : ToPartrec.Code) : Inhabited ((machine code).Γ (machine code).k₁) :=
  inferInstanceAs (Inhabited Γ')

attribute [local instance] inputInhabited outputFinite outputInhabited

def contextMachine (code : ToPartrec.Code) : FinTM2 := StackMachineContextCall.machine (machine code)

attribute [local implicit_reducible] contextMachine StackMachineContextCall.machine

/-- The actual compiled source can now be called while retaining its whole
physical argument. The additional cost is explicit, not hidden in decoding. -/
def context_outputs (code : ToPartrec.Code) {input output : List Nat} {time : Nat}
    (original : EvalsToInTime (TM2.step tr) (init code input) (some (halt output)) time) :
    TM2OutputsInTime (contextMachine code) (trList input)
      (some (StackMachineContextCall.packet (machine code) (trList input) (trList output)))
      (time + 3 * (trList input).length + 2 * (trList output).length + 5) :=
  StackMachineContextCall.outputs (machine code) (outputs code original)

theorem context_clean_halts_at_encoded_input (code : ToPartrec.Code) (input : List Nat)
    (state : (contextMachine code).Cfg)
    (path : Reaches (contextMachine code).step (initList (contextMachine code) (trList input)) state)
    (stopped : state.l = none) :
    ∃ output, state = haltList (contextMachine code) output := by
  apply StackMachineContextCall.clean_halts_at (machine code) (trList input) _ state path stopped
  intro original reached halted
  obtain ⟨output, same⟩ := clean_halts_at_encoded_input code input original reached halted
  exact ⟨trList output, same⟩

/-- A completed packet recovers a real encoded source computation. The
clean-halt theorem is instantiated at this encoded input only. -/
theorem context_reflects_outputs (code : ToPartrec.Code) {input : List Nat}
    {returned : List (StackMachineContextCall.Cell (machine code))} {time : Nat}
    (executed : TM2OutputsInTime (contextMachine code) (trList input) (some returned) time) :
    ∃ output : List Nat,
      StackMachineContextCall.packet (machine code) (trList input) (trList output) = returned ∧
      Nonempty (EvalsToInTime (TM2.step tr) (init code input) (some (halt output)) time) := by
  have clean (state : (machine code).Cfg)
      (path : Reaches (machine code).step (initList (machine code) (trList input)) state)
      (stopped : state.l = none) : ∃ output, state = haltList (machine code) output := by
    obtain ⟨output, same⟩ := clean_halts_at_encoded_input code input state path stopped
    exact ⟨trList output, same⟩
  obtain ⟨word, packet, ⟨original⟩⟩ := StackMachineContextCall.reflects_outputs_at (machine code) clean executed
  obtain ⟨output, canonical⟩ := clean_halts_at_encoded_input code input (haltList (machine code) word)
    (StackMachineComposition.execution_reaches original.toEvalsTo) rfl
  have words := congrArg (fun state : (machine code).Cfg => state.stk (machine code).k₁) canonical
  have same : word = trList output := by simpa [haltList] using words
  subst word
  exact ⟨output, packet, ⟨reflects_outputs code original⟩⟩

end Mettapedia.Machines.FiniteCompiledMachine
