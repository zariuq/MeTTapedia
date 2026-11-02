import Mettapedia.Machines.PrefixPortfolio
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Retained dyadic execution of compiled four-stack machines

The worker executes actual `TM2.step` transitions from Mathlib's compiler of
partial-recursive list programs. A readout decodes the terminated main stack;
running configurations cannot publish values. The compiler's existing
simulation theorem supplies output soundness and eventual completion.

The allocation theorem counts these machine transitions and reserved idle
slots. It does not charge the portfolio implementation's administration or
claim a wall-clock bound for Lean or the native learner.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PrefixMachine

open Mettapedia.UniversalAI.TimeBoundedAIXI
open Turing.PartrecToTM2

def readNumber : List Γ' → Option (Nat × List Γ')
  | [] => none
  | .cons :: rest => some (0, rest)
  | .consₗ :: _rest => none
  | .bit0 :: rest => (readNumber rest).map fun fields => (2 * fields.1, fields.2)
  | .bit1 :: rest => (readNumber rest).map fun fields => (2 * fields.1 + 1, fields.2)

theorem readNumber_trPosNum (number : PosNum) (suffix : List Γ') :
    readNumber (trPosNum number ++ .cons :: suffix) = some ((number : Nat), suffix) := by
  induction number with
  | one => simp [trPosNum, readNumber]
  | bit0 number ih => simp [trPosNum, readNumber, ih, PosNum.cast_bit0, two_mul]
  | bit1 number ih => simp [trPosNum, readNumber, ih, PosNum.cast_bit1, two_mul]

theorem readNumber_trNum (number : Num) (suffix : List Γ') :
    readNumber (trNum number ++ .cons :: suffix) = some ((number : Nat), suffix) := by
  cases number with
  | zero => simp [trNum, readNumber]
  | pos number => simpa [trNum] using readNumber_trPosNum number suffix

theorem readNumber_trNat (number : Nat) (suffix : List Γ') :
    readNumber (trNat number ++ .cons :: suffix) = some (number, suffix) := by
  simpa [trNat] using readNumber_trNum (number : Num) suffix

def readSingleton (stack : List Γ') : Option Nat :=
  (readNumber stack).bind fun fields =>
    if fields.2 = [] ∧ trList [fields.1] = stack then some fields.1 else none

theorem readSingleton_trList (number : Nat) : readSingleton (trList [number]) = some number := by
  simp [readSingleton, trList, readNumber_trNat]

theorem readSingleton_sound {stack : List Γ'} {number : Nat}
    (decoded : readSingleton stack = some number) : stack = trList [number] := by
  obtain ⟨fields, _parsed, canonical⟩ := Option.bind_eq_some_iff.mp decoded
  split at canonical
  · rename_i accepted
    cases Option.some.inj canonical
    exact accepted.2.symm
  · cases canonical

def readOutput {α : Type*} [Encodable α] (state : Cfg') : Option α :=
  match state.l with
  | some _ => none
  | none => (readSingleton (state.stk .main)).bind fun encoded =>
      (Encodable.decode encoded).bind fun answer =>
        if Encodable.encode answer = encoded then some answer else none

theorem readOutput_halt {α : Type*} [Encodable α] (answer : α) :
    readOutput (halt [Encodable.encode answer]) = some answer := by
  change (readSingleton (trList [Encodable.encode answer])).bind _ = _
  rw [readSingleton_trList]
  simp [Encodable.encodek]

theorem readOutput_stopped {α : Type*} [Encodable α] (state : Cfg') (answer : α)
    (found : readOutput state = some answer) : Turing.TM2.step tr state = none := by
  cases state with
  | mk rawLabel rawRegister rawStore =>
      cases rawLabel with
      | none => rfl
      | some label => simp [readOutput] at found

def worker {α : Type*} [Encodable α] (code : Turing.ToPartrec.Code)
    (input : KolmogorovComplexity.BinString → Nat) : PrefixPortfolio.Worker Cfg' α where
  initial word := init code [input word]
  step _word := Turing.TM2.step tr
  read _word := readOutput
  stopped _word := readOutput_stopped

theorem compiled_finite_control (code : Turing.ToPartrec.Code) :
    @Turing.TM2.Supports _ _ _ _ ⟨trNormal code Cont'.halt⟩ tr (codeSupp code Cont'.halt) :=
  tr_supports code Cont'.halt

theorem worker_sound {α : Type*} [Encodable α] (code : Turing.ToPartrec.Code)
    (input : KolmogorovComplexity.BinString → Nat) (word : KolmogorovComplexity.BinString)
    (work : Nat) (answer : α)
    (found : ((worker (α := α) code input).searcher word).result work = some answer) :
    [Encodable.encode answer] ∈ code.eval [input word] := by
  let state := StepCounting.runFor (Turing.TM2.step tr) work (init code [input word])
  have read : readOutput state = some answer := found
  have terminated : state ∈ StateTransition.eval (Turing.TM2.step tr) (init code [input word]) :=
    StateTransition.mem_eval.mpr ⟨StepCounting.reaches_runFor _ _ _, readOutput_stopped state answer read⟩
  rw [tr_eval] at terminated
  obtain ⟨output, computes, same⟩ := (Part.mem_map_iff halt).mp terminated
  have decoded : (readSingleton (trList output)).bind (fun encoded =>
      (Encodable.decode (α := α) encoded).bind fun value =>
        if Encodable.encode value = encoded then some value else none) = some answer := by
    simpa [← same, readOutput, halt, K'.elim] using read
  -- The compiler below emits singleton lists. General list programs can
  -- terminate with other list shapes, so this interface checks the shape.
  cases output with
  | nil => simp [readSingleton, trList, readNumber] at decoded
  | cons head tail =>
      simp only [trList, readSingleton, readNumber_trNat] at decoded
      by_cases empty : trList tail = []
      · have nilTail : tail = [] := by
          cases tail with
          | nil => rfl
          | cons item rest => simp [trList] at empty
        subst tail
        have canonicalRead : (Encodable.decode head).bind (fun value =>
            if Encodable.encode value = head then some value else none) = some answer := by
          have readHead : readOutput (halt [head]) = some answer := by simpa only [← same] using read
          change (readSingleton (trList [head])).bind _ = some answer at readHead
          rwa [readSingleton_trList, Option.bind_some] at readHead
        have sameHead : Encodable.encode answer = head := by
          obtain ⟨value, _decodes, returned⟩ := Option.bind_eq_some_iff.mp canonicalRead
          split at returned
          · rename_i canonical
            cases Option.some.inj returned
            exact canonical
          · cases returned
        simpa only [sameHead] using computes
      · simp [empty] at decoded

theorem worker_complete {α : Type*} [Encodable α] (code : Turing.ToPartrec.Code)
    (input : KolmogorovComplexity.BinString → Nat) (word : KolmogorovComplexity.BinString)
    (answer : α) (computes : [Encodable.encode answer] ∈ code.eval [input word]) :
    ∃ work, ((worker (α := α) code input).searcher word).result work = some answer := by
  have terminated : halt [Encodable.encode answer] ∈
      StateTransition.eval (Turing.TM2.step tr) (init code [input word]) := by
    rw [tr_eval]
    exact Part.mem_map halt computes
  obtain ⟨path, _stopped⟩ := StateTransition.mem_eval.mp terminated
  obtain ⟨work, reached⟩ := StepCounting.exists_runFor_eq_of_reaches path
  refine ⟨work, ?_⟩
  change readOutput (StepCounting.runFor (Turing.TM2.step tr) work (init code [input word])) = some answer
  rw [reached]
  exact readOutput_halt answer

#print axioms readNumber_trPosNum
#print axioms readNumber_trNum
#print axioms readNumber_trNat
#print axioms readSingleton_trList
#print axioms readSingleton_sound
#print axioms readOutput_halt
#print axioms readOutput_stopped
#print axioms compiled_finite_control
#print axioms worker_sound
#print axioms worker_complete

end Mettapedia.Machines.PrefixMachine
