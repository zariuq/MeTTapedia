import Mettapedia.Computability.KolmogorovComplexity.NaturalWordEncoding
import Mettapedia.Computability.BinaryWordAddition
import Mettapedia.Machines.ConditionalSourceMachine

/-!
# Linear physical conversion of exact words into compiler natural fields

A virtual high sentinel followed by a one-bit borrow implements the exact
dense word codec. The original word and temporary result remain on stacks.
A second physical pass emits the compiler's canonical natural digits and
their delimiter. Leading zero bits in the source are not discarded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.NaturalWordMachine

open Turing StateTransition Turing.TM2.Stmt
open Turing.PartrecToTM2
open KolmogorovComplexity
open BinaryStackArithmetic (naturalBits increment bitValue)

def borrowWord : Bool → List Bool → List Bool
  | borrow, [] => if borrow then [] else [true]
  | borrow, bit :: rest => (if borrow then !bit else bit) :: borrowWord (borrow && !bit) rest

theorem borrowWord_false (word : List Bool) : borrowWord false word = word ++ [true] := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp [borrowWord, ih]

theorem increment_borrowWord (word : List Bool) : increment (borrowWord true word) = word ++ [true] := by
  induction word with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [borrowWord, borrowWord_false, increment, ih]

theorem borrowWord_naturalBits (word : List Bool) :
    borrowWord true word = naturalBits (NaturalWordEncoding.encode word) := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false =>
          have digit := BinaryWordAddition.naturalBits_digit true (NaturalWordEncoding.encode rest)
            (by simp [bitValue])
          simpa [borrowWord, NaturalWordEncoding.encode, bitValue, ih, Nat.add_comm] using digit.symm
      | true =>
          have successor : naturalBits (NaturalWordEncoding.encode rest + 1) = rest ++ [true] := by
            rw [← BinaryStackArithmetic.increment_naturalBits, ← ih, increment_borrowWord]
          have digit := BinaryWordAddition.naturalBits_digit false (NaturalWordEncoding.encode rest + 1)
            (by simp [bitValue])
          simpa [borrowWord, borrowWord_false, NaturalWordEncoding.encode, bitValue, successor,
            Nat.mul_add, Nat.add_assoc] using digit.symm

theorem borrowWord_length (borrow : Bool) (word : List Bool) :
    word.length ≤ (borrowWord borrow word).length ∧ (borrowWord borrow word).length ≤ word.length + 1 := by
  induction word generalizing borrow with
  | nil => cases borrow <;> simp [borrowWord]
  | cons bit rest ih =>
      have previous := ih (borrow && !bit)
      simp only [borrowWord, List.length_cons]
      constructor <;> omega

def symbol (bit : Bool) : Γ' := if bit then .bit1 else .bit0

theorem trPosNum_agrees (number : PosNum) :
    trPosNum number = (naturalBits (number : Nat)).map symbol := by
  induction number with
  | one => rfl
  | bit0 number ih =>
      have cast : ((PosNum.bit0 number : PosNum) : Nat) = bitValue false + 2 * (number : Nat) := by
        simp [bitValue, PosNum.cast_bit0, two_mul]
      have positive : bitValue false + 2 * (number : Nat) ≠ 0 := by
        have bound := PosNum.to_nat_pos number
        simp only [bitValue, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        omega
      rw [cast, BinaryWordAddition.naturalBits_digit false _ positive]
      simp [trPosNum, ih, symbol]
  | bit1 number ih =>
      have cast : ((PosNum.bit1 number : PosNum) : Nat) = bitValue true + 2 * (number : Nat) := by
        simp [bitValue, PosNum.cast_bit1, two_mul, Nat.add_comm]
      rw [cast, BinaryWordAddition.naturalBits_digit true _ (by simp [bitValue])]
      simp [trPosNum, ih, symbol]

theorem trNum_agrees (number : Num) : trNum number = (naturalBits (number : Nat)).map symbol := by
  cases number with
  | zero => rfl
  | pos number => exact trPosNum_agrees number

theorem trNat_agrees (number : Nat) : trNat number = (naturalBits number).map symbol := by
  simpa [trNat] using trNum_agrees (number : Num)

theorem encoded_field (word : List Bool) :
    (borrowWord true word).map symbol ++ [Γ'.cons] = trList [NaturalWordEncoding.encode word] := by
  rw [borrowWord_naturalBits, ← trNat_agrees]
  rfl

theorem field_length_bounds (word : List Bool) :
    word.length + 1 ≤ (trList [NaturalWordEncoding.encode word]).length ∧
      (trList [NaturalWordEncoding.encode word]).length ≤ word.length + 2 := by
  rw [← encoded_field]
  have bound := borrowWord_length true word
  simp only [List.length_append, List.length_map, List.length_singleton]
  constructor <;> omega

theorem query_length_bounds (program condition : List Bool) :
    program.length + condition.length + 2 ≤
        (Mettapedia.Machines.ConditionalSourceMachine.query NaturalWordEncoding.codec program condition).length ∧
      (Mettapedia.Machines.ConditionalSourceMachine.query NaturalWordEncoding.codec program condition).length ≤
        program.length + condition.length + 4 := by
  have fields : Mettapedia.Machines.ConditionalSourceMachine.query NaturalWordEncoding.codec program condition =
      trList [NaturalWordEncoding.encode program] ++ trList [NaturalWordEncoding.encode condition] := by
    simp [Mettapedia.Machines.ConditionalSourceMachine.query, NaturalWordEncoding.codec, trList, List.append_assoc]
  rw [fields, List.length_append]
  have first := field_length_bounds program
  have second := field_length_bounds condition
  constructor <;> omega

inductive Stack where
  | input | temporary | result
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input | .temporary => Bool
  | .result => Γ'

/-- One borrow and one optional bit are the entire finite register. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet
  Λ := Bool
  main := false
  σ := Bool × Option Bool
  initialState := (true, none)
  m phase := if phase then
    pop .temporary (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome)
        (push .result (fun state => symbol (state.2.getD false)) (goto (fun _ => true)))
        (load (fun _ => (true, none)) halt))
    else
    pop .input (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome)
        (push .temporary (fun state => if state.1 then !(state.2.getD false) else state.2.getD false)
          (load (fun state => (state.1 && !(state.2.getD false), none)) (goto (fun _ => false))))
        (push .result (fun _ => Γ'.cons)
          (branch Prod.fst
            (load (fun _ => (true, none)) (goto (fun _ => true)))
            (push .temporary (fun _ => true) (load (fun _ => (true, none)) (goto (fun _ => true)))))))

def config (phase : Option Bool) (borrow : Bool) (last : Option Bool)
    (input temporary : List Bool) (result : List Γ') : machine.Cfg where
  l := phase
  var := (borrow, last)
  stk key := match key with | .input => input | .temporary => temporary | .result => result

local macro "word_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]))

theorem scan_cons (borrow : Bool) (last : Option Bool) (bit : Bool)
    (input temporary : List Bool) (result : List Γ') :
    machine.step (config (some false) borrow last (bit :: input) temporary result) =
      some (config (some false) (borrow && !bit) none input
        ((if borrow then !bit else bit) :: temporary) result) := by word_step

theorem scan_nil (borrow : Bool) (last : Option Bool) (temporary : List Bool) (result : List Γ') :
    machine.step (config (some false) borrow last [] temporary result) =
      some (config (some true) true none [] (if borrow then temporary else true :: temporary) (Γ'.cons :: result)) := by
  cases borrow <;> word_step

theorem restore_cons (borrow : Bool) (last : Option Bool) (bit : Bool)
    (input temporary : List Bool) (result : List Γ') :
    machine.step (config (some true) borrow last input (bit :: temporary) result) =
      some (config (some true) borrow (some bit) input temporary (symbol bit :: result)) := by word_step

theorem restore_nil (borrow : Bool) (last : Option Bool) (input : List Bool) (result : List Γ') :
    machine.step (config (some true) borrow last input [] result) =
      some (config none true none input [] result) := by word_step

def scan_run (borrow : Bool) (last : Option Bool) (word temporary : List Bool) (result : List Γ') :
    EvalsToInTime machine.step (config (some false) borrow last word temporary result)
      (some (config (some true) true none [] ((borrowWord borrow word).reverse ++ temporary) (Γ'.cons :: result)))
      (word.length + 1) := by
  induction word generalizing borrow last temporary with
  | nil =>
      have first := StackMachineComposition.oneStep (scan_nil borrow last temporary result)
      cases borrow <;> simpa [borrowWord] using first
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (scan_cons borrow last bit rest temporary result)
      have later := ih (borrow && !bit) none ((if borrow then !bit else bit) :: temporary)
      simpa [borrowWord, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def restore_run (borrow : Bool) (last : Option Bool) (input temporary : List Bool) (result : List Γ') :
    EvalsToInTime machine.step (config (some true) borrow last input temporary result)
      (some (config none true none input [] (temporary.reverse.map symbol ++ result))) (temporary.length + 1) := by
  induction temporary generalizing last result with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil borrow last input result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (restore_cons borrow last bit input rest result)
      have later := ih (some bit) (symbol bit :: result)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

theorem init_eq (word : List Bool) : initList machine word = config (some false) true none word [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (word : List Γ') : haltList machine word = config none true none [] [] word := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The suffix is already present on the result stack. Conversion retains
it without traversing or re-encoding it; placing it there is a caller action. -/
def prepend_run (word : List Bool) (suffix : List Γ') :
    EvalsToInTime machine.step (config (some false) true none word [] suffix)
      (some (config none true none [] [] (trList [NaturalWordEncoding.encode word] ++ suffix)))
      (2 * word.length + 3) := by
  have scanned := scan_run true none word [] suffix
  simp only [List.append_nil] at scanned
  have restored := restore_run true none [] (borrowWord true word).reverse (Γ'.cons :: suffix)
  have framed : (borrowWord true word).map symbol ++ Γ'.cons :: suffix =
      trList [NaturalWordEncoding.encode word] ++ suffix := by
    rw [← encoded_field]
    simp only [List.append_assoc, List.singleton_append]
  simp only [List.length_reverse, List.reverse_reverse, framed] at restored
  have joined := EvalsToInTime.trans _ (word.length + 1) ((borrowWord true word).length + 1) _ _ _ scanned restored
  have bound := (borrowWord_length true word).2
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

/-- Every bit, the virtual high sentinel, physical reversal and natural-field
delimiter are charged. The bound is independent of the represented magnitude. -/
def outputs (word : List Bool) :
    TM2OutputsInTime machine word (some (trList [NaturalWordEncoding.encode word])) (2 * word.length + 3) := by
  change EvalsToInTime _ (initList machine word)
    (some (haltList machine (trList [NaturalWordEncoding.encode word]))) _
  rw [init_eq, halt_eq]
  simpa only [List.append_nil] using prepend_run word []

/-- A caller can prepend the program to an already encoded condition.
Only the program is converted here; the condition's placement is not free. -/
def query_run (program condition : List Bool) :
    EvalsToInTime machine.step
      (config (some false) true none program [] (trList [NaturalWordEncoding.encode condition]))
      (some (config none true none [] []
        (Mettapedia.Machines.ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)))
      (2 * program.length + 3) := by
  have fields : Mettapedia.Machines.ConditionalSourceMachine.query NaturalWordEncoding.codec program condition =
      trList [NaturalWordEncoding.encode program] ++ trList [NaturalWordEncoding.encode condition] := by
    simp [Mettapedia.Machines.ConditionalSourceMachine.query, NaturalWordEncoding.codec, trList, List.append_assoc]
  rw [fields]
  exact prepend_run program _

end Mettapedia.Computability.NaturalWordMachine
