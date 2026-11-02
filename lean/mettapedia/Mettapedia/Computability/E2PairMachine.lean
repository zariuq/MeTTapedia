import Mettapedia.Computability.BinaryCountdownMachine
import Mettapedia.Computability.StackMachineRegisters
import Mettapedia.Computability.StackMachineContextCall
import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.Computability.KolmogorovComplexity.FeatureDyadicSearch

/-!
# Physical admission of the existing two-field E2 candidate record

The job contains the canonical candidate record and original word as two
delimiter-framed fields. Length headers are read into a fixed-width binary
countdown, never expanded to a unary payload size. The output is the original
three-word task. Rejection is a nonpublishing state, matching partial admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.E2PairMachine

open Turing StateTransition Turing.TM2.Stmt KolmogorovComplexity
open WordTemplateMachine BinaryStackArithmetic

attribute [local implicit_reducible] BinaryCountdownMachine.machine

abbrev counter : FinTM2 := BinaryCountdownMachine.machine

inductive Auxiliary where
  | input | header | accumulator | result
  deriving DecidableEq, Fintype

inductive Phase where
  | prefix (index : Fin 8) | header (side : Bool) | lengthFirst (side : Bool) | length (side : Bool)
  | run (side label : Bool) | readFlag (side : Bool) | clearCounter (side : Bool) | finishField (side : Bool)
  | candidateEnd | original | originalEnd | reverse | reject
  deriving DecidableEq, Fintype

abbrev Key := Bool ⊕ Auxiliary
abbrev Alphabet : Key → Type
  | .inl key => BinaryCountdownMachine.Alphabet key
  | .inr .header => Unit
  | .inr .input | .inr .accumulator | .inr .result => Option Bool
abbrev Control := BinaryCountdownMachine.Registers × Option (Option Bool) × Option Bool × Option Unit

def initial : Control := (BinaryCountdownMachine.clean false, none, none, none)

def countHeader : List Bool := [true, true, false, true, false, true, false]
def prefixBit : Fin 7 → Bool := ![true, true, false, true, false, true, false]
def advance (index : Fin 8) (active : index.val < 7) : Fin 8 := ⟨index.val + 1, by omega⟩

def following (side : Bool) : Phase := if side then .candidateEnd else .header true

def lift (side : Bool) (statement : counter.Stmt) : TM2.Stmt Alphabet Phase Control :=
  StackMachineRegisters.embedStatement (Alphabet := counter.Γ) (TargetAlphabet := Alphabet)
    Sum.inl (Phase.run side) (fun state => state.1) (fun state value => (value, state.2))
    (fun _ => rfl) (.goto fun _ => .readFlag side) statement

def program : Phase → TM2.Stmt Alphabet Phase Control
  | .prefix index => if active : index.val < 7 then
      pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
        (branch (fun state => decide (state.2.1 = some (some (prefixBit ⟨index.val, active⟩))))
          (load (fun _ => initial) (goto fun _ => .prefix (advance index active)))
          (goto fun _ => .reject))
      else load (fun _ => initial) (goto fun _ => .header false)
  | .header side => pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => decide (state.2.1 = some (some true)))
        (push (.inr .header) (fun _ => ()) (load (fun _ => initial) (goto fun _ => .header side)))
        (branch (fun state => decide (state.2.1 = some (some false)))
          (load (fun _ => initial) (goto fun _ => .lengthFirst side))
          (goto fun _ => .reject)))
  | .lengthFirst side => pop (.inr .header) (fun state marker => (state.1, state.2.1, state.2.2.1, marker))
      (branch (fun state => state.2.2.2.isSome)
        (pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
          (branch (fun state => decide (state.2.1 = some (some true)))
            (push (.inl false) (fun _ => true) (load (fun _ => initial) (goto fun _ => .length side)))
            (goto fun _ => .reject)))
        (load (fun _ => initial) (goto fun _ => .run side false)))
  | .length side => pop (.inr .header) (fun state marker => (state.1, state.2.1, state.2.2.1, marker))
      (branch (fun state => state.2.2.2.isSome)
        (pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
          (branch (fun state => state.2.1.join.isSome)
            (push (.inl false) (fun state => state.2.1.join.getD false)
              (load (fun _ => initial) (goto fun _ => .length side)))
            (goto fun _ => .reject)))
        (load (fun _ => initial) (goto fun _ => .run side false)))
  | .run side label => lift side (counter.m label)
  | .readFlag side => pop (.inl false) (fun state flag => (state.1, state.2.1, flag, state.2.2.2))
      (branch (fun state => decide (state.2.2.1 = some true))
        (pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
          (branch (fun state => state.2.1.join.isSome)
            (push (.inr .accumulator) (fun state => state.2.1.getD none)
              (load (fun _ => initial) (goto fun _ => .run side false)))
            (goto fun _ => .reject)))
        (branch (fun state => decide (state.2.2.1 = some false))
          (load (fun _ => initial) (goto fun _ => .clearCounter side))
          (goto fun _ => .reject)))
  | .clearCounter side => pop (.inl false) (fun state flag => (state.1, state.2.1, flag, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (load (fun _ => initial) (goto fun _ => .clearCounter side))
        (load (fun _ => initial) (goto fun _ => .finishField side)))
  | .finishField side => push (.inr .accumulator) (fun _ => none)
      (load (fun _ => initial) (goto fun _ => following side))
  | .candidateEnd => pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => decide (state.2.1 = some none))
        (load (fun _ => initial) (goto fun _ => .original)) (goto fun _ => .reject))
  | .original => pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.join.isSome)
        (push (.inr .accumulator) (fun state => state.2.1.getD none)
          (load (fun _ => initial) (goto fun _ => .original)))
        (branch (fun state => decide (state.2.1 = some none))
          (load (fun _ => initial) (goto fun _ => .originalEnd)) (goto fun _ => .reject)))
  | .originalEnd => pop (.inr .input) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone)
        (push (.inr .accumulator) (fun _ => none) (load (fun _ => initial) (goto fun _ => .reverse)))
        (goto fun _ => .reject))
  | .reverse => pop (.inr .accumulator) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inr .result) (fun state => state.2.1.getD none) (load (fun _ => initial) (goto fun _ => .reverse)))
        (load (fun _ => initial) halt))
  | .reject => goto fun _ => .reject

def machine : FinTM2 where
  K := Key
  k₀ := .inr .input
  k₁ := .inr .result
  Γ := Alphabet
  Λ := Phase
  main := .prefix 0
  σ := Control
  initialState := initial
  m := program

attribute [local implicit_reducible] machine

def storage (contents : ∀ key, List (counter.Γ key)) (input : List (Option Bool))
    (header : List Unit) (accumulator result : List (Option Bool)) : ∀ key, List (Alphabet key)
  | .inl key => contents key
  | .inr .input => input
  | .inr .header => header
  | .inr .accumulator => accumulator
  | .inr .result => result

def config (phase : Option Phase) (input : List (Option Bool)) (header : List Unit)
    (word : List Bool) (pending : List Unit) (accumulator result : List (Option Bool)) : machine.Cfg where
  l := phase
  var := initial
  stk := storage (fun key => match key with | false => word | true => pending) input header accumulator result

def sourceConfig (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool))
    (state : counter.Cfg) : machine.Cfg where
  l := some (state.l.elim (.readFlag side) (Phase.run side))
  var := (state.var, none, none, none)
  stk := storage state.stk input [] accumulator result

theorem storage_update (contents : ∀ key, List (counter.Γ key)) (input : List (Option Bool))
    (header : List Unit) (accumulator result : List (Option Bool)) (key : Bool) (word : List (counter.Γ key)) :
    storage (Function.update contents key word) input header accumulator result =
      Function.update (storage contents input header accumulator result) (.inl key) word := by
  funext target
  cases target with
  | inl target =>
      by_cases same : target = key
      · subst target; simp [storage, Function.update]
      · simp [storage, Function.update, same]
  | inr target => cases target <;> simp [storage, Function.update]

theorem source_step (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool))
    (before after : counter.Cfg) (advanced : counter.step before = some after) :
    machine.step (sourceConfig side input accumulator result before) =
      some (sourceConfig side input accumulator result after) := by
  exact StackMachineRegisters.step_embedStatement (Alphabet := counter.Γ) (TargetAlphabet := Alphabet)
    Sum.inl (Phase.run side) (.readFlag side)
    (fun state : Control => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
    (fun registers => (registers, none, none, none))
    (fun contents => storage contents input [] accumulator result)
    (fun _ => rfl) (fun _ _ => rfl)
    (by intro contents key; change contents key = (contents key).map id; simp)
    (by
      intro contents key word
      change storage (Function.update contents key word) input [] accumulator result =
        Function.update (storage contents input [] accumulator result) (.inl key) (word.map id)
      simpa only [List.map_id] using storage_update contents input [] accumulator result key word)
    counter.m program before after (fun _ _ => rfl) advanced

def source_execution (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool))
    {before after : counter.Cfg} {time : Nat} (executed : EvalsToInTime counter.step before (some after) time) :
    EvalsToInTime machine.step (sourceConfig side input accumulator result before)
      (some (sourceConfig side input accumulator result after)) time :=
  StackMachineComposition.lift_execution counter.step machine.step (sourceConfig side input accumulator result)
    (source_step side input accumulator result) executed

theorem source_initial (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) (word : List Bool) :
    sourceConfig side input accumulator result (initList counter word) = config (some (.run side false)) input [] word [] accumulator result := by
  simp only [sourceConfig, config, initial, initList, counter, BinaryCountdownMachine.machine]
  congr 1
  funext key
  cases key with
  | inl key => cases key <;> simp [storage]
  | inr key => cases key <;> simp [storage]

theorem source_halted (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) (word : List Bool) :
    sourceConfig side input accumulator result (haltList counter word) = config (some (.readFlag side)) input [] word [] accumulator result := by
  simp only [sourceConfig, config, initial, haltList, counter, BinaryCountdownMachine.machine]
  congr 1
  funext key
  cases key with
  | inl key => cases key <;> simp [storage]
  | inr key => cases key <;> simp [storage]

/-- Repeated debits execute in the same counter arena; no whole-counter copy
is introduced between payload bits. -/
def counter_run (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) (word : List Bool) :
    EvalsToInTime machine.step (config (some (.run side false)) input [] word [] accumulator result)
      (some (config (some (.readFlag side)) input [] (BinaryCountdownMachine.resume 0 word) [] accumulator result))
      (BinaryCountdownMachine.clock word) := by
  have ran := source_execution side input accumulator result (BinaryCountdownMachine.outputs word)
  simpa only [source_initial, source_halted] using ran

local macro "parser_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, storage, initial, following, TM2.step, TM2.stepAux, haltList]
  all_goals funext key
  all_goals cases key with
    | inl key => cases key <;> simp [storage, Function.update]
    | inr key => cases key <;> simp [storage, Function.update]))

theorem header_true (side : Bool) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) :
    machine.step (config (some (.header side)) (some true :: input) header [] [] accumulator result) =
      some (config (some (.header side)) input (() :: header) [] [] accumulator result) := by parser_step

theorem header_false (side : Bool) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) :
    machine.step (config (some (.header side)) (some false :: input) header [] [] accumulator result) =
      some (config (some (.lengthFirst side)) input header [] [] accumulator result) := by parser_step

def CanonicalHeader (bits : List Bool) : Prop := bits = [] ∨ ∃ rest, bits = true :: rest

theorem header_counter_value (length : Nat) : value (binaryBits length).reverse = length := by
  change ofBinaryBits (binaryBits length) = length
  exact ofBinaryBits_binaryBits length

theorem digit_bits_roundtrip (bits : List Bool) :
    (bits.map BinaryStackArithmetic.bitValue).map (fun digit => decide (digit = 1)) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [BinaryStackArithmetic.bitValue, ih]

theorem canonical_header_inverse (bits : List Bool) (canonical : CanonicalHeader bits) :
    binaryBits (value bits.reverse) = bits := by
  rcases canonical with rfl | ⟨rest, rfl⟩
  · simp [value, binaryBits]
  · let digits := (true :: rest).reverse.map BinaryStackArithmetic.bitValue
    have bounded : ∀ digit ∈ digits, digit < 2 := by
      intro digit member
      obtain ⟨bit, _member, rfl⟩ := List.mem_map.mp member
      cases bit <;> decide
    have high : ∀ nonempty : digits ≠ [], digits.getLast nonempty ≠ 0 := by
      intro nonempty
      simp [digits, List.reverse_cons, BinaryStackArithmetic.bitValue]
    have exactDigits := Nat.digits_ofDigits 2 (by decide) digits bounded high
    change binaryBits (Nat.ofDigits 2 digits) = true :: rest
    simp only [binaryBits, exactDigits, digits, ← List.map_reverse, List.reverse_reverse]
    exact digit_bits_roundtrip _

theorem canonical_binaryBits (length : Nat) : CanonicalHeader (binaryBits length) := by
  by_cases zero : length = 0
  · subst length
    exact Or.inl (by simp [binaryBits])
  · have nonempty : Nat.digits 2 length ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr zero
    have high := Nat.getLast_digit_ne_zero 2 zero
    have bounded := Nat.digits_lt_base (by decide : 1 < 2) (List.getLast_mem nonempty)
    have lastOne : (Nat.digits 2 length).getLast nonempty = 1 := by omega
    have head : (binaryBits length).head? = some true := by
      simp only [binaryBits, List.head?_map, List.head?_reverse,
        List.getLast?_eq_getLast_of_ne_nil nonempty, lastOne]
      rfl
    cases selected : binaryBits length with
    | nil => simp [selected] at head
    | cons bit rest =>
        have bitTrue : bit = true := by simpa only [selected, List.head?_cons, Option.some.injEq] using head
        exact Or.inr ⟨rest, by simp [bitTrue]⟩

theorem count_header_agrees : Mettapedia.Algorithms.Compression.Framing.writeNat 2 = countHeader := by decide_cbv

theorem prefix_read (index : Fin 7) (input : List (Option Bool)) :
    machine.step (config (some (.prefix ⟨index.val, by omega⟩)) (some (prefixBit index) :: input) [] [] [] [] []) =
      some (config (some (.prefix ⟨index.val + 1, by omega⟩)) input [] [] [] [] []) := by
  have active : index.val < 7 := index.isLt
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, active, advance]
  funext key
  cases key with
  | inl key => cases key <;> simp [storage, Function.update]
  | inr key => cases key <;> simp [storage, Function.update]

theorem prefix_end (input : List (Option Bool)) :
    machine.step (config (some (.prefix 7)) input [] [] [] [] []) =
      some (config (some (.header false)) input [] [] [] [] []) := by
  simp [FinTM2.step, machine, program, config, initial, TM2.step, TM2.stepAux]

theorem length_first_empty (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.lengthFirst side)) input [] [] [] accumulator result) =
      some (config (some (.run side false)) input [] [] [] accumulator result) := by parser_step

theorem length_first_true (side : Bool) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) :
    machine.step (config (some (.lengthFirst side)) (some true :: input) (() :: header) [] [] accumulator result) =
      some (config (some (.length side)) input header [true] [] accumulator result) := by parser_step

theorem length_read (side : Bool) (bit : Bool) (input : List (Option Bool)) (header : List Unit) (word : List Bool)
    (accumulator result : List (Option Bool)) :
    machine.step (config (some (.length side)) (some bit :: input) (() :: header) word [] accumulator result) =
      some (config (some (.length side)) input header (bit :: word) [] accumulator result) := by parser_step

theorem length_end (side : Bool) (input : List (Option Bool)) (word : List Bool) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.length side)) input [] word [] accumulator result) =
      some (config (some (.run side false)) input [] word [] accumulator result) := by parser_step

theorem payload_read (side bit : Bool) (input : List (Option Bool)) (word : List Bool) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.readFlag side)) (some bit :: input) [] (true :: word) [] accumulator result) =
      some (config (some (.run side false)) input [] word [] (some bit :: accumulator) result) := by parser_step

theorem flag_zero (side : Bool) (input : List (Option Bool)) (word : List Bool) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.readFlag side)) input [] (false :: word) [] accumulator result) =
      some (config (some (.clearCounter side)) input [] word [] accumulator result) := by parser_step

theorem clear_read (side bit : Bool) (input : List (Option Bool)) (word : List Bool) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.clearCounter side)) input [] (bit :: word) [] accumulator result) =
      some (config (some (.clearCounter side)) input [] word [] accumulator result) := by parser_step

theorem clear_end (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.clearCounter side)) input [] [] [] accumulator result) =
      some (config (some (.finishField side)) input [] [] [] accumulator result) := by parser_step

theorem finish_field (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some (.finishField side)) input [] [] [] accumulator result) =
      some (config (some (following side)) input [] [] [] (none :: accumulator) result) := by parser_step

theorem candidate_end (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some .candidateEnd) (none :: input) [] [] [] accumulator result) =
      some (config (some .original) input [] [] [] accumulator result) := by parser_step

theorem original_read (bit : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some .original) (some bit :: input) [] [] [] accumulator result) =
      some (config (some .original) input [] [] [] (some bit :: accumulator) result) := by parser_step

theorem original_delimiter (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    machine.step (config (some .original) (none :: input) [] [] [] accumulator result) =
      some (config (some .originalEnd) input [] [] [] accumulator result) := by parser_step

theorem original_end (accumulator result : List (Option Bool)) :
    machine.step (config (some .originalEnd) [] [] [] [] accumulator result) =
      some (config (some .reverse) [] [] [] [] (none :: accumulator) result) := by parser_step

theorem reverse_read (cell : Option Bool) (accumulator result : List (Option Bool)) :
    machine.step (config (some .reverse) [] [] [] [] (cell :: accumulator) result) =
      some (config (some .reverse) [] [] [] [] accumulator (cell :: result)) := by parser_step

theorem reverse_end (result : List (Option Bool)) :
    machine.step (config (some .reverse) [] [] [] [] [] result) = some (haltList machine result) := by parser_step

theorem replicate_marker_push (count : Nat) (header : List Unit) :
    List.replicate count () ++ () :: header = List.replicate (count + 1) () ++ header := by
  simp [List.replicate_succ', List.append_assoc]

def header_run (side : Bool) (count : Nat) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some (.header side)) (List.replicate count (some true) ++ some false :: input) header [] [] accumulator result)
      (some (config (some (.lengthFirst side)) input (List.replicate count () ++ header) [] [] accumulator result))
      (count + 1) := by
  induction count generalizing header with
  | zero => simpa using StackMachineComposition.oneStep (header_false side input header accumulator result)
  | succ count ih =>
      have first := StackMachineComposition.oneStep
        (header_true side (List.replicate count (some true) ++ some false :: input) header accumulator result)
      have finish := ih (() :: header)
      rw [replicate_marker_push] at finish
      simpa only [List.replicate_succ, List.cons_append, Nat.succ_eq_add_one] using
        EvalsToInTime.trans _ 1 (count + 1) _ _ _ first finish

def length_run (side : Bool) (bits word : List Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some (.length side)) (bits.map some ++ input) (List.replicate bits.length ()) word [] accumulator result)
      (some (config (some (.run side false)) input [] (bits.reverse ++ word) [] accumulator result)) (bits.length + 1) := by
  induction bits generalizing word with
  | nil => simpa using StackMachineComposition.oneStep (length_end side input word accumulator result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep
        (length_read side bit (rest.map some ++ input) (List.replicate rest.length ()) word accumulator result)
      have finish := ih (bit :: word)
      simpa [List.reverse_cons, List.append_assoc, List.replicate_succ] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def length_first_run (side : Bool) (bits : List Bool) (canonical : CanonicalHeader bits)
    (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some (.lengthFirst side)) (bits.map some ++ input) (List.replicate bits.length ()) [] [] accumulator result)
      (some (config (some (.run side false)) input [] bits.reverse [] accumulator result)) (bits.length + 1) := by
  cases bits with
  | nil => simpa using StackMachineComposition.oneStep (length_first_empty side input accumulator result)
  | cons bit rest =>
      cases bit with
      | false =>
          exact False.elim (by rcases canonical with impossible | ⟨tail, impossible⟩ <;> cases impossible)
      | true =>
          have first := StackMachineComposition.oneStep
            (length_first_true side (rest.map some ++ input) (List.replicate rest.length ()) accumulator result)
          have finish := length_run side rest [true] input accumulator result
          simpa [List.reverse_cons, List.replicate_succ] using
            EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def clear_run (side : Bool) (word : List Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some (.clearCounter side)) input [] word [] accumulator result)
      (some (config (some (.finishField side)) input [] [] [] accumulator result)) (word.length + 1) := by
  induction word with
  | nil => simpa using StackMachineComposition.oneStep (clear_end side input accumulator result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (clear_read side bit input rest accumulator result)
      simpa using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first ih

def original_run (word : List Bool) (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .original) (word.map some ++ [none]) [] [] [] accumulator result)
      (some (config (some .originalEnd) [] [] [] [] (word.reverse.map some ++ accumulator) result)) (word.length + 1) := by
  induction word generalizing accumulator with
  | nil => simpa using StackMachineComposition.oneStep (original_delimiter [] accumulator result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (original_read bit (rest.map some ++ [none]) accumulator result)
      have finish := ih (some bit :: accumulator)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def reverse_run (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .reverse) [] [] [] [] accumulator result)
      (some (haltList machine (accumulator.reverse ++ result))) (accumulator.length + 1) := by
  induction accumulator generalizing result with
  | nil => simpa using StackMachineComposition.oneStep (reverse_end result)
  | cons cell rest ih =>
      have first := StackMachineComposition.oneStep (reverse_read cell rest result)
      have finish := ih (cell :: result)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

/-- The potential pays for the actual counter execution and the single
combined flag/payload transition at every copied bit. -/
def body_run (side : Bool) (payload word : List Bool) (fits : value word = payload.length)
    (input : List (Option Bool)) (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some (.run side false)) (payload.map some ++ input) [] word [] accumulator result)
      (some (config (some (.finishField side)) input [] [] [] (payload.reverse.map some ++ accumulator) result))
      (5 * payload.length + 2 * BinaryCountdownMachine.zeros word + 3 * word.length + 4) := by
  induction payload generalizing word accumulator with
  | nil =>
      have zero : BinaryCountdownMachine.decrement word = none :=
        (BinaryCountdownMachine.decrement_none_iff word).mpr fits
      have called := counter_run side input accumulator result word
      simp only [BinaryCountdownMachine.resume, zero, List.replicate_zero, List.nil_append] at called
      have flagged := StackMachineComposition.oneStep (flag_zero side input word accumulator result)
      have cleared := clear_run side word input accumulator result
      have first := EvalsToInTime.trans _ _ _ _ _ _ called flagged
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first cleared
      have maximum := BinaryCountdownMachine.clock_le_length word
      have bounded := WordEqualityMachine.within joined
        (show _ ≤ 5 * ([] : List Bool).length + 2 * BinaryCountdownMachine.zeros word + 3 * word.length + 4 from by
          simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
          omega)
      simpa using bounded
  | cons bit rest ih =>
      have positive : value word ≠ 0 := by simp only [List.length_cons] at fits; omega
      cases changed : BinaryCountdownMachine.decrement word with
      | none => exact False.elim (positive ((BinaryCountdownMachine.decrement_none_iff word).mp changed))
      | some after =>
          have nextValue := BinaryCountdownMachine.decrement_value changed
          have nextLength := BinaryCountdownMachine.decrement_length changed
          have remaining : value after = rest.length := by simp only [List.length_cons] at fits; omega
          have called := counter_run side (some bit :: (rest.map some ++ input)) accumulator result word
          simp only [BinaryCountdownMachine.resume, changed, List.replicate_zero, List.nil_append] at called
          have copied := StackMachineComposition.oneStep (payload_read side bit (rest.map some ++ input) after accumulator result)
          have finish := ih after remaining (some bit :: accumulator)
          have first := EvalsToInTime.trans _ _ _ _ _ _ called copied
          have joined := EvalsToInTime.trans _ _ _ _ _ _ first finish
          have amortized := BinaryCountdownMachine.debit_amortized changed
          have bounded := WordEqualityMachine.within joined
            (show _ ≤ 5 * (bit :: rest).length + 2 * BinaryCountdownMachine.zeros word + 3 * word.length + 4 from by
              simp only [List.length_cons]
              omega)
          simpa [List.reverse_cons, List.map_append, List.append_assoc] using bounded

noncomputable def field_run (side : Bool) (payload : List Bool) (input : List (Option Bool))
    (accumulator result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some (.header side)) ((e2encode payload).map some ++ input) [] [] [] accumulator result)
      (some (config (some (following side)) input [] [] [] (none :: (payload.reverse.map some ++ accumulator)) result))
      (5 * payload.length + 7 * (binaryBits payload.length).length + 7) := by
  let bits := binaryBits payload.length
  have h := header_run side bits.length (bits.map some ++ payload.map some ++ input) [] accumulator result
  simp only [List.append_nil] at h
  have l := length_first_run side bits (canonical_binaryBits payload.length) (payload.map some ++ input) accumulator result
  have b := body_run side payload bits.reverse (header_counter_value payload.length) input accumulator result
  have f := StackMachineComposition.oneStep (finish_field side input (payload.reverse.map some ++ accumulator) result)
  simp only [List.append_assoc] at h l b f
  have hl := EvalsToInTime.trans _ _ _ _ _ _ h l
  have hlb := EvalsToInTime.trans _ _ _ _ _ _ hl b
  have joined := EvalsToInTime.trans _ _ _ _ _ _ hlb f
  have potential := BinaryCountdownMachine.zeros_le_length bits.reverse
  have bounded := WordEqualityMachine.within joined
    (show _ ≤ 5 * payload.length + 7 * (binaryBits payload.length).length + 7 from by
      simp only [bits, List.length_reverse] at potential ⊢
      omega)
  simpa [e2encode, e1encode, bits, List.map_append, List.map_replicate, List.append_assoc] using bounded

def prefix_run (input : List (Option Bool)) :
    EvalsToInTime machine.step (config (some (.prefix 0)) (countHeader.map some ++ input) [] [] [] [] [])
      (some (config (some (.header false)) input [] [] [] [] [])) 8 := by
  have a := StackMachineComposition.oneStep (prefix_read 0 ((countHeader.drop 1).map some ++ input))
  have b := StackMachineComposition.oneStep (prefix_read 1 ((countHeader.drop 2).map some ++ input))
  have c := StackMachineComposition.oneStep (prefix_read 2 ((countHeader.drop 3).map some ++ input))
  have d := StackMachineComposition.oneStep (prefix_read 3 ((countHeader.drop 4).map some ++ input))
  have e := StackMachineComposition.oneStep (prefix_read 4 ((countHeader.drop 5).map some ++ input))
  have f := StackMachineComposition.oneStep (prefix_read 5 ((countHeader.drop 6).map some ++ input))
  have g := StackMachineComposition.oneStep (prefix_read 6 input)
  have h := StackMachineComposition.oneStep (prefix_end input)
  dsimp only [countHeader, prefixBit] at a b c d e f g
  have ab := EvalsToInTime.trans _ _ _ _ _ _ a b
  have abc := EvalsToInTime.trans _ _ _ _ _ _ ab c
  have abcd := EvalsToInTime.trans _ _ _ _ _ _ abc d
  have abcde := EvalsToInTime.trans _ _ _ _ _ _ abcd e
  have abcdef := EvalsToInTime.trans _ _ _ _ _ _ abcde f
  have abcdefg := EvalsToInTime.trans _ _ _ _ _ _ abcdef g
  have joined := EvalsToInTime.trans _ _ _ _ _ _ abcdefg h
  simpa [countHeader] using joined

def job (descriptive feature original : List Bool) : List (Option Bool) :=
  Indexed.frame [FeatureTheory.DyadicSearch.pairCode descriptive feature, original]

theorem job_decompose (descriptive feature original : List Bool) :
    job descriptive feature original = countHeader.map some ++ (e2encode descriptive).map some ++
      (e2encode feature).map some ++ none :: (original.map some ++ [none]) := by
  simp [job, Indexed.frame, FeatureTheory.DyadicSearch.pairCode,
    Mettapedia.Algorithms.Compression.Framing.encode, Mettapedia.Algorithms.Compression.Framing.writeFields,
    ← count_header_agrees, List.map_append, List.append_assoc]

theorem job_length (descriptive feature original : List Bool) :
    (job descriptive feature original).length = descriptive.length + feature.length + original.length +
      2 * (binaryBits descriptive.length).length + 2 * (binaryBits feature.length).length + 11 := by
  rw [job_decompose]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, e2encode_length]
  simp only [countHeader, List.length_cons, List.length_nil]
  omega

theorem initial_agrees (input : List (Option Bool)) :
    initList machine input = config (some (.prefix 0)) input [] [] [] [] [] := by
  simp only [initList, machine, config, initial]
  congr 1
  funext key
  cases key with
  | inl key => cases key <;> simp [storage]
  | inr key => cases key <;> simp [storage]

/-- The original pair-code count and both E2 headers are physically consumed.
The complete task is reconstructed with all three boundaries and occurrences. -/
noncomputable def outputs (descriptive feature original : List Bool) :
    TM2OutputsInTime machine (job descriptive feature original)
      (some (Indexed.frame [descriptive, feature, original]))
      (8 * ((job descriptive feature original).length + 1)) := by
  let tail := none :: (original.map some ++ [none])
  let afterFirst := none :: descriptive.reverse.map some
  let afterSecond := none :: (feature.reverse.map some ++ afterFirst)
  let afterOriginal := none :: (original.reverse.map some ++ afterSecond)
  have a := prefix_run ((e2encode descriptive).map some ++ (e2encode feature).map some ++ tail)
  have b := field_run false descriptive ((e2encode feature).map some ++ tail) [] []
  have c := field_run true feature tail afterFirst []
  have d := StackMachineComposition.oneStep (candidate_end (original.map some ++ [none]) afterSecond [])
  have e := original_run original afterSecond []
  have f := StackMachineComposition.oneStep (original_end (original.reverse.map some ++ afterSecond) [])
  have g := reverse_run afterOriginal []
  simp only [following, Bool.false_eq_true, if_false, if_true, List.append_nil] at b c
  simp only [List.append_assoc] at a
  have ab := EvalsToInTime.trans _ _ _ _ _ _ a b
  have abc := EvalsToInTime.trans _ _ _ _ _ _ ab c
  have abcd := EvalsToInTime.trans _ _ _ _ _ _ abc d
  have abcde := EvalsToInTime.trans _ _ _ _ _ _ abcd e
  have abcdef := EvalsToInTime.trans _ _ _ _ _ _ abcde f
  have joined := EvalsToInTime.trans _ _ _ _ _ _ abcdef g
  have bounded := WordEqualityMachine.within joined
    (show _ ≤ 8 * ((job descriptive feature original).length + 1) from by
      simp only [afterOriginal, afterSecond, afterFirst, List.length_cons, List.length_append,
        List.length_map, List.length_reverse, job_length]
      omega)
  have startSame : config (some (.prefix 0))
      (countHeader.map some ++ ((e2encode descriptive).map some ++ ((e2encode feature).map some ++ tail))) [] [] [] [] [] =
      initList machine (job descriptive feature original) := by
    rw [initial_agrees, job_decompose]
    simp only [tail, List.append_assoc]
  have outputSame : afterOriginal.reverse ++ [] = Indexed.frame [descriptive, feature, original] := by
    simp [afterOriginal, afterSecond, afterFirst, Indexed.frame,
      List.reverse_append, List.reverse_cons, List.map_reverse, List.append_assoc]
  have started := Eq.mp (congrArg (fun state : machine.Cfg => EvalsToInTime machine.step state
    (some (haltList machine (afterOriginal.reverse ++ []))) (8 * ((job descriptive feature original).length + 1))) startSame) bounded
  exact Eq.mp (congrArg (fun output : List (Option Bool) => TM2OutputsInTime machine
    (job descriptive feature original) (some output) (8 * ((job descriptive feature original).length + 1))) outputSame) started

def terminal_tail {before middle final : machine.Cfg} {prefixTime time : Nat}
    (prefixRun : EvalsToInTime machine.step before (some middle) prefixTime)
    (executed : EvalsToInTime machine.step before (some final) time) (stopped : final.l = none) :
    EvalsToInTime machine.step middle (some final) time :=
  StackMachineContextCall.terminal_tail machine.step prefixRun executed
    ((StackMachineComposition.source_step_none_iff machine final).mpr stopped)

theorem reject_step (state : machine.Cfg) (rejected : state.l = some .reject) : machine.step state = some state := by
  cases state with
  | mk label registers contents =>
      dsimp only at rejected
      subst label
      rfl

theorem rejected_never_halts (before final : machine.Cfg) (rejected : before.l = some .reject) {time : Nat}
    (executed : EvalsToInTime machine.step before (some final) time) (stopped : final.l = none) : False := by
  have fixed : (flip bind machine.step) (some before) = some before := by
    simpa only [flip, Option.bind_eq_bind, Option.bind_some] using reject_step before rejected
  have repeated := Function.iterate_fixed fixed executed.steps
  have same := Option.some.inj (repeated.symm.trans executed.evals_in_steps)
  have label := congrArg (fun state : machine.Cfg => state.l) same
  rw [rejected, stopped] at label
  cases label

theorem rejects_if_next_label (before final : machine.Cfg) {time : Nat}
    (executed : EvalsToInTime machine.step before (some final) time) (stopped : final.l = none)
    (rejected : (machine.step before).map (fun state => state.l) = some (some .reject)) : False := by
  obtain ⟨after, advanced, label⟩ := Option.map_eq_some_iff.mp rejected
  exact rejected_never_halts after final label (terminal_tail (StackMachineComposition.oneStep advanced) executed stopped) stopped

local macro "reject_label" : tactic => `(tactic|
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux])

theorem header_completed (side : Bool) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.header side)) input header [] [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ count rest, input = List.replicate count (some true) ++ some false :: rest ∧
      Nonempty (EvalsToInTime machine.step
        (config (some (.lengthFirst side)) rest (List.replicate count () ++ header) [] [] accumulator result) (some final) time) := by
  cases input with
  | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
  | cons cell input =>
      cases cell with
      | none => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
      | some bit =>
          cases bit with
          | false =>
              have tail := terminal_tail (StackMachineComposition.oneStep (header_false side input header accumulator result)) executed stopped
              exact ⟨0, input, rfl, ⟨tail⟩⟩
          | true =>
              have tail := terminal_tail (StackMachineComposition.oneStep (header_true side input header accumulator result)) executed stopped
              obtain ⟨count, rest, inputSame, ⟨run⟩⟩ := header_completed side input (() :: header) accumulator result tail stopped
              rw [replicate_marker_push] at run
              refine ⟨count + 1, rest, ?_, ⟨run⟩⟩
              simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons (some true)) inputSame
termination_by input.length

theorem length_completed (side : Bool) (input : List (Option Bool)) (header : List Unit) (word : List Bool)
    (accumulator result : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.length side)) input header word [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ (bits : List Bool) (rest : List (Option Bool)), bits.length = header.length ∧ input = bits.map some ++ rest ∧
      Nonempty (EvalsToInTime machine.step
        (config (some (.run side false)) rest [] (bits.reverse ++ word) [] accumulator result) (some final) time) := by
  cases header with
  | nil =>
      have tail := terminal_tail (StackMachineComposition.oneStep (length_end side input word accumulator result)) executed stopped
      exact ⟨[], input, rfl, rfl, ⟨by simpa using tail⟩⟩
  | cons marker header =>
      cases marker
      cases input with
      | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
      | cons cell input =>
          cases cell with
          | none => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
          | some bit =>
              have tail := terminal_tail
                (StackMachineComposition.oneStep (length_read side bit input header word accumulator result)) executed stopped
              obtain ⟨bits, rest, bitsLength, inputSame, ⟨run⟩⟩ :=
                length_completed side input header (bit :: word) accumulator result tail stopped
              refine ⟨bit :: bits, rest, by simpa using congrArg Nat.succ bitsLength, ?_, ?_⟩
              · simpa only [List.map_cons, List.cons_append] using congrArg (List.cons (some bit)) inputSame
              · exact ⟨by simpa [List.reverse_cons, List.append_assoc] using run⟩
termination_by header.length

theorem length_first_completed (side : Bool) (input : List (Option Bool)) (header : List Unit)
    (accumulator result : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.lengthFirst side)) input header [] [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ bits rest, CanonicalHeader bits ∧ bits.length = header.length ∧ input = bits.map some ++ rest ∧
      Nonempty (EvalsToInTime machine.step
        (config (some (.run side false)) rest [] bits.reverse [] accumulator result) (some final) time) := by
  cases header with
  | nil =>
      have tail := terminal_tail (StackMachineComposition.oneStep (length_first_empty side input accumulator result)) executed stopped
      exact ⟨[], input, Or.inl rfl, rfl, rfl, ⟨tail⟩⟩
  | cons marker header =>
      cases marker
      cases input with
      | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
      | cons cell input =>
          cases cell with
          | none => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
          | some bit =>
              cases bit with
              | false => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
              | true =>
                  have tail := terminal_tail
                    (StackMachineComposition.oneStep (length_first_true side input header accumulator result)) executed stopped
                  obtain ⟨bits, rest, bitsLength, inputSame, ⟨run⟩⟩ :=
                    length_completed side input header [true] accumulator result tail stopped
                  refine ⟨true :: bits, rest, Or.inr ⟨bits, rfl⟩, by simpa using congrArg Nat.succ bitsLength, ?_, ?_⟩
                  · simpa only [List.map_cons, List.cons_append] using congrArg (List.cons (some true)) inputSame
                  · exact ⟨by simpa [List.reverse_cons] using run⟩

theorem body_completed (side : Bool) (input : List (Option Bool)) (word : List Bool)
    (accumulator result : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step
      (config (some (.run side false)) input [] word [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ (payload : List Bool) (rest : List (Option Bool)), input = payload.map some ++ rest ∧ payload.length = value word ∧
      Nonempty (EvalsToInTime machine.step
        (config (some (.finishField side)) rest [] [] [] (payload.reverse.map some ++ accumulator) result) (some final) time) := by
  have called := counter_run side input accumulator result word
  cases changed : BinaryCountdownMachine.decrement word with
  | none =>
      simp only [BinaryCountdownMachine.resume, changed, List.replicate_zero, List.nil_append] at called
      have flag := StackMachineComposition.oneStep (flag_zero side input word accumulator result)
      have cleared := clear_run side word input accumulator result
      have first := EvalsToInTime.trans _ _ _ _ _ _ called flag
      have prefixRun := EvalsToInTime.trans _ _ _ _ _ _ first cleared
      refine ⟨[], input, rfl, ?_, ?_⟩
      · exact (BinaryCountdownMachine.decrement_none_iff word).mp changed |>.symm
      · exact ⟨by simpa using terminal_tail prefixRun executed stopped⟩
  | some after =>
      simp only [BinaryCountdownMachine.resume, changed, List.replicate_zero, List.nil_append] at called
      have afterCall := terminal_tail called executed stopped
      cases input with
      | nil => exact False.elim (rejects_if_next_label _ _ afterCall stopped (by reject_label))
      | cons cell input =>
          cases cell with
          | none => exact False.elim (rejects_if_next_label _ _ afterCall stopped (by reject_label))
          | some bit =>
              have copied := StackMachineComposition.oneStep (payload_read side bit input after accumulator result)
              have tail := terminal_tail copied afterCall stopped
              obtain ⟨payload, rest, inputSame, payloadLength, ⟨run⟩⟩ :=
                body_completed side input after (some bit :: accumulator) result tail stopped
              refine ⟨bit :: payload, rest, ?_, ?_, ?_⟩
              · simpa only [List.map_cons, List.cons_append] using congrArg (List.cons (some bit)) inputSame
              · have debit := BinaryCountdownMachine.decrement_value changed
                simp only [List.length_cons]
                omega
              · exact ⟨by simpa [List.reverse_cons, List.map_append, List.append_assoc] using run⟩
termination_by input.length

/-- A completed field has the exact original E2 encoding, not merely a
numerically equal noncanonical length header. -/
theorem field_completed (side : Bool) (input : List (Option Bool)) (accumulator result : List (Option Bool))
    {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.header side)) input [] [] [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ (payload : List Bool) (rest : List (Option Bool)), input = (e2encode payload).map some ++ rest ∧
      Nonempty (EvalsToInTime machine.step
        (config (some (following side)) rest [] [] [] (none :: (payload.reverse.map some ++ accumulator)) result) (some final) time) := by
  obtain ⟨count, lengthInput, inputHeader, ⟨headerRun⟩⟩ := header_completed side input [] accumulator result executed stopped
  simp only [List.append_nil] at headerRun
  obtain ⟨bits, bodyInput, canonical, bitsLength, inputLength, ⟨lengthRun⟩⟩ :=
    length_first_completed side lengthInput (List.replicate count ()) accumulator result headerRun stopped
  obtain ⟨payload, rest, inputBody, payloadLength, ⟨bodyRun⟩⟩ :=
    body_completed side bodyInput bits.reverse accumulator result lengthRun stopped
  have bitsSame : binaryBits payload.length = bits := by
    rw [payloadLength]
    exact canonical_header_inverse bits canonical
  have countSame : count = bits.length := by simpa only [List.length_replicate] using bitsLength.symm
  have parsed : input = (e2encode payload).map some ++ rest := by
    rw [inputHeader, inputLength, inputBody, countSame, ← bitsSame]
    simp [e2encode, e1encode, List.map_append, List.map_replicate, List.append_assoc]
  have finished := terminal_tail (StackMachineComposition.oneStep
    (finish_field side rest (payload.reverse.map some ++ accumulator) result)) bodyRun stopped
  exact ⟨payload, rest, parsed, ⟨finished⟩⟩

theorem prefix_read_completed (index : Fin 7) (input : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.prefix ⟨index.val, by omega⟩)) input [] [] [] [] []) (some final) time)
    (stopped : final.l = none) :
    ∃ rest, input = some (prefixBit index) :: rest ∧ Nonempty (EvalsToInTime machine.step
      (config (some (.prefix ⟨index.val + 1, by omega⟩)) rest [] [] [] [] []) (some final) time) := by
  have active : index.val < 7 := index.isLt
  cases input with
  | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by
      simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, active]))
  | cons cell input =>
      cases cell with
      | none => exact False.elim (rejects_if_next_label _ _ executed stopped (by
          simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, active]))
      | some bit =>
          by_cases same : bit = prefixBit index
          · subst bit
            exact ⟨input, rfl, ⟨terminal_tail (StackMachineComposition.oneStep (prefix_read index input)) executed stopped⟩⟩
          · exact False.elim (rejects_if_next_label _ _ executed stopped (by
              simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, active, same]))

theorem prefix_completed (input : List (Option Bool)) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some (.prefix 0)) input [] [] [] [] []) (some final) time)
    (stopped : final.l = none) :
    ∃ rest, input = countHeader.map some ++ rest ∧ Nonempty (EvalsToInTime machine.step
      (config (some (.header false)) rest [] [] [] [] []) (some final) time) := by
  obtain ⟨one, first, ⟨a⟩⟩ := prefix_read_completed 0 input executed stopped
  obtain ⟨two, second, ⟨b⟩⟩ := prefix_read_completed 1 one a stopped
  obtain ⟨three, third, ⟨c⟩⟩ := prefix_read_completed 2 two b stopped
  obtain ⟨four, fourth, ⟨d⟩⟩ := prefix_read_completed 3 three c stopped
  obtain ⟨five, fifth, ⟨e⟩⟩ := prefix_read_completed 4 four d stopped
  obtain ⟨six, sixth, ⟨f⟩⟩ := prefix_read_completed 5 five e stopped
  obtain ⟨rest, seventh, ⟨g⟩⟩ := prefix_read_completed 6 six f stopped
  refine ⟨rest, ?_, ⟨terminal_tail (StackMachineComposition.oneStep (prefix_end rest)) g stopped⟩⟩
  rw [first, second, third, fourth, fifth, sixth, seventh]
  rfl

theorem candidate_end_completed (input : List (Option Bool)) (accumulator result : List (Option Bool))
    {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some .candidateEnd) input [] [] [] accumulator result) (some final) time)
    (stopped : final.l = none) :
    ∃ rest, input = none :: rest ∧ Nonempty (EvalsToInTime machine.step
      (config (some .original) rest [] [] [] accumulator result) (some final) time) := by
  cases input with
  | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
  | cons cell input =>
      cases cell with
      | none => exact ⟨input, rfl, ⟨terminal_tail (StackMachineComposition.oneStep (candidate_end input accumulator result)) executed stopped⟩⟩
      | some bit => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))

theorem original_end_completed (input : List (Option Bool)) (accumulator result : List (Option Bool))
    {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some .originalEnd) input [] [] [] accumulator result) (some final) time)
    (stopped : final.l = none) : input = [] := by
  cases input with
  | nil => rfl
  | cons cell input => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))

theorem original_completed (input : List (Option Bool)) (accumulator result : List (Option Bool))
    {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (config (some .original) input [] [] [] accumulator result) (some final) time)
    (stopped : final.l = none) : ∃ word : List Bool, input = word.map some ++ [none] := by
  cases input with
  | nil => exact False.elim (rejects_if_next_label _ _ executed stopped (by reject_label))
  | cons cell input =>
      cases cell with
      | none =>
          have tail := terminal_tail (StackMachineComposition.oneStep (original_delimiter input accumulator result)) executed stopped
          have empty := original_end_completed input accumulator result tail stopped
          subst input
          exact ⟨[], rfl⟩
      | some bit =>
          have tail := terminal_tail (StackMachineComposition.oneStep (original_read bit input accumulator result)) executed stopped
          obtain ⟨word, same⟩ := original_completed input (some bit :: accumulator) result tail stopped
          exact ⟨bit :: word, by simpa only [List.map_cons, List.cons_append] using congrArg (List.cons (some bit)) same⟩
termination_by input.length

/-- Every terminal parser trace has consumed a complete canonical job. This
includes refusal of missing boundaries, noncanonical headers and extensions. -/
theorem terminal_job {input : List (Option Bool)} {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (initList machine input) (some final) time) (stopped : final.l = none) :
    ∃ descriptive feature original, input = job descriptive feature original := by
  have started := Eq.mp (congrArg (fun state : machine.Cfg => EvalsToInTime machine.step state (some final) time)
    (initial_agrees input)) executed
  obtain ⟨fieldsInput, prefixSame, ⟨prefixRun⟩⟩ := prefix_completed input started stopped
  obtain ⟨descriptive, featureInput, firstSame, ⟨firstRun⟩⟩ := field_completed false fieldsInput [] [] prefixRun stopped
  simp only [following, Bool.false_eq_true, if_false, List.append_nil] at firstRun
  obtain ⟨feature, endInput, secondSame, ⟨secondRun⟩⟩ :=
    field_completed true featureInput (none :: descriptive.reverse.map some) [] firstRun stopped
  change EvalsToInTime machine.step (config (some .candidateEnd) endInput [] [] []
    (none :: (feature.reverse.map some ++ none :: descriptive.reverse.map some)) []) (some final) time at secondRun
  obtain ⟨originalInput, endSame, ⟨originalRun⟩⟩ := candidate_end_completed endInput _ [] secondRun stopped
  obtain ⟨original, originalSame⟩ := original_completed originalInput _ [] originalRun stopped
  refine ⟨descriptive, feature, original, ?_⟩
  rw [prefixSame, firstSame, secondSame, endSame, originalSame, job_decompose]
  simp only [List.append_assoc]

theorem reflects_outputs {input returned : List (Option Bool)} {time : Nat}
    (executed : TM2OutputsInTime machine input (some returned) time) :
    ∃ descriptive feature original, input = job descriptive feature original ∧
      returned = Indexed.frame [descriptive, feature, original] := by
  obtain ⟨descriptive, feature, original, same⟩ := terminal_job executed rfl
  have actual := Eq.mp (congrArg (fun word : List (Option Bool) => TM2OutputsInTime machine word (some returned) time) same) executed
  have outputSame := StackMachineComposition.outputs_unique (outputs descriptive feature original).toTM2Outputs actual.toTM2Outputs
  exact ⟨descriptive, feature, original, same, outputSame.symm⟩

theorem clean_halts (input : List (Option Bool)) (state : machine.Cfg)
    (path : Reaches machine.step (initList machine input) state) (stopped : state.l = none) :
    ∃ output, state = haltList machine output := by
  obtain ⟨counted⟩ := StackMachineComposition.reaches_has_execution path
  let bounded : EvalsToInTime machine.step (initList machine input) (some state) counted.steps := ⟨counted, le_rfl⟩
  obtain ⟨descriptive, feature, original, same⟩ := terminal_job bounded stopped
  have expected := outputs descriptive feature original
  have actualValue : state ∈ StateTransition.eval machine.step (initList machine input) :=
    StateTransition.mem_eval.mpr ⟨path, (StackMachineComposition.source_step_none_iff machine state).mpr stopped⟩
  have canonical : haltList machine (Indexed.frame [descriptive, feature, original]) ∈
      StateTransition.eval machine.step (initList machine input) := by
    rw [same]
    exact StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches expected.toEvalsTo, by rfl⟩
  exact ⟨Indexed.frame [descriptive, feature, original], Part.mem_unique actualValue canonical⟩

theorem terminal_fields (word original : List Bool) {final : machine.Cfg} {time : Nat}
    (executed : EvalsToInTime machine.step (initList machine (Indexed.frame [word, original])) (some final) time)
    (stopped : final.l = none) :
    ∃ descriptive feature, word = FeatureTheory.DyadicSearch.pairCode descriptive feature := by
  obtain ⟨descriptive, feature, source, same⟩ := terminal_job executed stopped
  change Indexed.frame [word, original] = Indexed.frame [FeatureTheory.DyadicSearch.pairCode descriptive feature, source] at same
  have fields := Indexed.frame_injective same
  exact ⟨descriptive, feature, (List.cons.inj fields).1⟩

end Mettapedia.Computability.E2PairMachine
