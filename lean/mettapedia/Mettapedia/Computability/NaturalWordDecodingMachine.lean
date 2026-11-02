import Mettapedia.Computability.NaturalWordMachine
import Mettapedia.Computability.WordDropLastMachine
import Mettapedia.Computability.FramedWordMapping

/-!
# Physical inverse of the dense word/natural field codec

The digit homomorphism reads a canonical compiler natural field, the existing
binary machine increments it, and a finite buffer physically removes its high
sentinel. The admitted image is precisely the existing exact word codec; the
execution law is not an assertion of arbitrary malformed-field admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.NaturalWordDecodingMachine

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open BinaryStackArithmetic WordTemplateMachine

def digits : Γ' → List Bool
  | .bit0 => [false]
  | .bit1 => [true]
  | .cons | .consₗ => []

theorem digits_symbol (word : List Bool) : (word.map NaturalWordMachine.symbol).flatMap digits = word := by
  induction word with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [NaturalWordMachine.symbol, digits, ih]

theorem digits_field (word : BinString) :
    (trList [NaturalWordEncoding.encode word]).flatMap digits = NaturalWordMachine.borrowWord true word := by
  rw [← NaturalWordMachine.encoded_field, List.flatMap_append, digits_symbol]
  simp [digits]

def digitMachine : FinTM2 := WordHomomorphismMachine.machine digits

local instance : Fintype (digitMachine.Γ digitMachine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (digitMachine.Γ digitMachine.k₁) := inferInstanceAs (Inhabited Bool)
local instance : Fintype (BinaryStackArithmetic.machine.Γ BinaryStackArithmetic.machine.k₁) :=
  inferInstanceAs (Fintype Bool)
local instance : Inhabited (BinaryStackArithmetic.machine.Γ BinaryStackArithmetic.machine.k₁) :=
  inferInstanceAs (Inhabited Bool)

def incremented : FinTM2 := StackMachineComposition.machine digitMachine BinaryStackArithmetic.machine (Equiv.refl Bool)

local instance : Fintype (incremented.Γ incremented.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (incremented.Γ incremented.k₁) := inferInstanceAs (Inhabited Bool)

def machine : FinTM2 :=
  StackMachineComposition.machine incremented (WordDropLastMachine.machine Bool) (Equiv.refl Bool)

attribute [local implicit_reducible] digitMachine incremented machine WordDropLastMachine.machine
  BinaryStackArithmetic.machine WordHomomorphismMachine.machine

/-- Original word length controls decoding time, including both physical
handoffs and the sentinel-removal scan. No natural-valued register is used. -/
def outputs (word : BinString) :
    TM2OutputsInTime machine (trList [NaturalWordEncoding.encode word]) (some word) (24 * (word.length + 1)) := by
  have read := WordHomomorphismMachine.outputs digits (trList [NaturalWordEncoding.encode word])
  rw [digits_field] at read
  have incrementedRun := BinaryStackArithmetic.outputs (NaturalWordMachine.borrowWord true word)
  rw [NaturalWordMachine.increment_borrowWord] at incrementedRun
  have first := StackMachineComposition.outputs digitMachine BinaryStackArithmetic.machine (Equiv.refl Bool)
    (trList [NaturalWordEncoding.encode word]) (NaturalWordMachine.borrowWord true word) (word ++ [true])
    _ _ read (by
      change TM2OutputsInTime BinaryStackArithmetic.machine
        ((NaturalWordMachine.borrowWord true word).map id) _ _
      simpa only [List.map_id] using incrementedRun)
  have dropped := WordDropLastMachine.outputs Bool word true
  have joined := StackMachineComposition.outputs incremented (WordDropLastMachine.machine Bool) (Equiv.refl Bool)
    (trList [NaturalWordEncoding.encode word]) (word ++ [true]) word _ _ first (by
      change TM2OutputsInTime (WordDropLastMachine.machine Bool) ((word ++ [true]).map id) _ _
      simpa only [List.map_id] using dropped)
  have cells := (NaturalWordMachine.field_length_bounds word).2
  have bits := (NaturalWordMachine.borrowWord_length true word).2
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

local instance : Fintype (machine.Γ machine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (machine.Γ machine.k₁) := inferInstanceAs (Inhabited Bool)
local instance : Inhabited (machine.Γ machine.k₀) := inferInstanceAs (Inhabited Γ')

def vectorMachine : FinTM2 := FramedWordMapping.machine machine

/-- Every field occurrence is decoded in place in the ordered frame, including
empty words and repeated words. All subroutine transfers are in the clock. -/
noncomputable def vector_outputs (words : List BinString) :
    TM2OutputsInTime vectorMachine
      (Indexed.frame (words.map fun word => trList [NaturalWordEncoding.encode word]))
      (some (Indexed.frame words))
      (32 * (Indexed.frame (words.map fun word => trList [NaturalWordEncoding.encode word])).length + 2) := by
  have run := FramedWordMapping.outputs machine
    (fun word => trList [NaturalWordEncoding.encode word]) id (fun word => 24 * (word.length + 1)) outputs words
  simp only [List.map_id] at run
  have bound : FramedWordMapping.totalClock machine
      (fun word => trList [NaturalWordEncoding.encode word]) id (fun word => 24 * (word.length + 1)) words ≤
      32 * (Indexed.frame (words.map fun word => trList [NaturalWordEncoding.encode word])).length + 2 := by
    clear run
    rw [FramedWordMapping.totalClock_eq]
    induction words with
    | nil => simp [Indexed.frame]
    | cons word rest ih =>
        have cells := NaturalWordMachine.field_length_bounds word
        simp only [List.map_cons, List.sum_cons, Indexed.frame, List.flatMap_cons, List.length_append,
          List.length_map, List.length_cons, List.length_nil] at ih ⊢
        dsimp only [id_eq] at ih ⊢
        omega
  exact ⟨run.toEvalsTo, run.steps_le_m.trans bound⟩

end Mettapedia.Computability.NaturalWordDecodingMachine
