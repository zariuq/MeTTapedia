import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences
import Mettapedia.Machines.TIsa.X86PlacedScalar

/-!
# A native TEST on two instantiated operands

A reversible codebook allows exact equality on the two code words.
Without such a representation, equality on codes is not a test of the
values. The source test retains all bindings on success and writes a
usual p1 boolean. The native block materializes that same boolean
with checked comparison, literal and join instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.WordTests

open Derivation (Matcher Determinate Match Store agree passes)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch Jump)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u v w

variable {T : Type u} {V : Type v} {B : Type w}

theorem code_equality (codes : PackedOccurrences.Codes V) {v w : V} {left right : Word}
    (encodedLeft : codes.encode v = some left) (encodedRight : codes.encode w = some right) :
    left = right ↔ v = w := by
  constructor
  · intro same
    subst right
    exact Option.some.inj ((codes.reads encodedLeft).symm.trans (codes.reads encodedRight))
  · intro same
    subst w
    exact Option.some.inj (encodedLeft.symm.trans encodedRight)

private theorem unchanged_level (st : StoreInstructions.State V B) (level : ℕ) :
    st.setLevel level (st.levels level) = st := by
  unfold StoreInstructions.State.setLevel
  rw [Function.update_eq_self]

theorem equal_test_words [DecidableEq V] (matcher : Matcher T V B) (codes : PackedOccurrences.Codes V)
    (st : StoreInstructions.State V B) (level : ℕ) (dst : P1Source.Reg) (lhs rhs : T)
    (v w : V) (left right : Word)
    (readLeft : matcher.instantiate (st.levels level).bindings lhs = some v)
    (readRight : matcher.instantiate (st.levels level).bindings rhs = some w)
    (encodedLeft : codes.encode v = some left) (encodedRight : codes.encode w = some right) :
    executeInstruction matcher st (.transform (.test (.check (.equal lhs rhs)) level dst)) =
      .ok (st.write dst (booleanWord (Comparison.equal.evaluate left right))) := by
  have encoded := code_equality codes encodedLeft encodedRight
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, Determinate.apply, passes,
    agree, readLeft, readRight, Comparison.evaluate]
  by_cases equalValue : v = w
  · have equal := encoded.mpr equalValue
    simp [equalValue, equal, booleanWord, unchanged_level]
  · have different : left ≠ right := fun h => equalValue (encoded.mp h)
    have unequal : (left == right) = false := beq_eq_false_iff_ne.mpr different
    simp [equalValue, unequal, booleanWord]

structure Block (image : NativeImage.View) (offset rejected finish : ℕ) (left right dst : Fin 16)
    (condition : Comparison := .equal) : Prop where
  compare : CompareBranch image offset rejected condition left right
  yesInside : offset + 9 + 6 ≤ image.size
  noInside : rejected + 6 ≤ image.size
  yesCode : Code image (offset + 9) (X86Immediate32.code dst 1)
  noCode : Code image rejected (X86Immediate32.code dst 0)
  yesJump : Jump image (offset + 9 + 6) finish
  noJump : Jump image (rejected + 6) finish

private theorem result_word (test : Bool) :
    ((if test then 1 else 0 : BitVec 32).zeroExtend 64) = booleanWord test := by
  cases test <;> rfl

private theorem rip_not_result (result : Fin 16) : key result ∉ ({.rip} : Finset Register) := by
  revert result
  decide +kernel

theorem lower_compare_x86 (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48}
    {offset rejected finish : ℕ} {left right dst : Fin 16} {condition : Comparison}
    (point : At image native base offset) (code : Block image offset rejected finish left right dst condition)
    (a b : Word) (aKnown : lookup native left = some a) (bKnown : lookup native right = some b) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches 4).run native = .ok () after ∧
      RegisterFrame (({.rflags, .rip} : Finset Register) ∪ X86Immediate32.writes dst ∪ {.rip}) native after ∧
      lookup after dst = some (booleanWord (condition.evaluate a b)) ∧
      Nonempty (At image after base finish) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  let flag := condition.evaluate a b
  let chosen := if flag then offset + 9 else rejected
  let literal : BitVec 32 := if flag then 1 else 0
  obtain ⟨afterCmp, compared, cmpFrame, ⟨branch⟩⟩ :=
    X86PlacedScalar.compare_branch other extra vector point condition left right code.compare a b aKnown bKnown
  have fits : chosen + 6 ≤ image.size := by
    dsimp only [chosen]
    split
    · exact code.yesInside
    · exact code.noInside
  have materialize : Code image chosen (X86Immediate32.code dst literal) := by
    dsimp only [chosen, literal]
    split
    · exact code.yesCode
    · exact code.noCode
  have join : Jump image (chosen + 6) finish := by
    dsimp only [chosen]
    split
    · exact code.yesJump
    · exact code.noJump
  have entry : At image afterCmp base chosen := branch
  obtain ⟨afterLiteral, moved, movFrame, value, ⟨beforeJump⟩⟩ :=
    X86PlacedScalar.rex_immediate other extra vector entry fits dst literal materialize
  obtain ⟨after, jumped, jumpFrame, done⟩ := X86PlacedScalar.jump other extra vector beforeJump join
  have ran : (X86FuelPrefix.fetches 4).run native = .ok () after := by
    rw [show 4 = 2 + (1 + 1) from rfl, X86FuelPrefix.fetches_add, run_bind, compared]
    dsimp only
    rw [X86FuelPrefix.fetches_add, run_bind, moved]
    exact jumped
  rw [show literal.zeroExtend 64 = booleanWord flag from result_word flag] at value
  exact ⟨after, ran, (cmpFrame.trans movFrame).trans jumpFrame,
    (jumpFrame.lookup dst (rip_not_result dst)).trans value, done⟩

theorem lower_equal_test_x86 [DecidableEq V] (matcher : Matcher T V B) (codes : PackedOccurrences.Codes V)
    (st : StoreInstructions.State V B) (level : ℕ) (result : P1Source.Reg) (lhs rhs : T)
    (v w : V) (a b : Word)
    (readLeft : matcher.instantiate (st.levels level).bindings lhs = some v)
    (readRight : matcher.instantiate (st.levels level).bindings rhs = some w)
    (encodedLeft : codes.encode v = some a) (encodedRight : codes.encode w = some b)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48}
    {offset rejected finish : ℕ} {left right : Fin 16}
    (point : At image native base offset)
    (code : Block image offset rejected finish left right (X86BoundedLoad.physical result))
    (aKnown : lookup native left = some a) (bKnown : lookup native right = some b) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after abstract,
      (X86FuelPrefix.fetches 4).run native = .ok () after ∧
      executeInstruction matcher st (.transform (.test (.check (.equal lhs rhs)) level result)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical result) = some (abstract.machine.registers result) ∧
      Nonempty (At image after base finish) := by
  obtain ⟨after, ran, _, asWord, placed⟩ := lower_compare_x86 other extra vector point code a b aKnown bKnown
  refine ⟨after, st.write result (booleanWord (Comparison.equal.evaluate a b)), ran,
    equal_test_words matcher codes st level result lhs rhs v w a b readLeft readRight encodedLeft encodedRight,
    ?_, placed⟩
  simpa [StoreInstructions.State.write, P1WordExecution.State.write] using asWord

namespace Examples

private def identity : Matcher Word Word Unit := ⟨(), fun _ p v => if p = v then some () else none, fun _ w => some w⟩
private def words : PackedOccurrences.Codes Word := ⟨some, some, fun equal => by cases equal; rfl⟩

theorem equal_values_pass (st : StoreInstructions.State Word Unit) :
    executeInstruction identity st (.transform (.test (.check (.equal 23 23)) 0 1)) = .ok (st.write 1 1) := by
  exact equal_test_words identity words st 0 1 23 23 23 23 23 23 rfl rfl rfl rfl

theorem unequal_values_refuse (st : StoreInstructions.State Word Unit) :
    executeInstruction identity st (.transform (.test (.check (.equal 23 24)) 0 1)) = .ok (st.write 1 0) := by
  exact equal_test_words identity words st 0 1 23 24 23 24 23 24 rfl rfl rfl rfl

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.WordTests
