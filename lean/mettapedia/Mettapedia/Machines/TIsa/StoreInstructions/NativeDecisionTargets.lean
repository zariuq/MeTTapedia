import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisions

/-!
# Compiling a register decision to continuation targets

The same decision tree used for materialized words can instead
tail-transfer to its leaves. The leaves do not write a status
register. The caller's data registers and memory are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisionTargets

open _root_.X86Registers X86RegisterRefinement X86Execution
open NativeDecisions (Tree compareBytes compare_size compare_placed)
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch Jump jumpDelta)
local instance : MemoryPrimitives := X86Memory.ordinary

def width : Tree → ℕ
  | .leaf _ => 5
  | .test _ _ _ yes no => 9 + width yes + width no

def cost (registers : Fin 16 → Word) : Tree → ℕ
  | .leaf _ => 1
  | .test condition left right yes no =>
    2 + if condition.evaluate (registers left) (registers right) then cost registers yes else cost registers no

def emit (target : BitVec 32 → ℕ) : Tree → ℕ → List ℕ
  | .leaf word, start => X86UnconditionalJump.Block.code (jumpDelta start (target word))
  | .test condition left right yes no, start =>
    let alternate := start + 9 + width yes
    compareBytes condition left right start alternate ++
      (emit target yes (start + 9) ++ emit target no alternate)

theorem emit_size (target : BitVec 32 → ℕ) (tree : Tree) (start : ℕ) :
    (emit target tree start).length = width tree := by
  induction tree generalizing start with
  | leaf word => simp only [emit, width, X86UnconditionalJump.Block.code_length]
  | test condition left right yes no iy ino =>
    simp only [emit, List.length_append, compare_size, iy, ino, width, Nat.add_assoc]

inductive Placed (image : NativeImage.View) (target : BitVec 32 → ℕ) : ℕ → Tree → Prop where
  | leaf (start : ℕ) (word : BitVec 32) (jump : Jump image start (target word)) :
      Placed image target start (.leaf word)
  | test {start : ℕ} {condition : Comparison} {left right : Fin 16} {yes no : Tree}
      (check : CompareBranch image start (start + 9 + width yes) condition left right)
      (passed : Placed image target (start + 9) yes)
      (failed : Placed image target (start + 9 + width yes) no) :
      Placed image target start (.test condition left right yes no)

theorem placed_of_emitted (image : NativeImage.View) (target : BitVec 32 → ℕ)
    (tree : Tree) (start : ℕ) (size : start + width tree ≤ image.size)
    (destinations : ∀ word, target word ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit target tree start)) :
    Placed image target start tree := by
  induction tree generalizing start with
  | leaf word =>
    exact .leaf start word ⟨size, destinations word, by
      unfold jumpDelta
      have inside := destinations word
      change start + 5 ≤ image.size at size
      rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
      omega, installed⟩
  | test condition left right yes no iy ino =>
    let alternate := start + 9 + width yes
    obtain ⟨check, children⟩ := NativeWords.code_append (show Code image start
      (compareBytes condition left right start alternate ++
        (emit target yes (start + 9) ++ emit target no alternate)) from installed)
    rw [compare_size] at children
    obtain ⟨passed, failed⟩ := NativeWords.code_append children
    rw [emit_size] at failed
    change start + (9 + width yes + width no) ≤ image.size at size
    exact .test (compare_placed image condition left right start alternate (by omega)
      (by dsimp only [alternate]; omega) short check) (iy _ (by omega) passed)
      (ino alternate (by dsimp only [alternate]; omega) failed)

abbrev clobbers : Finset Register := {.rflags, .rip}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (target : BitVec 32 → ℕ) (tree : Tree) (registers : Fin 16 → Word)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : X86RegisterRefinement.State}
    (point : At image before base start) (placed : Placed image target start tree)
    (operands : ∀ r ∈ tree.reads, lookup before r = some (registers r)) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (cost registers tree)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base (target (tree.answer registers))) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction placed generalizing before with
  | leaf start word jump =>
    obtain ⟨after, ran, frame, endpoint⟩ := X86PlacedScalar.jump other extra vector point jump
    exact ⟨after, ran, (X86StateFrame.registerOnly frame).mono (by decide) (by simp), endpoint⟩
  | @test start condition left right yes no check passed failed iy ino =>
    obtain ⟨tested, ran, frame, ⟨atNext⟩⟩ := X86PlacedScalar.compare_branch other extra vector point condition left right check
      (registers left) (registers right) (operands left (by simp [Tree.reads])) (operands right (by simp [Tree.reads]))
    have preserved (r : Fin 16) (member : r ∈ (.test condition left right yes no : Tree).reads) :
        lookup tested r = some (registers r) :=
      (frame.lookup r (by fin_cases r <;> decide)).trans (operands r member)
    cases value : condition.evaluate (registers left) (registers right) with
    | true =>
      simp only [value, if_true] at atNext
      obtain ⟨after, loop, later, endpoint⟩ := iy atNext
        (fun r member => preserved r (by simp [Tree.reads, member]))
      simp only [cost, Tree.answer, value, if_true]
      exact ⟨after, X86FuelPrefix.fetches_then 2 _ before tested after ran loop,
        ((X86StateFrame.registerOnly frame).trans later).mono (by simp) (by simp), endpoint⟩
    | false =>
      simp only [value, Bool.false_eq_true, if_false] at atNext
      obtain ⟨after, loop, later, endpoint⟩ := ino atNext
        (fun r member => preserved r (by simp [Tree.reads, member]))
      simp only [cost, Tree.answer, value, Bool.false_eq_true, if_false]
      exact ⟨after, X86FuelPrefix.fetches_then 2 _ before tested after ran loop,
        ((X86StateFrame.registerOnly frame).trans later).mono (by simp) (by simp), endpoint⟩

namespace Examples

theorem one_leaf_emits_only_a_near_jump :
    emit (fun _ => 10) (.leaf 1) 0 = [233, 5, 0, 0, 0] := by decide +kernel

theorem changing_the_selected_target_changes_the_bytes :
    emit (fun _ => 10) (.leaf 1) 0 ≠ emit (fun _ => 11) (.leaf 1) 0 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisionTargets
