import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords

/-!
# Compiling a register decision to fetched x86

Every test compares runtime registers. A leaf materializes its
word and jumps to the common continuation. Placement of the
entire emitted fragment is sufficient for the individual
instruction premises; memory is unchanged on every path.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisions

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch Jump registerCode compareDelta jumpDelta)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Tree
  | leaf (word : BitVec 32)
  | test (condition : Comparison) (left right : Fin 16) (yes no : Tree)

def Tree.answer (registers : Fin 16 → Word) : Tree → BitVec 32
  | .leaf word => word
  | .test condition left right yes no =>
    if condition.evaluate (registers left) (registers right) then yes.answer registers else no.answer registers

def Tree.cost (registers : Fin 16 → Word) : Tree → ℕ
  | .leaf _ => 2
  | .test condition left right yes no =>
    2 + if condition.evaluate (registers left) (registers right) then yes.cost registers else no.cost registers

def Tree.reads : Tree → Finset (Fin 16)
  | .leaf _ => ∅
  | .test _ left right yes no => insert left (insert right (yes.reads ∪ no.reads))

def Tree.width : Tree → ℕ
  | .leaf _ => 11
  | .test _ _ _ yes no => 9 + yes.width + no.width

def compareBytes (condition : Comparison) (left right : Fin 16) (start no : ℕ) : List ℕ :=
  registerCode 0x39 right left ++ X86NativeJcc.code (X86PreparedCompare.negative condition) (compareDelta start no)

def emit (destination : Fin 16) (exit : ℕ) : Tree → ℕ → List ℕ
  | .leaf word, start =>
    X86Immediate32.code destination word ++ X86UnconditionalJump.Block.code (jumpDelta (start + 6) exit)
  | .test condition left right yes no, start =>
    let rightAt := start + 9 + yes.width
    compareBytes condition left right start rightAt ++ (emit destination exit yes (start + 9) ++
      emit destination exit no rightAt)

theorem compare_size (condition : Comparison) (left right : Fin 16) (start no : ℕ) :
    (compareBytes condition left right start no).length = 9 := by
  simp only [compareBytes, List.length_append, registerCode, List.length_cons, List.length_nil, X86NativeJcc.code_length]

theorem compare_placed (image : NativeImage.View) (condition : Comparison) (left right : Fin 16)
    (start no : ℕ) (space : start + 9 ≤ image.size) (target : no ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (compareBytes condition left right start no)) :
    CompareBranch image start no condition left right := by
  obtain ⟨cmp, branch⟩ := NativeWords.code_append (show Code image start
    (registerCode 0x39 right left ++ X86NativeJcc.code (X86PreparedCompare.negative condition)
      (compareDelta start no)) from bytes)
  rw [show (registerCode 0x39 right left).length = 3 from rfl] at branch
  refine ⟨space, target, ?_, cmp, branch⟩
  unfold compareDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

theorem size (destination : Fin 16) (exit : ℕ) (tree : Tree) (start : ℕ) :
    (emit destination exit tree start).length = tree.width := by
  induction tree generalizing start with
  | leaf word =>
    simp only [emit, List.length_append, X86Immediate32.code_length, X86UnconditionalJump.Block.code_length, Tree.width]
  | test condition left right yes no iy ino =>
    simp only [emit, List.length_append, compare_size, iy, ino, Tree.width, Nat.add_assoc]

inductive Placed (image : NativeImage.View) (destination : Fin 16) (exit : ℕ) : ℕ → Tree → Prop where
  | leaf (start : ℕ) (word : BitVec 32) (within : start + 6 ≤ image.size)
      (materialize : Code image start (X86Immediate32.code destination word))
      (join : Jump image (start + 6) exit) : Placed image destination exit start (.leaf word)
  | test {start : ℕ} {condition : Comparison} {left right : Fin 16} {yes no : Tree}
      (compare : CompareBranch image start (start + 9 + yes.width) condition left right)
      (success : Placed image destination exit (start + 9) yes)
      (failure : Placed image destination exit (start + 9 + yes.width) no) :
      Placed image destination exit start (.test condition left right yes no)

theorem placed_of_emitted (image : NativeImage.View) (destination : Fin 16) (exit : ℕ)
    (tree : Tree) (start : ℕ) (room : start + tree.width ≤ image.size)
    (target : exit ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit destination exit tree start)) :
    Placed image destination exit start tree := by
  induction tree generalizing start with
  | leaf word =>
    obtain ⟨set, join⟩ := NativeWords.code_append (show Code image start
      (X86Immediate32.code destination word ++ X86UnconditionalJump.Block.code (jumpDelta (start + 6) exit)) from installed)
    rw [X86Immediate32.code_length] at join
    simp only [Tree.width] at room
    refine .leaf start word (by omega) set ⟨by omega, target, ?_, join⟩
    unfold jumpDelta
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
    omega
  | test condition left right yes no iy ino =>
    let alternate := start + 9 + yes.width
    obtain ⟨compare, children⟩ := NativeWords.code_append (show Code image start
      (compareBytes condition left right start alternate ++ (emit destination exit yes (start + 9) ++
        emit destination exit no alternate)) from installed)
    rw [compare_size] at children
    obtain ⟨passed, failed⟩ := NativeWords.code_append children
    rw [size] at failed
    simp only [Tree.width] at room
    have checked := compare_placed image condition left right start alternate (by omega)
      (by dsimp only [alternate]; omega) short compare
    exact .test checked (iy (start + 9) (by omega) passed)
      (ino alternate (by dsimp only [alternate]; omega) failed)

def clobbers (destination : Fin 16) : Finset Register := {key destination, .rflags, .rip}

theorem clobbers_data (destination : Fin 16) : clobbers destination ⊆ dataRegisters := by
  revert destination
  decide +kernel

private theorem compares_keep (r : Fin 16) : key r ∉ ({.rflags, .rip} : Finset Register) := by
  revert r
  decide +kernel

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (tree : Tree) (registers : Fin 16 → Word)
    {image : NativeImage.View} {base : BitVec 48} {start exit : ℕ}
    {before : X86RegisterRefinement.State} (point : At image before base start)
    (placed : Placed image destination exit start tree)
    (operands : ∀ r ∈ tree.reads, lookup before r = some (registers r)) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (tree.cost registers)).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers destination) ∅ before after ∧
      lookup after destination = some ((tree.answer registers).zeroExtend 64) ∧
      Nonempty (At image after base exit) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction placed generalizing before with
  | leaf start word within materialize join =>
    obtain ⟨set, ran, setFrame, result, ⟨atJump⟩⟩ :=
      X86PlacedScalar.rex_immediate other extra vector point within destination word materialize
    obtain ⟨after, jumped, jumpedFrame, endpoint⟩ :=
      X86PlacedScalar.jump other extra vector atJump join
    have frames := (X86StateFrame.registerOnly setFrame).trans (X86StateFrame.registerOnly jumpedFrame)
    have unchanged : key destination ∉ ({.rip} : Finset Register) :=
      fun seen => compares_keep destination (Finset.mem_insert_of_mem seen)
    refine ⟨after, X86FuelPrefix.fetches_then 1 1 before set after ran jumped,
      frames.mono ?_ (by simp), (jumpedFrame.lookup destination unchanged).trans result, endpoint⟩
    intro r member
    simp only [clobbers, X86Immediate32.writes, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at member ⊢
    tauto
  | @test start condition left right yes no compare success failure iy ino =>
    obtain ⟨tested, ran, frame, ⟨branch⟩⟩ :=
      X86PlacedScalar.compare_branch other extra vector point condition left right compare (registers left) (registers right)
        (operands left (by simp [Tree.reads])) (operands right (by simp [Tree.reads]))
    have stable (r : Fin 16) (reads : r ∈ (.test condition left right yes no : Tree).reads) :
        lookup tested r = some (registers r) := (frame.lookup r (compares_keep r)).trans (operands r reads)
    have subset : ({.rflags, .rip} : Finset Register) ⊆ clobbers destination := by simp [clobbers]
    cases accepted : condition.evaluate (registers left) (registers right) with
    | false =>
      have atNo : At image tested base (start + 9 + yes.width) := by simpa [accepted] using branch
      obtain ⟨after, rest, frameTail, outcome, endpoint⟩ := ino atNo
        (fun reg seen => stable reg (by simp [Tree.reads, seen]))
      refine ⟨after, ?_, ((X86StateFrame.registerOnly frame).trans frameTail).mono
        (Finset.union_subset subset (Finset.Subset.refl _)) (by simp), ?_, endpoint⟩
      · simpa [Tree.cost, accepted] using (X86FuelPrefix.fetches_then 2 _ before tested after ran rest)
      · simpa [Tree.answer, accepted] using outcome
    | true =>
      have atYes : At image tested base (start + 9) := by simpa [accepted] using branch
      obtain ⟨after, rest, frameTail, outcome, endpoint⟩ := iy atYes
        (fun reg seen => stable reg (by simp [Tree.reads, seen]))
      refine ⟨after, ?_, ((X86StateFrame.registerOnly frame).trans frameTail).mono
        (Finset.union_subset subset (Finset.Subset.refl _)) (by simp), ?_, endpoint⟩
      · simpa [Tree.cost, accepted] using (X86FuelPrefix.fetches_then 2 _ before tested after ran rest)
      · simpa [Tree.answer, accepted] using outcome

end Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisions
