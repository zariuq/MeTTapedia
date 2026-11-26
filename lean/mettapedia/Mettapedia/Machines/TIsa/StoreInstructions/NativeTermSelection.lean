import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena

/-!
# Fetched selection of two term records by handle

The original unsigned handles are checked against the initialized
count before any address arithmetic. A successful path leaves both
handles intact. A failed path jumps to the malformed-input exit
before calculating or loading either record.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTermSelection

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch registerCode)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open NativeTermArena (Ready)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Side | left | right

def Side.input : Side → Index
  | .left => ⟨1, by decide⟩
  | .right => ⟨2, by decide⟩

def Side.output : Side → Index
  | .left => ⟨6, by decide⟩
  | .right => ⟨7, by decide⟩

def zeroBase : Base := ⟨0, by decide⟩
def recordBase : Base := ⟨3, by decide⟩

def scaleCode (side : Side) : List ℕ :=
  addressCode side.output.register side.input 3 zeroBase ++
    addressCode side.output.register side.output 2 recordBase

theorem scale_size (side : Side) : (scaleCode side).length = 8 := rfl

def zeroCode : List ℕ := registerCode 0x89 12 0

def emit (start malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 1 15 start malformed ++
    (NativeDecisions.compareBytes .lessUnsigned 2 15 (start + 9) malformed ++
      (zeroCode ++ (scaleCode .left ++ scaleCode .right)))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 37 := rfl

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 37 ≤ image.size
  checkLeft : CompareBranch image start malformed .lessUnsigned 1 15
  checkRight : CompareBranch image (start + 9) malformed .lessUnsigned 2 15
  zero : Code image (start + 18) zeroCode
  left : Code image (start + 21) (scaleCode .left)
  right : Code image (start + 29) (scaleCode .right)

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ) (space : start + 37 ≤ image.size)
    (target : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit start malformed)) :
    Placed image start malformed := by
  obtain ⟨leftTest, afterLeft⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 1 15 start malformed ++ _) from installed)
  rw [NativeDecisions.compare_size] at afterLeft
  obtain ⟨rightTest, rest⟩ := NativeWords.code_append afterLeft
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨zero, rest⟩ := NativeWords.code_append rest
  rw [show zeroCode.length = 3 from rfl] at rest
  obtain ⟨left, right⟩ := NativeWords.code_append rest
  rw [scale_size] at right
  exact ⟨space, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short leftTest,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short rightTest, zero, left, right⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev compareClobbers : Finset Register := {.rflags, .rip}

abbrev clobbers : Finset Register := {.rax, .rsi, .rdi, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem scale_fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {atCode : ℕ}
    {before : Native} (point : At image before base atCode) (extent : atCode + 8 ≤ image.size)
    (side : Side) (pointer handle : Word)
    (knownPointer : lookup before 3 = some pointer) (zero : lookup before 0 = some 0)
    (knownHandle : lookup before side.input.register = some handle)
    (installed : Code image atCode (scaleCode side)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame {key side.output.register, .rip} ∅ before after ∧
      lookup after side.output.register = some (pointer + handle * 32) ∧
      Nonempty (At image after base (atCode + 8)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨first, later⟩ := NativeWords.code_append (show Code image atCode
    (addressCode side.output.register side.input 3 zeroBase ++
      addressCode side.output.register side.output 2 recordBase) from installed)
  change Code image (atCode + 4) (addressCode side.output.register side.output 2 recordBase) at later
  obtain ⟨scaled, one, kept, value, ⟨positioned⟩⟩ := X86IndexedAddress.forms_address
    other extra vector point (by omega) side.output.register side.input 3 zeroBase first 0 handle zero knownHandle
  have stillPointer := (kept.lookup 3 (by cases side <;> decide)).trans knownPointer
  obtain ⟨after, two, final, exactWord, reached⟩ := X86IndexedAddress.forms_address other extra vector
    positioned (by omega) side.output.register side.output 2 recordBase later pointer _ stillPointer value
  change lookup after side.output.register = some (pointer + (0 + handle * (8 : Word)) * (4 : Word)) at exactWord
  have total : ((0 : Word) + handle * 8) * 4 = handle * 32 := by
    calc
      _ = (handle * 8) * 4 := congrArg (fun w : Word => w * 4) (BitVec.zero_add (handle * 8))
      _ = handle * ((8 : Word) * 4) := BitVec.mul_assoc _ _ _
      _ = handle * 32 := rfl
  rw [total] at exactWord
  have frame : RegisterFrame {key side.output.register, .rip} before after := (kept.trans final).mono (by simp)
  exact ⟨after, X86FuelPrefix.fetches_then 1 1 before scaled after one two,
    X86StateFrame.registerOnly frame, exactWord, reached⟩

def Rejected (image : NativeImage.View) (base : BitVec 48) (malformed : ℕ) (before after : Native) : Prop :=
  X86StateFrame.Frame compareClobbers ∅ before after ∧ Nonempty (At image after base malformed)

def Arrival {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
    {arena : PackedTerms.Arena} {before : Native} (ready : Ready layout arena before) (left right : Word)
    (image : NativeImage.View) (base : BitVec 48) (start malformed steps : ℕ) (after : Native) : Prop :=
  if l : left.toNat < arena.nodes.size then
    if r : right.toNat < arena.nodes.size then
      steps = 9 ∧ lookup after 6 = some (ready.bank ⟨left.toNat, l⟩).pointer ∧
        lookup after 7 = some (ready.bank ⟨right.toNat, r⟩).pointer ∧ Nonempty (At image after base (start + 37))
    else steps = 4 ∧ Rejected image base malformed before after
  else steps = 2 ∧ Rejected image base malformed before after

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ}
    {before : Native} (point : At image before base start) (placed : Placed image start malformed)
    {nodeCapacity edgeCapacity : ℕ} (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (arena : PackedTerms.Arena)
    (ready : Ready layout arena before) (left right : Word)
    (leftKnown : lookup before 1 = some left) (rightKnown : lookup before 2 = some right)
    (count : lookup before 15 = some (BitVec.ofNat 64 arena.nodes.size))
    (table : lookup before 3 = some layout.nodes.pointer) (zero : lookup before 12 = some 0) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ Arrival ready left right image base start malformed steps after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have room := placed.extent
  obtain ⟨a, leftCheck, leftFrame, ⟨lBranch⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 1 15 placed.checkLeft
    left _ leftKnown count
  change At image a base (if decide (left.toNat < (BitVec.ofNat 64 arena.nodes.size).toNat) then start + 9
    else malformed) at lBranch
  rw [ready.count_word] at lBranch
  by_cases leftInside : left.toNat < arena.nodes.size
  · simp only [leftInside, decide_true, if_true] at lBranch
    obtain ⟨b, rightCheck, rightFrame, ⟨rBranch⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector lBranch .lessUnsigned 2 15 placed.checkRight
      right _ ((leftFrame.lookup 2 (by decide)).trans rightKnown) ((leftFrame.lookup 15 (by decide)).trans count)
    have early := X86StateFrame.registerOnly (leftFrame.trans rightFrame)
    have checkedBoth := X86FuelPrefix.fetches_then 2 2 before a b leftCheck rightCheck
    change At image b base (if decide (right.toNat < (BitVec.ofNat 64 arena.nodes.size).toNat)
      then start + 9 + 9 else malformed) at rBranch
    rw [ready.count_word] at rBranch
    by_cases rightInside : right.toNat < arena.nodes.size
    · simp only [rightInside, decide_true, if_true] at rBranch
      obtain ⟨c, copied, copiedFrame, zeroed, ⟨forLeft⟩⟩ := X86PlacedRegisterMove.executes
        (handlers other extra) vector (show At image b base (start + 18) from rBranch) (by omega)
        12 0 0 ((early.lookup 12 (by decide)).trans zero) placed.zero
      have preset := early.trans (X86StateFrame.registerOnly copiedFrame)
      obtain ⟨d, calculatedLeft, leftShift, leftPointer, ⟨forRight⟩⟩ := scale_fetched other extra vector
        (show At image c base (start + 21) from forLeft) (by omega) .left layout.nodes.pointer left
        ((preset.lookup 3 (by decide)).trans table) zeroed ((preset.lookup 1 (by decide)).trans leftKnown) placed.left
      have throughLeft := preset.trans leftShift
      obtain ⟨after, calculatedRight, rightShift, rightPointer, endpoint⟩ := scale_fetched other extra vector
        (show At image d base (start + 29) from forRight) (by omega) .right layout.nodes.pointer right
        ((throughLeft.lookup 3 (by decide)).trans table) ((leftShift.lookup 0 (by decide)).trans zeroed)
        ((throughLeft.lookup 2 (by decide)).trans rightKnown) placed.right
      have ranCopy := X86FuelPrefix.fetches_then 4 1 before b c checkedBoth copied
      have ranLeft := X86FuelPrefix.fetches_then 5 2 before c d ranCopy calculatedLeft
      refine ⟨after, 9, X86FuelPrefix.fetches_then 7 2 before d after ranLeft calculatedRight,
        (throughLeft.trans rightShift).mono (by decide) (by simp), ?_⟩
      rw [Arrival, dif_pos leftInside, dif_pos rightInside, ready.bank_word, ready.bank_word]
      exact ⟨rfl, (rightShift.lookup 6 (by decide)).trans leftPointer, rightPointer, endpoint⟩
    · simp only [rightInside, decide_false] at rBranch
      refine ⟨b, 4, checkedBoth, early.mono (by decide) (by simp), ?_⟩
      rw [Arrival, dif_pos leftInside, dif_neg rightInside]
      exact ⟨rfl, early, ⟨rBranch⟩⟩
  · simp only [leftInside, decide_false] at lBranch
    have early := X86StateFrame.registerOnly leftFrame
    refine ⟨a, 2, leftCheck, early.mono (by decide) (by simp), ?_⟩
    rw [Arrival, dif_neg leftInside]
    exact ⟨rfl, early, ⟨lBranch⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTermSelection
