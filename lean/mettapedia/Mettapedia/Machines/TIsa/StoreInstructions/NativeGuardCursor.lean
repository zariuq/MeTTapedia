import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardPolicy

/-!
# Advancing or closing the native guard scan

Advancing rewrites just the occurrence ordinal. Closing the
scan reads the remaining counter only for exact count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardCursor

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls CodeApart footprint)
open X86PlacedScalar (Code Jump CompareBranch registerCode jumpDelta)
open NativeGuardWorkspace (Frame)
open IndexedGuard (Query)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rcx, .rsi, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def ordinalBytes (frame : Frame) : Finset ℕ := footprint (frame.cell 14).address

def addCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 1
def storeCode : List ℕ := NativeGuardPolicy.encoding.bytes 1 112
def advance (start next : ℕ) : List ℕ :=
  NativeGuardOperands.stackCode ++ (NativeGuardOperands.indexCode ++ (addCode ++
    (storeCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 20) next))))
theorem advance_size (start next : ℕ) : (advance start next).length = 25 := rfl

structure AdvancePlaced (image : NativeImage.View) (start next : ℕ) : Prop where
  extent : start + 25 ≤ image.size
  stack : Code image start NativeGuardOperands.stackCode
  index : Code image (start + 3) NativeGuardOperands.indexCode
  add : Code image (start + 10) addCode
  store : Code image (start + 13) storeCode
  jump : Jump image (start + 20) next

theorem advance_placed (image : NativeImage.View) (start next : ℕ)
    (extent : start + 25 ≤ image.size) (target : next ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (advance start next)) : AdvancePlaced image start next := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (NativeGuardOperands.stackCode ++ _) from code)
  obtain ⟨idx, rest⟩ := NativeWords.code_append rest
  obtain ⟨add, rest⟩ := NativeWords.code_append rest
  obtain ⟨store, jump⟩ := NativeWords.code_append rest
  refine ⟨extent, stack, idx, add, store, ⟨by omega, target, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

theorem fetched_advance (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (code : AdvancePlaced image start next)
    (frame : Frame) (stack : lookup before 4 = some frame.pointer) (ordinal : ℕ)
    (current : Reads before (frame.cell 14).address (BitVec.ofNat 64 ordinal)) (one : lookup before 13 = some 1)
    (apart : CodeApart image base (ordinalBytes frame)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (ordinalBytes frame) before after ∧
      Reads after (frame.cell 14).address (BitVec.ofNat 64 (ordinal + 1)) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  obtain ⟨a, opened, moved, address, ⟨atIndex⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have first := X86StateFrame.registerOnly moved
  obtain ⟨b, indexed, loaded, known, ⟨atAdd⟩⟩ := (NativeAgendaRead.fieldSource frame 14).fetch (handlers other extra)
    vector NativeGuardOperands.indexWire (BitVec.ofNat 64 ordinal) atIndex
    (controls.transport first (by decide)) address (current.preserved first (by simp)) (show start + 10 ≤ image.size by omega) code.index
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at indexed
  have firstTwo := first.trans loaded
  obtain ⟨c, added, addFrame, addedWord, ⟨atStore⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector (show At image b base (start + 10) from atAdd) (by omega)
    .add 13 1 (BitVec.ofNat 64 ordinal) 1 ((firstTwo.lookup 13 (by decide)).trans one) known code.add
  have arith : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [arith] at added
  have changed : lookup c 1 = some (BitVec.ofNat 64 (ordinal + 1)) := by
    change lookup c 1 = some (BitVec.ofNat 64 ordinal + BitVec.ofNat 64 1) at addedWord
    rwa [BitVec.ofNat_add_ofNat] at addedWord
  have beforeStore := firstTwo.trans (X86StateFrame.registerOnly addFrame)
  obtain ⟨d, stored, storeFrame, advanced, ⟨atJump⟩⟩ := X86PlacedMemory.stores (handlers other extra)
    vector (show At image c base (start + 13) from atStore) (controls.transport beforeStore (by decide))
    NativeGuardPolicy.encoding 1 112 frame.pointer (BitVec.ofNat 64 (ordinal + 1)) (frame.cell 14)
    ((loaded.trans (X86StateFrame.registerOnly addFrame)).lookup 6 (by decide) |>.trans address)
    changed (show start + 20 ≤ image.size by omega) code.store apart
  obtain ⟨after, hopped, hoppedFrame, done⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image d base (start + 20) from atJump) code.jump
  have frameAll : X86StateFrame.Frame clobbers (ordinalBytes frame) before after :=
    ((beforeStore.trans storeFrame).trans (X86StateFrame.registerOnly hoppedFrame)).mono (by decide) (by simp [ordinalBytes])
  exact ⟨after, X86FuelPrefix.fetches_then 4 1 before d after
    (X86FuelPrefix.fetches_then 3 1 before c d
      (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b opened indexed) added) stored)
    hopped, frameAll, advanced.preserved (X86StateFrame.registerOnly hoppedFrame) (by simp), done⟩

def finishWidth : Query → ℕ
  | .count _ => 24
  | _ => 5

private def jump (start next : ℕ) : List ℕ := X86UnconditionalJump.Block.code (jumpDelta start next)
def finish (q : Query) (start pass fail : ℕ) : List ℕ :=
  match q with
  | .any => jump start fail
  | .absent => jump start pass
  | .count _ => NativeGuardPolicy.stackCode ++ (NativeGuardPolicy.loadCode ++
    (NativeDecisions.compareBytes .equal 0 12 (start + 10) fail ++ jump (start + 19) pass))

theorem finish_size (q : Query) (start pass fail : ℕ) : (finish q start pass fail).length = finishWidth q := by
  cases q <;> simp [finish, finishWidth, jump, X86UnconditionalJump.Block.code_length, NativeDecisions.compare_size,
    show NativeGuardPolicy.stackCode.length = 3 from rfl, show NativeGuardPolicy.loadCode.length = 7 from rfl]

inductive FinishPlaced (image : NativeImage.View) : Query → ℕ → ℕ → ℕ → Prop
  | any {start pass fail : ℕ} : Jump image start fail → FinishPlaced image .any start pass fail
  | absent {start pass fail : ℕ} : Jump image start pass → FinishPlaced image .absent start pass fail
  | count {n start pass fail : ℕ} :
      Code image start NativeGuardPolicy.stackCode →
      Code image (start + 3) NativeGuardPolicy.loadCode →
      CompareBranch image (start + 10) fail .equal 0 12 →
      Jump image (start + 19) pass → FinishPlaced image (.count n) start pass fail

private theorem jump_placed (image : NativeImage.View) (start next : ℕ)
    (extent : start + 5 ≤ image.size) (target : next ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (jump start next)) : Jump image start next := by
  refine ⟨extent, target, ?_, code⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

theorem finish_placed (image : NativeImage.View) (q : Query) (start pass fail : ℕ)
    (extent : start + finishWidth q ≤ image.size) (passed : pass ≤ image.size) (failed : fail ≤ image.size)
    (short : image.size < 2 ^ 31) (code : Code image start (finish q start pass fail)) : FinishPlaced image q start pass fail := by
  cases q with
  | any => exact .any (jump_placed image _ _ extent failed short code)
  | absent => exact .absent (jump_placed image _ _ extent passed short code)
  | count n =>
    change start + 24 ≤ image.size at extent
    obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (NativeGuardPolicy.stackCode ++ _) from code)
    obtain ⟨load, rest⟩ := NativeWords.code_append rest
    change Code image (start + 10) _ at rest
    obtain ⟨test, jump⟩ := NativeWords.code_append rest
    rw [NativeDecisions.compare_size] at jump
    exact .count stack load (NativeDecisions.compare_placed image _ _ _ _ _ (by omega) failed short test)
      (jump_placed image _ _ (by omega) passed short jump)

theorem fetched_finish (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start pass fail : ℕ} {before : Native}
    (q : Query) (point : At image before base start) (controls : Controls before) (code : FinishPlaced image q start pass fail)
    (frame : Frame) (stack : lookup before 4 = some frame.pointer) (remaining : ℕ) (fits : remaining < 2 ^ 64)
    (count : Reads before (frame.cell 15).address (BitVec.ofNat 64 remaining)) (zero : lookup before 12 = some 0) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      Nonempty (At image after base (if NativeGuardPolicy.scan (NativeGuardPolicy.adjust q remaining) [] then pass else fail)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  cases code with
  | any route =>
    obtain ⟨after, ran, frame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other) extra vector point route
    exact ⟨after, 1, ran, (X86StateFrame.registerOnly frame).mono (by decide) (by simp), endpoint⟩
  | absent route =>
    obtain ⟨after, ran, frame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other) extra vector point route
    exact ⟨after, 1, ran, (X86StateFrame.registerOnly frame).mono (by decide) (by simp), endpoint⟩
  | count stackCode loadCode test route =>
    have extent := test.1
    obtain ⟨a, opened, openedFrame, pointer, ⟨atCount⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector point (by omega) 4 6 frame.pointer stack stackCode
    have openedMemory := X86StateFrame.registerOnly openedFrame
    obtain ⟨b, loaded, loadedFrame, n, ⟨atTest⟩⟩ := (NativeAgendaRead.fieldSource frame 15).fetch
      (handlers other extra) vector NativeGuardPolicy.wire (BitVec.ofNat 64 remaining) atCount
      (controls.transport openedMemory (by decide)) pointer (count.preserved openedMemory (by simp))
      (show _ + 10 ≤ image.size by omega) loadCode
    have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
    rw [linked] at loaded
    have loadedMemory := openedMemory.trans loadedFrame
    obtain ⟨c, compared, compareFrame, ⟨decision⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector atTest .equal 0 12 test _ _ n
      ((loadedMemory.lookup 12 (by decide)).trans zero)
    have known : BitVec.ofNat 64 remaining = 0 ↔ remaining = 0 := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
      rfl
    simp only [Comparison.evaluate, beq_iff_eq, known] at decision
    have previous := loadedMemory.trans (X86StateFrame.registerOnly compareFrame)
    have ran := X86FuelPrefix.fetches_then 2 2 before b c (X86FuelPrefix.fetches_then 1 1 before a b opened loaded) compared
    by_cases empty : remaining = 0
    · simp only [if_pos empty] at decision
      obtain ⟨after, hopped, hoppedFrame, endpoint⟩ := X86PlacedScalar.jump
        (X86PlacedFrameAddress.nativeBase other) extra vector decision route
      refine ⟨after, 5, X86FuelPrefix.fetches_then 4 1 before c after ran hopped,
        (previous.trans (X86StateFrame.registerOnly hoppedFrame)).mono (by decide) (by simp), ?_⟩
      simpa [NativeGuardPolicy.scan, NativeGuardPolicy.adjust, SymbolicGuardScan.scan, SymbolicGuardScan.countRemaining, empty] using endpoint
    · simp only [if_neg empty] at decision
      refine ⟨c, 4, ran, previous.mono (by decide) (by simp), ?_⟩
      simpa [NativeGuardPolicy.scan, NativeGuardPolicy.adjust, SymbolicGuardScan.scan, SymbolicGuardScan.countRemaining, empty] using Nonempty.intro decision

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardCursor
