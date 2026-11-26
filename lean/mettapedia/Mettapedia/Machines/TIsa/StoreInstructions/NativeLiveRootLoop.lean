import Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRoots
import Mettapedia.Machines.TIsa.StoreInstructions.PackedGuardRoots

/-!
# Retargeting a whole live root vector

The loop only changes slots in the vector. Its prefix is the
new view and its suffix is the old view. In particular each
slot is mapped once, not repeatedly until it reaches a fixed
point. This is the move associated with one binding.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootLoop

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls footprint CodeApart)
open X86PlacedScalar (Code CompareBranch Jump jumpDelta)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open NativeLiveRoots (Input slotBytes)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start done malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 1 14 start done ++
    (NativeLiveRoots.emit (start + 9) malformed ++ (NativeOccursLoop.incrementCode ++
      X86UnconditionalJump.Block.code (jumpDelta (start + 54) start)))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 59 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, NativeLiveRoots.emit_size,
    X86UnconditionalJump.Block.code_length, show NativeOccursLoop.incrementCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 59 ≤ image.size
  check : CompareBranch image start done .lessUnsigned 1 14
  root : NativeLiveRoots.Placed image (start + 9) malformed
  increment : Code image (start + 51) NativeOccursLoop.incrementCode
  again : Jump image (start + 54) start

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ) (extent : start + 59 ≤ image.size)
    (finish : done ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start done malformed)) : Placed image start done malformed := by
  obtain ⟨check, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 1 14 start done ++ _) from code)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨root, rest⟩ := NativeWords.code_append rest
  rw [NativeLiveRoots.emit_size] at rest
  obtain ⟨advance, again⟩ := NativeWords.code_append rest
  refine ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finish short check,
    NativeLiveRoots.placed_of_emitted image _ _ (by omega) bad short root, advance, ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := insert .rcx NativeLiveRoots.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {rc mc : ℕ} {roots : Region rc} {map : Region mc} {translated : Array Word}
variable {image : NativeImage.View} {base : BitVec 48}

structure Cursor (original target active : Array Word) (ordinal : ℕ) : Prop where
  width : active.size = original.size
  previous : ∀ i, i < ordinal → active[i]? = target[i]?
  upcoming : ∀ i, ordinal ≤ i → active[i]? = original[i]?

theorem Cursor.start (original target : Array Word) : Cursor original target original 0 :=
  ⟨rfl, fun _ impossible => (Nat.not_lt_zero _ impossible).elim, fun _ _ => rfl⟩

theorem Cursor.bump {original target active : Array Word} {ordinal : ℕ}
    (cursor : Cursor original target active ordinal) (word : Word)
    (inside : ordinal < active.size) (found : target[ordinal]? = some word) :
    Cursor original target (active.set ordinal word inside) (ordinal + 1) := by
  refine ⟨(Array.size_set inside).trans cursor.width, ?_, ?_⟩
  · intro i previous
    by_cases same : i = ordinal
    · subst i
      exact (Array.getElem?_set_self inside).trans found.symm
    · rw [Array.getElem?_set_ne inside (Ne.symm same)]
      exact cursor.previous i (by omega)
  · intro i upcoming
    rw [Array.getElem?_set_ne inside (by omega)]
    exact cursor.upcoming i (by omega)

theorem Cursor.complete {original target active : Array Word} (cursor : Cursor original target active original.size)
    (width : target.size = original.size) : active = target := by
  apply Array.ext (cursor.width.trans width.symm)
  intro i inside targetInside
  have found := cursor.previous i (by rwa [cursor.width] at inside)
  rw [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem targetInside] at found
  exact Option.some.inj found

structure Ready (roots : Region rc) (map : Region mc) (active translated : Array Word)
    (ordinal limit : ℕ) (native : Native) : Prop where
  slot : Input roots map active translated ordinal native
  finish : lookup native 14 = some (BitVec.ofNat 64 limit)
  one : lookup native 13 = some 1

/-- The exact packed output is reached in twelve fetched
instructions per remaining slot and two to leave the loop. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start done malformed : ℕ} (code : Placed image start done malformed)
    (separate : NativeBindingSelection.Separated map roots)
    (apart : ∀ i : Fin rc, CodeApart image base (slotBytes roots i))
    (original target active : Array Word) (mapped : PackedSubstitution.translate translated original = some target)
    (ordinal remaining : ℕ) (bound : ordinal + remaining = original.size) (cursor : Cursor original target active ordinal)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Ready roots map active translated ordinal original.size before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after writes, (X86FuelPrefix.fetches (12 * remaining + 2)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ NativeMarkTable.Within roots ordinal original.size writes ∧
      Ready roots map target translated original.size original.size after ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  obtain ⟨width, atWord⟩ := PackedRemapCoordinates.coordinates translated original target mapped
  induction remaining generalizing ordinal active before with
  | zero =>
    have boundary : ordinal = original.size := by omega
    subst ordinal
    obtain rfl := cursor.complete width
    obtain ⟨after, ran, regs, ⟨halt⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector point .lessUnsigned 1 14 code.check _ _ input.slot.index input.finish
    have pure := X86StateFrame.registerOnly regs
    have ready : Ready roots map active translated original.size original.size after :=
      ⟨⟨input.slot.operands.preserved pure, input.slot.mapping.preserved pure, (regs.lookup 6 (by decide)).trans input.slot.roots,
        (regs.lookup 7 (by decide)).trans input.slot.map, (regs.lookup 1 (by decide)).trans input.slot.index,
        (regs.lookup 15 (by decide)).trans input.slot.extent⟩, (regs.lookup 14 (by decide)).trans input.finish,
        (regs.lookup 13 (by decide)).trans input.one⟩
    exact ⟨after, ∅, ran, pure.mono (by decide) (Finset.Subset.refl _), by simp [NativeMarkTable.Within],
      ready, ⟨by simpa [Comparison.evaluate] using halt⟩⟩
  | succ future ih =>
    have within : ordinal < original.size := by omega
    have activeInside : ordinal < active.size := cursor.width.symm ▸ within
    have rootFit := cursor.width ▸ input.slot.operands.fits
    have wordExact := NativeSubstitutionReserve.word_of_region roots ordinal (within.le.trans rootFit)
    have sizeExact := NativeSubstitutionReserve.word_of_region roots original.size rootFit
    obtain ⟨a, ran, regs, ⟨decision⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector point .lessUnsigned 1 14 code.check _ _ input.slot.index input.finish
    change At image a base (if decide ((BitVec.ofNat 64 ordinal).toNat < (BitVec.ofNat 64 original.size).toNat)
      then start + 9 else done) at decision
    rw [wordExact, sizeExact] at decision
    have next : At image a base (start + 9) := by simpa [within] using decision
    have pure := X86StateFrame.registerOnly regs
    have slot : Input roots map active translated ordinal a :=
      ⟨input.slot.operands.preserved pure, input.slot.mapping.preserved pure, (regs.lookup 6 (by decide)).trans input.slot.roots,
        (regs.lookup 7 (by decide)).trans input.slot.map, (regs.lookup 1 (by decide)).trans input.slot.index,
        (regs.lookup 15 (by decide)).trans input.slot.extent⟩
    have item := cursor.upcoming ordinal (Nat.le_refl _)
    rw [Array.getElem?_eq_getElem activeInside, Array.getElem?_eq_getElem within] at item
    have targetInside : ordinal < target.size := width.symm ▸ within
    let new := target[ordinal]
    have found : target[ordinal]? = some new := Array.getElem?_eq_getElem targetInside
    have move : translated[active[ordinal].toNat]? = some new := by
      rw [Option.some.inj item]
      exact (atWord ⟨ordinal, within⟩).trans found
    obtain ⟨b, steps, retargeted, readback⟩ := NativeLiveRoots.fetched_one other extra vector next
      (controls.transport pure (by decide)) code.root ⟨ordinal, activeInside⟩ slot separate (apart _)
    rw [show translated[active[ordinal].toNat]? = some new from move] at readback
    obtain ⟨rfl, replaced, stored, mapReady, ⟨atInc⟩⟩ := readback
    have throughMap := pure.trans replaced
    obtain ⟨c, increased, increasedFrame, ordinalWord, ⟨atJump⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector (show At image b base (start + 51) from atInc) (by omega)
      .add 13 1 (BitVec.ofNat 64 ordinal) 1 ((throughMap.lookup 13 (by decide)).trans input.one)
      ((throughMap.lookup 1 (by decide)).trans input.slot.index) code.increment
    have arithmetic : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [arithmetic] at increased
    have advanced : lookup c 1 = some (BitVec.ofNat 64 (ordinal + 1)) := by
      change lookup c 1 = some (BitVec.ofNat 64 ordinal + BitVec.ofNat 64 1) at ordinalWord
      rwa [BitVec.ofNat_add_ofNat] at ordinalWord
    obtain ⟨d, jumped, jumping, ⟨again⟩⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image c base (start + 54) from atJump) code.again
    have tailFrame := X86StateFrame.registerOnly (increasedFrame.trans jumping)
    let write := slotBytes roots ⟨ordinal, activeInside.trans_le slot.operands.fits⟩
    have headFrame : X86StateFrame.Frame clobbers write before d :=
      (throughMap.trans tailFrame).mono (by decide) (by
        simp only [Finset.empty_union, Finset.union_empty, write]
        exact Finset.Subset.refl _)
    have shifted : Ready roots map (active.set ordinal new activeInside) translated (ordinal + 1) original.size d :=
      ⟨⟨stored.preserved tailFrame, mapReady.preserved tailFrame, (headFrame.lookup 6 (by decide)).trans input.slot.roots,
        (headFrame.lookup 7 (by decide)).trans input.slot.map, (jumping.lookup 1 (by decide)).trans advanced,
        (headFrame.lookup 15 (by decide)).trans input.slot.extent⟩,
        (headFrame.lookup 14 (by decide)).trans input.finish, (headFrame.lookup 13 (by decide)).trans input.one⟩
    obtain ⟨after, writes, scanned, framed, confined, ready, endpoint⟩ :=
      ih _ (ordinal + 1) (by omega) (cursor.bump new activeInside found) again
        (controls.transport headFrame clobbers_data) shifted
    have limits : NativeMarkTable.Within roots ordinal original.size (write ∪ writes) := by
      intro b hit
      rcases Finset.mem_union.mp hit with this | later
      · exact ⟨⟨ordinal, activeInside.trans_le slot.operands.fits⟩, Nat.le_refl _, within, this⟩
      · obtain ⟨i, lower, upper, member⟩ := confined b later
        exact ⟨i, by omega, upper, member⟩
    have prefixRun := X86FuelPrefix.fetches_then 11 1 before c d
      (X86FuelPrefix.fetches_then 10 1 before b c (X86FuelPrefix.fetches_then 2 8 before a b ran retargeted) increased) jumped
    have ranAll := X86FuelPrefix.fetches_then 12 (12 * future + 2) before d after prefixRun scanned
    rw [show 12 + (12 * future + 2) = 12 * (future + 1) + 2 by omega] at ranAll
    exact ⟨after, write ∪ writes, ranAll,
      (headFrame.trans framed).mono (by simp) (Finset.Subset.refl _), limits, ready, endpoint⟩

/-- The completed map of a binding can move the guard pattern
and its entire occurrence vector with one native pass. -/
theorem fetched_binding_roots (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start done malformed : ℕ} (code : Placed image start done malformed)
    (separate : NativeBindingSelection.Separated map roots)
    (apart : ∀ i : Fin rc, CodeApart image base (slotBytes roots i))
    (old next : PackedGuardRoots.State) (name replacement : Word) (result : PackedSubstitution.State)
    (remap : PackedSubstitution.substitute old.arena name replacement = some result)
    (applied : PackedGuardRoots.applyBinding old name replacement = some next)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Ready roots map old.roots result.mapped 0 old.roots.size before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after writes, (X86FuelPrefix.fetches (12 * old.roots.size + 2)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ NativeMarkTable.Within roots 0 old.roots.size writes ∧
      MapReady roots next.roots after ∧ MapReady map result.mapped after ∧
      next.arena = result.target ∧ Nonempty (At image after base done) := by
  obtain ⟨same, translated⟩ := PackedGuardRoots.applyBinding_uses_one_map old next name replacement result remap applied
  obtain ⟨after, writes, ran, confined, within, ready, endpoint⟩ := fetched other extra vector
    code separate apart old.roots next.roots old.roots translated 0 old.roots.size (Nat.zero_add _) (Cursor.start _ _) point controls input
  exact ⟨after, writes, ran, confined, within, ready.slot.operands, ready.slot.mapping, same, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootLoop
