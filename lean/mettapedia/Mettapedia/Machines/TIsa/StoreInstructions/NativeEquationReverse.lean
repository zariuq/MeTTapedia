import Mettapedia.Machines.TIsa.StoreInstructions.NativeRegisterCopies
import Mettapedia.Machines.TIsa.StoreInstructions.NativePendingFill

/-!
# Transferring a newest-first equation chain into solver order

The reader follows the original links and the writer pushes
each pair onto the staged destination. The newest occurrence
is visited first, hence it comes last in the result. Only the
new suffix is written; the snapshot's count stays unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationReverse

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint)
open X86PlacedScalar (Code Jump jumpDelta)
open NativeRegisterCopies (Copy Values)
open NativeAgendaRecords (Ready Records)
open NativeAgendaLoop (Within)
open PackedEquations (Arena Node readWords prependWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def prepare : List Copy := [⟨11, 3⟩, ⟨0, 11⟩, ⟨1, 9⟩, ⟨2, 10⟩]
def restore : List Copy := [⟨11, 0⟩, ⟨3, 11⟩]

def emit (start done malformed : ℕ) : List ℕ :=
  NativeAgendaRead.emit start done malformed ++ (NativeRegisterCopies.emit prepare ++
    (NativeAgendaInsert.emit ++ (NativeRegisterCopies.emit restore ++ X86UnconditionalJump.Block.code (jumpDelta (start + 131) start))))

theorem emit_size (start done malformed : ℕ) : (emit start done malformed).length = 136 := by
  simp only [emit, List.length_append, NativeAgendaRead.emit_size, NativeRegisterCopies.emit_size, NativeAgendaInsert.emit_size,
    X86UnconditionalJump.Block.code_length, show prepare.length = 4 from rfl, show restore.length = 2 from rfl]

structure Placed (image : NativeImage.View) (start done malformed : ℕ) : Prop where
  extent : start + 136 ≤ image.size
  read : NativeAgendaRead.Placed image start done malformed
  prepare : Code image (start + 72) (NativeRegisterCopies.emit prepare)
  push : NativeAgendaInsert.Placed image (start + 84)
  restore : Code image (start + 125) (NativeRegisterCopies.emit restore)
  again : Jump image (start + 131) start

theorem placed_of_emitted (image : NativeImage.View) (start done malformed : ℕ)
    (extent : start + 136 ≤ image.size) (finish : done ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31) (code : Code image start (emit start done malformed)) :
    Placed image start done malformed := by
  obtain ⟨read, rest⟩ := NativeWords.code_append (show Code image start
    (NativeAgendaRead.emit start done malformed ++ _) from code)
  rw [NativeAgendaRead.emit_size] at rest
  obtain ⟨pre, rest⟩ := NativeWords.code_append rest
  rw [NativeRegisterCopies.emit_size] at rest
  obtain ⟨push, rest⟩ := NativeWords.code_append rest
  rw [NativeAgendaInsert.emit_size] at rest
  obtain ⟨post, again⟩ := NativeWords.code_append rest
  rw [NativeRegisterCopies.emit_size] at again
  refine ⟨extent, NativeAgendaRead.placed_of_emitted image _ _ malformed (by omega) finish bad short read, pre,
    NativeAgendaInsert.placed_of_emitted image _ (by omega) push, post, ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {cap : ℕ} {layout : NativeAgendaRecords.Layout cap}
variable {image : NativeImage.View} {base : BitVec 48} {start done malformed : ℕ}

structure Input (layout : NativeAgendaRecords.Layout cap) (source stage : Arena)
    (cursor accumulated : Word) (native : Native) : Prop where
  source : Ready layout source native
  records : Records layout stage native
  base : lookup native 5 = some layout.words.pointer
  cursor : lookup native 11 = some cursor
  length : lookup native 14 = some (BitVec.ofNat 64 stage.size)
  accumulated : lookup native 0 = some accumulated
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

private def put (v : Values) (i : Fin 16) (word : Word) : Values := Function.update v i (some word)
private def prepIn (origin accumulated l r : Word) : Values :=
  put (put (put (put (fun _ => none) 11 origin) 0 accumulated) 1 l) 2 r
private def prepOut (origin accumulated l r : Word) : Values :=
  put (put (put (put (prepIn origin accumulated l r) 3 origin) 11 accumulated) 9 l) 10 r
private theorem prep_exact (o a l r : Word) :
    NativeRegisterCopies.interpret prepare (prepIn o a l r) = some (prepOut o a l r) := rfl
private def restoreIn (after tail : Word) : Values := put (put (fun _ => none) 11 after) 3 tail
private def restoreOut (after tail : Word) : Values := put (put (restoreIn after tail) 0 after) 11 tail
private theorem restore_exact (after tail : Word) :
    NativeRegisterCopies.interpret restore (restoreIn after tail) = some (restoreOut after tail) := rfl

private theorem older_kept {before after : Native} {regs : Finset Register} {bytes : Finset ℕ}
    {source : Arena} {lo hi : ℕ} (ready : Ready layout source before) (lower : source.size ≤ lo)
    (run : X86StateFrame.Frame regs bytes before after) (writes : Within layout lo hi bytes) :
    Ready layout source after :=
  ⟨ready.fits, ready.count.preserved run (NativeAgendaLoop.Within.preserves_count writes),
    fun i j => (ready.node i j).preserved run (NativePendingFill.Within.separate writes _ (fun d col bound _ =>
      layout.records_apart _ d (i.isLt.trans_le (lower.trans bound)) j col))⟩

theorem fetched_one (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (code : Placed image start done malformed)
    (writable : ∀ i j, CodeApart image base (footprint ((layout.record i).cell j).address))
    (source stage : Arena) (cursor accumulated : Word) (pair : Word × Word) (pending recorded : Words)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout source stage cursor accumulated before)
    (known : readWords source cursor = some (pair :: pending))
    (leading : readWords stage accumulated = some recorded)
    (prefixBound : source.size ≤ stage.size) (room : stage.size < cap) :
    let node : Node := ⟨accumulated, pair.1, pair.2⟩
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after writes older, (X86FuelPrefix.fetches 31).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Within layout stage.size (stage.size + 1) writes ∧
      Input layout source (stage.push node) older (PackedEquations.next stage) after ∧ readWords source older = some pending ∧
      prependWords stage accumulated [pair] = some (stage.push node, PackedEquations.next stage) ∧
      readWords (stage.push node) (PackedEquations.next stage) = some (pair :: recorded) ∧ Nonempty (At image after base start) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let node : Node := ⟨accumulated, pair.1, pair.2⟩
  have extent := code.extent
  obtain ⟨old, picked, equal, nextRead⟩ := NativeAgendaRecords.top_of_read source cursor (pair :: pending) known
  obtain ⟨a, read, readFrame, atPair⟩ := NativeAgendaRead.fetched other extra vector point controls
    code.read input.source input.base cursor input.cursor input.zero
  simp only [NativeAgendaRead.Arrival, picked] at atPair
  rw [NativeAgendaRead.cost_pop _ _ old picked] at read
  obtain ⟨previous, left, right, ⟨atPrep⟩⟩ := atPair
  have knownLeft : lookup a 1 = some pair.1 := (congrArg Prod.fst equal) ▸ left
  have knownRight : lookup a 2 = some pair.2 := (congrArg Prod.snd equal) ▸ right
  have src := (NativeRegisterCopies.Ready.empty a).set 11 old.older previous
  have dest := src.set 0 accumulated ((readFrame.lookup 0 (by decide)).trans input.accumulated)
  have lhs := dest.set 1 pair.1 knownLeft
  have values : NativeRegisterCopies.Ready (prepIn old.older accumulated pair.1 pair.2) a := lhs.set 2 pair.2 knownRight
  obtain ⟨b, prepared, shuffle, roles, ⟨atPush⟩⟩ := NativeRegisterCopies.fetched other extra vector
    atPrep prepare (by change start + 72 + 12 ≤ image.size; omega) code.prepare _ _ values (prep_exact _ _ _ _)
  have throughPrep : X86StateFrame.Frame (NativeAgendaRead.clobbers ∪ NativeRegisterCopies.clobbers prepare) ∅ before b :=
    (readFrame.trans shuffle).mono (Finset.Subset.refl _) (by simp)
  have staged : Records layout stage b :=
    ⟨input.records.fits, fun i j => (input.records.node i j).preserved throughPrep (by simp)⟩
  have operands : NativeAgendaInsert.Inputs layout stage node b :=
    ⟨staged, (throughPrep.lookup 5 (by decide)).trans input.base, (throughPrep.lookup 14 (by decide)).trans input.length,
      (throughPrep.lookup 13 (by decide)).trans input.one, roles 11 accumulated rfl, roles 9 pair.1 rfl, roles 10 pair.2 rfl⟩
  let writes := NativeAgendaInsert.footprintOf layout stage room node
  have confined : Within layout stage.size (stage.size + 1) writes := by
    intro byte changed
    obtain ⟨j, actual⟩ := NativeAgendaInsert.footprint_member _ _ _ _ changed
    exact ⟨⟨stage.size, room⟩, j, Nat.le_refl _, Nat.lt_succ_self _, actual⟩
  have protectedSpace : CodeApart image base writes := by
    intro i word located changed
    obtain ⟨d, col, _, _, inside⟩ := confined _ changed
    exact writable d col i word located inside
  have olderBound := PackedEquations.read_bound PackedEquations.wordCodes stage accumulated leading
  obtain ⟨c, pushed, pushFrame, now, count, newRoot, actual, ⟨atRestore⟩⟩ := NativeAgendaInsert.fetched other extra vector
    (show At image b base (start + 84) from atPush) (controls.transport throughPrep (by decide))
    code.push node operands room recorded leading olderBound protectedSpace
  have throughPush := throughPrep.trans pushFrame
  have pushedRoot := (NativeRegisterCopies.Ready.empty c).set 11 (PackedEquations.next stage) newRoot
  have resume : NativeRegisterCopies.Ready (restoreIn (PackedEquations.next stage) old.older) c :=
    pushedRoot.set 3 old.older ((pushFrame.lookup 3 (by decide)).trans (roles 3 old.older rfl))
  obtain ⟨d, restored, restoreFrame, returned, ⟨atJump⟩⟩ := NativeRegisterCopies.fetched other extra vector
    atRestore restore (by change start + 125 + 6 ≤ image.size; omega) code.restore _ _ resume (restore_exact _ _)
  obtain ⟨after, hopped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image d base (start + 131) from atJump) code.again
  have tailFrame : X86StateFrame.Frame (NativeRegisterCopies.clobbers restore ∪ {.rip}) ∅ c after :=
    (restoreFrame.trans (X86StateFrame.registerOnly jumpFrame)).mono (Finset.Subset.refl _) (by simp)
  have all : X86StateFrame.Frame clobbers writes before after :=
    (throughPush.trans tailFrame).mono (by decide) (by
      simp only [Finset.empty_union, Finset.union_empty, writes]
      exact Finset.Subset.refl _)
  have final : Input layout source (stage.push node) old.older (PackedEquations.next stage) after :=
    ⟨older_kept input.source prefixBound all confined, ⟨now.fits, fun i j => (now.node i j).preserved tailFrame (by simp)⟩,
      (all.lookup 5 (by decide)).trans input.base, (jumpFrame.lookup 11 (by decide)).trans (returned 11 old.older rfl),
      (tailFrame.lookup 14 (by decide)).trans (by simpa only [Array.size_push, PackedEquations.next] using count),
      (jumpFrame.lookup 0 (by decide)).trans (returned 0 (PackedEquations.next stage) rfl),
      (all.lookup 12 (by decide)).trans input.zero, (all.lookup 13 (by decide)).trans input.one⟩
  have sizeLimit := layout.words.positive_room (show 0 < 3 * (cap + 1) by omega)
  have fits : PackedEquations.CanAppend stage accumulated := ⟨olderBound, by omega⟩
  have packed : prependWords stage accumulated [pair] = some (stage.push node, PackedEquations.next stage) := by
    rcases pair with ⟨l, r⟩
    simp only [prependWords, bind, Option.bind_some, PackedEquations.append, if_pos fits, node]
  have ran := X86FuelPrefix.fetches_then 30 1 before d after
    (X86FuelPrefix.fetches_then 28 2 before c d
      (X86FuelPrefix.fetches_then 19 9 before b c
        (X86FuelPrefix.fetches_then 15 4 before a b read prepared) pushed) restored) hopped
  exact ⟨after, writes, old.older, ran, all, confined, final, nextRead, packed, actual, endpoint⟩

/-- Reversing into the private suffix performs one iteration
per source record and does not rewrite any previous link. -/
theorem fetched_all (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (code : Placed image start done malformed)
    (writable : ∀ i j, CodeApart image base (footprint ((layout.record i).cell j).address))
    (source stage : Arena) (cursor accumulated : Word) (pending recorded : Words)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout source stage cursor accumulated before)
    (known : readWords source cursor = some pending) (leading : readWords stage accumulated = some recorded)
    (prefixBound : source.size ≤ stage.size) (room : stage.size + pending.length ≤ cap) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after updated head writes, (X86FuelPrefix.fetches (31 * pending.length + 2)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Within layout stage.size updated.size writes ∧
      Input layout source updated 0 head after ∧ updated.size = stage.size + pending.length ∧
      prependWords stage accumulated pending.reverse = some (updated, head) ∧
      readWords updated head = some (pending.reverse ++ recorded) ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction pending generalizing stage cursor accumulated recorded before with
  | nil =>
    have empty := NativeAgendaRecords.top_of_read source cursor [] known
    have zero := NativeAgendaRead.empty_cursor source cursor empty
    subst cursor
    obtain ⟨after, ran, framed, endpoint⟩ := NativeAgendaRead.fetched other extra vector point controls code.read
      input.source input.base 0 input.cursor input.zero
    rw [NativeAgendaRead.cost_empty _ _ empty] at ran
    simp only [NativeAgendaRead.Arrival, empty] at endpoint
    have next : Input layout source stage 0 accumulated after :=
      ⟨input.source.preserved framed, ⟨input.records.fits, fun i j => (input.records.node i j).preserved framed (by simp)⟩,
        (framed.lookup 5 (by decide)).trans input.base, endpoint.1, (framed.lookup 14 (by decide)).trans input.length,
        (framed.lookup 0 (by decide)).trans input.accumulated, (framed.lookup 12 (by decide)).trans input.zero,
        (framed.lookup 13 (by decide)).trans input.one⟩
    exact ⟨after, stage, accumulated, ∅, ran, framed.mono (by decide) (Finset.Subset.refl _), by simp [Within],
      next, by simp, rfl, leading, endpoint.2⟩
  | cons first pending ih =>
    have stages : stage.size + pending.length + 1 ≤ cap := by simpa only [List.length_cons, Nat.add_assoc] using room
    obtain ⟨middle, firstWrites, older, took, framed, confined, next, sourceTail, inserted, headRead, ⟨again⟩⟩ :=
      fetched_one other extra vector code writable source stage cursor accumulated first pending recorded point controls input
        known leading prefixBound (by omega)
    let advanced := stage.push ⟨accumulated, first.1, first.2⟩
    have increased : advanced.size = stage.size + 1 := Array.size_push _
    obtain ⟨after, updated, root, writes, scanned, scanFrame, scanWrites, ready, width, output, exactRead, endpoint⟩ :=
      ih advanced older (PackedEquations.next stage) (first :: recorded) again
        (controls.transport framed clobbers_data) next sourceTail headRead (by omega) (by omega)
    have size : updated.size = stage.size + (first :: pending).length := by simp only [List.length_cons]; omega
    have confinedAll : Within layout stage.size updated.size (firstWrites ∪ writes) := by
      intro byte touched
      rcases Finset.mem_union.mp touched with early | late
      · obtain ⟨i, j, low, high, held⟩ := confined byte early
        exact ⟨i, j, low, by omega, held⟩
      · obtain ⟨i, j, low, high, held⟩ := scanWrites byte late
        exact ⟨i, j, by omega, high, held⟩
    have structureExact : prependWords stage accumulated (first :: pending).reverse = some (updated, root) := by
      rw [List.reverse_cons, PackedEquations.prepend_words_append, inserted]
      exact output
    have ran := X86FuelPrefix.fetches_then 31 _ before middle after took scanned
    have cost : 31 + (31 * pending.length + 2) = 31 * (first :: pending).length + 2 := by simp only [List.length_cons]; omega
    rw [cost] at ran
    exact ⟨after, updated, root, firstWrites ∪ writes, ran,
      (framed.trans scanFrame).mono (by simp) (Finset.Subset.refl _), confinedAll, ready, size,
      structureExact, by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using exactRead, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationReverse
