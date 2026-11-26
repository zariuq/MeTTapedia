import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionBody

/-!
# Fetched graph substitution over the original arena

The bound read by the loop is the original node count, not a
staged length. Newly built nodes therefore cannot become new
inputs to the same substitution. The loop finishes with a
complete handle map but does not publish a different agenda.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionLoop

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch Jump jumpDelta)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table)
open NativeSubstitutionMemory (Geometry Includes)
open NativeSubstitutionChanged renaming State → RemapState
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start done exhausted malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 1 15 start done ++
    (NativeSubstitutionBody.emit (start + 9) exhausted malformed ++
      (NativeOccursLoop.incrementCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 550) start)))

theorem emit_size (start done exhausted malformed : ℕ) : (emit start done exhausted malformed).length = 555 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, NativeSubstitutionBody.emit_size,
    X86UnconditionalJump.Block.code_length, show NativeOccursLoop.incrementCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start done exhausted malformed : ℕ) : Prop where
  extent : start + 555 ≤ image.size
  check : CompareBranch image start done .lessUnsigned 1 15
  body : NativeSubstitutionBody.Placed image (start + 9) exhausted malformed
  increment : Code image (start + 547) NativeOccursLoop.incrementCode
  again : Jump image (start + 550) start

theorem placed_of_emitted (image : NativeImage.View) (start done exhausted malformed : ℕ)
    (extent : start + 555 ≤ image.size) (complete : done ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start done exhausted malformed)) : Placed image start done exhausted malformed := by
  obtain ⟨check, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 1 15 start done ++ _) from code)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨body, rest⟩ := NativeWords.code_append rest
  rw [NativeSubstitutionBody.emit_size] at rest
  obtain ⟨increment, again⟩ := NativeWords.code_append rest
  refine ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) complete short check,
    NativeSubstitutionBody.placed_of_emitted image _ exhausted malformed (by omega) lack bad short body,
    increment, ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := insert .rcx NativeSubstitutionBody.clobbers
private abbrev cursorClobbers : Finset Register := {.rcx, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {agenda : NativeAgendaRecords.Layout agendaCapacity}
variable {source target : PackedTerms.Arena} {mapping : Array Word} {original query replacement : Word}

private theorem with_cursor {before after : Native}
    (ready : RemapState layout map frame agenda source target mapping original query replacement before)
    (run : X86StateFrame.Frame cursorClobbers ∅ before after) (cursor : Word)
    (known : lookup after 1 = some cursor) :
    RemapState layout map frame agenda source target mapping cursor query replacement after :=
  ⟨ready.extension, ready.terms.preserved run, ready.staged.preserved run (by decide),
    ready.mapped.preserved run, (run.lookup 3 (by decide)).trans ready.nodes,
    (run.lookup 5 (by decide)).trans ready.agendaBase, ready.pool.preserved run (by simp),
    (run.lookup 7 (by decide)).trans ready.tableBase, known,
    (run.lookup 8 (by decide)).trans ready.query, (run.lookup 9 (by decide)).trans ready.replacement,
    (run.lookup 12 (by decide)).trans ready.zero, (run.lookup 13 (by decide)).trans ready.one⟩

structure Ready (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (agenda : NativeAgendaRecords.Layout agendaCapacity) (source : PackedTerms.Arena)
    (packed : PackedSubstitution.State) (query replacement : Word) (native : Native) : Prop where
  stage : RemapState layout map frame agenda source packed.target packed.mapped
    (BitVec.ofNat 64 packed.mapped.size) query replacement native
  endCount : lookup native 15 = some (BitVec.ofNat 64 source.nodes.size)
  two : lookup native 14 = some 2

/-- A successful packed traversal has a complete fetched
realization when its final extents fit. No condition on a future
staged node is tested by the loop bound. -/
theorem fetched_all (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done exhausted malformed : ℕ}
    (placed : Placed image start done exhausted malformed) (geometry : Geometry layout map frame agenda image base)
    (source : PackedTerms.Arena) (query replacement : Word) (remaining : ℕ)
    (old result : PackedSubstitution.State)
    (run : PackedSubstitution.scan source query replacement remaining old = some result)
    (visits : old.mapped.size + remaining = source.nodes.size) (mapFit : source.nodes.size ≤ mapCapacity)
    (nodesFit : result.target.nodes.size ≤ nodeCapacity) (edgesFit : result.target.children.size ≤ edgeCapacity)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (ready : Ready layout map frame agenda source old query replacement before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps writes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Includes layout map frame writes ∧
      Ready layout map frame agenda source result query replacement after ∧
      result.mapped.size = source.nodes.size ∧ Nonempty (At image after base done) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction remaining generalizing old before with
  | zero =>
    obtain rfl := Option.some.inj run
    obtain ⟨after, ran, regs, ⟨stops⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 1 15 placed.check _ _
      ready.stage.cursor ready.endCount
    have size : old.mapped.size = source.nodes.size := by omega
    rw [size] at stops
    have stop : At image after base done := by simpa [Comparison.evaluate] using stops
    have readOnly := X86StateFrame.registerOnly regs
    refine ⟨after, 2, ∅, ran, readOnly.mono (by decide) (Finset.Subset.refl _),
      Includes.empty layout map frame, ⟨?_, (regs.lookup 15 (by decide)).trans ready.endCount,
        (regs.lookup 14 (by decide)).trans ready.two⟩, size, ⟨stop⟩⟩
    exact with_cursor ready.stage (readOnly.mono (by decide) (Finset.Subset.refl _)) _
      ((regs.lookup 1 (by decide)).trans ready.stage.cursor)
  | succ n ih =>
    obtain ⟨mid, reaches, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨handle, rewritten, mapped⟩ := NativeRemapSnapshot.advance_readout source query replacement old mid reaches
    have remainingFits : old.mapped.size < source.nodes.size := by omega
    have ord := NativeSubstitutionReserve.word_of_region map old.mapped.size (remainingFits.le.trans mapFit)
    have total := (NativeRemapSnapshot.ready_restrict ready.stage.extension ready.stage.terms).count_word
    obtain ⟨a, checked, cmp, ⟨atDecision⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 1 15 placed.check _ _
      ready.stage.cursor ready.endCount
    change At image a base (if decide ((BitVec.ofNat 64 old.mapped.size).toNat <
      (BitVec.ofNat 64 source.nodes.size).toNat) then start + 9 else done) at atDecision
    rw [ord, total] at atDecision
    have atBody : At image a base (start + 9) := by simpa [remainingFits] using atDecision
    have checkedFrame := X86StateFrame.registerOnly cmp
    have selected := with_cursor ready.stage (checkedFrame.mono (by decide) (Finset.Subset.refl _)) _
      ((cmp.lookup 1 (by decide)).trans ready.stage.cursor)
    have extension := (NativeRemapSnapshot.scan_extends source query replacement n mid result rest).1
    obtain ⟨b, work, writes, executed, bodyFrame, privateWrites, advanced, tagTwo, ⟨atIncrement⟩⟩ :=
      NativeSubstitutionBody.fetched other extra vector atBody (controls.transport checkedFrame (by decide)) placed.body
        geometry selected ((cmp.lookup 14 (by decide)).trans ready.two) (by simpa only [ord] using remainingFits)
        ord (remainingFits.trans_le mapFit) mid.target handle rewritten (extension.node_size.trans nodesFit)
        (extension.edge_size.trans edgesFit)
    have extent := placed.extent
    obtain ⟨c, increased, increasedFrame, ordinal, ⟨atJump⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector (show At image b base (start + 547) from atIncrement)
      (by omega) .add 13 1 (BitVec.ofNat 64 old.mapped.size) 1 advanced.one advanced.cursor placed.increment
    have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [ordinary] at increased
    have newCursor : lookup c 1 = some (BitVec.ofNat 64 mid.mapped.size) := by
      change lookup c 1 = some (BitVec.ofNat 64 old.mapped.size + BitVec.ofNat 64 1) at ordinal
      rw [mapped, Array.size_push, ← BitVec.ofNat_add_ofNat]
      exact ordinal
    obtain ⟨d, jumped, jumping, ⟨atAgain⟩⟩ := X86PlacedScalar.jump
      (X86PlacedFrameAddress.nativeBase other) extra vector
      (show At image c base (start + 550) from atJump) placed.again
    have tail := X86StateFrame.registerOnly (increasedFrame.trans jumping)
    have trace : X86StateFrame.Frame clobbers writes before d :=
      (((checkedFrame.trans bodyFrame).trans tail)).mono (by decide) (by simp)
    have next : Ready layout map frame agenda source mid query replacement d := by
      refine ⟨?_, (trace.lookup 15 (by decide)).trans ready.endCount, (tail.lookup 14 (by decide)).trans tagTwo⟩
      rw [mapped]
      exact with_cursor advanced (tail.mono (by decide) (Finset.Subset.refl _)) _
        ((jumping.lookup 1 (by decide)).trans (mapped ▸ newCursor))
    have nextVisits : mid.mapped.size + n = source.nodes.size := by
      rw [mapped, Array.size_push]
      omega
    obtain ⟨after, more, later, finished, lateFrame, privateTail, finalReady, count, endpoint⟩ :=
      ih mid rest nextVisits atAgain (controls.transport trace clobbers_data) next
    have step := X86FuelPrefix.fetches_then 2 work before a b checked executed
    have loop := X86FuelPrefix.fetches_then (2 + work + 1) 1 before c d
      (X86FuelPrefix.fetches_then (2 + work) 1 before b c step increased) jumped
    exact ⟨after, _, writes ∪ later, X86FuelPrefix.fetches_then _ more before d after loop finished,
      (trace.trans lateFrame).mono (by simp) (Finset.Subset.refl _), privateWrites.union privateTail,
      finalReady, count, endpoint⟩

/-- Starting with the reused scratch table at initialized length
zero produces exactly the packed substitution, retaining the
entire old agenda as a readable snapshot. -/
theorem fetched_substitute (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done exhausted malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done exhausted malformed)
    (geometry : Geometry layout map frame agenda image base)
    (source : PackedTerms.Arena) (query replacement : Word) (result : PackedSubstitution.State)
    (run : PackedSubstitution.substitute source query replacement = some result)
    (mapFit : source.nodes.size ≤ mapCapacity)
    (nodesFit : result.target.nodes.size ≤ nodeCapacity) (edgesFit : result.target.children.size ≤ edgeCapacity)
    (ready : Ready layout map frame agenda source ⟨source, #[]⟩ query replacement before)
    (equations : PackedEquations.Arena) (live : NativeAgendaRecords.Ready agenda equations before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps writes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers writes before after ∧ Includes layout map frame writes ∧
      Ready layout map frame agenda source result query replacement after ∧
      result.mapped.size = source.nodes.size ∧ NativeAgendaRecords.Ready agenda equations after ∧
      Nonempty (At image after base done) := by
  obtain ⟨after, fuel, writes, fetched, framed, staging, initialized, count, reached⟩ :=
    fetched_all other extra vector placed geometry source query replacement source.nodes.size ⟨source, #[]⟩
      result run (by simp) mapFit nodesFit edgesFit point controls ready
  exact ⟨after, fuel, writes, fetched, framed, staging, initialized, count, geometry.agenda_kept live framed staging, reached⟩

namespace Examples

private def sharedSource : PackedTerms.Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 2⟩, ⟨⟨2, 2⟩, 2, 2⟩], #[0, 1, 2, 2]⟩

/-- Two uses of a changed child still name one child, while
both edge occurrences survive. This is a fixture for the
packed result the native scan must realize. -/
theorem sharing_does_not_erase_an_edge_occurrence :
    (PackedSubstitution.substitute sharedSource 7 1).map
      (fun output => (output.target.nodes.size, output.target.children, output.mapped)) =
    some (6, #[0, 1, 2, 2, 1, 1, 4, 4], #[1, 1, 4, 5]) := by
  decide +kernel

private def forwardSource : PackedTerms.Arena :=
  ⟨#[⟨⟨2, 1⟩, 0, 1⟩, ⟨⟨1, 42⟩, 0, 0⟩], #[1]⟩

theorem future_map_entry_is_not_an_input :
    (PackedSubstitution.substitute forwardSource 7 1).isNone = true := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionLoop
