import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstLeaf

/-!
# Resetting the scratch phase and reserving a whole handle map

The occurrence pass needed room only through its target.
Substitution visits the original arena, so it must check the
full initialized count against the same resident capacity.
After the check, resetting the cursor starts the map's empty
initialized prefix without clearing any old mark words.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch)
open NativeAgendaRead (fieldSource)
open NativeArenaGeometry (Region)
open NativeBindEntry (frameCode tableCode capacityCode zeroCode tableWire capacityWire)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start exhausted : ℕ) : List ℕ :=
  frameCode ++ (tableCode ++ (capacityCode ++
    (NativeDecisions.compareBytes .lessEqualUnsigned 15 2 (start + 17) exhausted ++ zeroCode)))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 29 := rfl

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 29 ≤ image.size
  context : Code image start frameCode
  table : Code image (start + 3) tableCode
  capacity : Code image (start + 10) capacityCode
  reserve : CompareBranch image (start + 17) exhausted .lessEqualUnsigned 15 2
  zero : Code image (start + 26) zeroCode

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (extent : start + 29 ≤ image.size) (target : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨context, rest⟩ := NativeWords.code_append (show Code image start (frameCode ++ _) from installed)
  obtain ⟨table, rest⟩ := NativeWords.code_append rest
  obtain ⟨capacity, rest⟩ := NativeWords.code_append rest
  change Code image (start + 17) _ at rest
  obtain ⟨reserve, zero⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at zero
  exact ⟨extent, context, table, capacity,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short reserve, zero⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := NativeBindEntry.setupClobbers

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    {nodeCapacity edgeCapacity agendaCapacity mapCapacity : ℕ}
    {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
    {agendaLayout : NativeAgendaRecords.Layout agendaCapacity} {table : Region mapCapacity}
    (descriptor : WordRegion.Region 2) (input : NativeBindEntry.Environment layout arena agendaLayout table descriptor before)
    (size : lookup before 15 = some (BitVec.ofNat 64 arena.nodes.size)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if arena.nodes.size ≤ mapCapacity then
        steps = 6 ∧ lookup after 1 = some 0 ∧ lookup after 7 = some (table.atWord 0) ∧
          MapReady table #[] after ∧ Nonempty (At image after base (start + 29))
      else steps = 5 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  have capacityExact : (BitVec.ofNat 64 mapCapacity).toNat = mapCapacity := by
    by_cases pos : 0 < mapCapacity
    · have bound := table.positive_room pos
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [show mapCapacity = 0 by omega]
      rfl
  obtain ⟨a, moved, opened, pointer, ⟨atTable⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
    point (by omega) 4 6 descriptor.pointer input.stack placed.context
  have movedFrame := X86StateFrame.registerOnly opened
  obtain ⟨b, loadedTable, tableFrame, tablePointer, ⟨atCapacity⟩⟩ := (fieldSource descriptor 0).fetch
    (handlers other extra) vector tableWire (table.atWord 0) atTable (controls.transport movedFrame (by decide))
    pointer (input.markTable.preserved movedFrame (by simp)) (show start + 10 ≤ image.size by omega) placed.table
  have two := movedFrame.trans tableFrame
  obtain ⟨c, loadedLimit, limitFrame, limit, ⟨atTest⟩⟩ := (fieldSource descriptor 1).fetch
    (handlers other extra) vector capacityWire (BitVec.ofNat 64 mapCapacity)
    (show At image b base (start + 10) from atCapacity) (controls.transport two (by decide))
    ((tableFrame.lookup 6 (by decide)).trans pointer) (input.capacity.preserved two (by simp))
    (show start + 17 ≤ image.size by omega) placed.capacity
  rw [linked] at loadedTable loadedLimit
  have three := two.trans limitFrame
  obtain ⟨d, tested, testFrame, ⟨atSpace⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 17) from atTest) .lessEqualUnsigned 15 2 placed.reserve _ _
    ((three.lookup 15 (by decide)).trans size) limit
  change At image d base (if decide ((BitVec.ofNat 64 arena.nodes.size).toNat ≤ (BitVec.ofNat 64 mapCapacity).toNat)
    then start + 17 + 9 else exhausted) at atSpace
  rw [input.source.count_word, capacityExact] at atSpace
  have five := three.trans (X86StateFrame.registerOnly testFrame)
  have throughTwo := X86FuelPrefix.fetches_then 1 1 before a b moved loadedTable
  have throughThree := X86FuelPrefix.fetches_then 2 1 before b c throughTwo loadedLimit
  have checked := X86FuelPrefix.fetches_then 3 2 before c d throughThree tested
  by_cases fits : arena.nodes.size ≤ mapCapacity
  · simp only [fits, decide_true, if_true] at atSpace
    obtain ⟨after, reset, resetFrame, zero, endpoint⟩ := X86PlacedRegisterMove.executes (handlers other extra)
      vector (show At image d base (start + 26) from atSpace) (by omega) 12 1 0
      ((five.lookup 12 (by decide)).trans input.zero) placed.zero
    have tableKept := ((limitFrame.trans (X86StateFrame.registerOnly (testFrame.trans resetFrame))).lookup 7 (by decide)).trans
      tablePointer
    refine ⟨after, 6, X86FuelPrefix.fetches_then 5 1 before d after checked reset,
      (five.trans (X86StateFrame.registerOnly resetFrame)).mono (by decide) (by simp), ?_⟩
    rw [if_pos fits]
    exact ⟨rfl, zero, tableKept, NativeSubstLeaf.empty_on_reuse _ _, endpoint⟩
  · simp only [fits, decide_false] at atSpace
    refine ⟨d, 5, checked, five.mono (by decide) (by simp), ?_⟩
    rw [if_neg fits]
    exact ⟨rfl, ⟨atSpace⟩⟩

theorem one_mark_slot_need_not_hold_the_remap :
    (0 : Word).toNat < 1 ∧ ¬ (2 : ℕ) ≤ 1 := by decide +kernel

open Mettapedia.Logic.LP

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- From an actual accepted agenda binding to the first remap
iteration, without clearing scratch or reconstructing the agenda. -/
theorem fetched_enter_remap (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {entry done shared cycle exhausted : ℕ}
    {targets : NativeTermDispatch.Targets} {before : Native}
    (point : At image before base entry) (controls : Controls before) (side : NativeBindEntry.Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (reserveCode : Placed image (shared + 273) exhausted)
    {nodeCapacity edgeCapacity agendaCapacity mapCapacity : ℕ}
    {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
    {agendaLayout : NativeAgendaRecords.Layout agendaCapacity} {table : Region mapCapacity}
    {descriptor : WordRegion.Region 2}
    (geometry : NativeOccursLoop.Geometry layout agendaLayout table image base)
    (agendaApart : NativeBindingSelection.Separated agendaLayout.words table)
    (descriptorApart : NativeBindingSelection.Separated (NativeBindingSelection.descriptorRegion descriptor) table)
    (agenda : PackedEquations.Arena) (root left right : Word) (history : PackedWorklist.Words)
    (context : NativeAgendaDispatch.Context agendaLayout layout agenda arena root before)
    (environment : NativeBindEntry.Environment layout arena agendaLayout table descriptor before)
    (held : PackedEquations.readWords agenda root = some ((left, right) :: history))
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols arena left = some lTerm) (rightRead : PackedTerms.lookup symbols arena right = some rTerm)
    (routed : NativeTermDispatch.choose arena left right = side.exiting)
    (query replacement : Word) (accepted : PackedUnifierAction.inspect arena left right = some (.bindVar query replacement))
    (room : arena.nodes.size ≤ mapCapacity) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps writes cursor, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (NativeBindingSelection.clobbers ∪ clobbers) writes before after ∧
      NativeMarkTable.Within table 0 (replacement.toNat + 1) writes ∧
      NativeAgendaDispatch.Context agendaLayout layout agenda arena cursor after ∧
      PackedEquations.readWords agenda cursor = some history ∧
      lookup after 1 = some 0 ∧ lookup after 7 = some (table.atWord 0) ∧
      lookup after 8 = some query ∧ lookup after 9 = some replacement ∧
      MapReady table #[] after ∧ Nonempty (At image after base (shared + 273 + 29)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨choice, marked, cost, ran, outcome⟩ := NativeBindingSelection.fetched_binding other extra vector
    point controls side agendaCode entryCode gateCode geometry agendaApart descriptorApart agenda root left right
    history context environment held symbols lTerm rTerm leftRead rightRead routed
  have target := choice.resolved
  obtain ⟨decoded, parsed, read⟩ := Option.bind_eq_some_iff.mp target
  have live := (Array.getElem?_eq_some_iff.mp read).choose
  rw [PackedTerms.decode_size symbols arena parsed] at live
  have targetRoom := live.trans_le room
  rw [if_pos targetRoom] at outcome
  obtain ⟨writes, cursor, bindingFrame, _, tail, confined, ready, env, _, name, replacementReg, ⟨endpoint⟩⟩ := outcome
  have outcomeEq := Option.some.inj (choice.inspection.symm.trans accepted)
  have noncyclic : choice.term.occursIn choice.name = false := by
    cases cyclic : choice.term.occursIn choice.name
    · rfl
    · simp [cyclic] at outcomeEq
  rw [noncyclic] at outcomeEq
  have pair := PackedUnifierAction.Encoded.bindVar.inj outcomeEq
  have acceptedAt : At image marked base (shared + 273) := by
    simpa only [noncyclic, Bool.false_eq_true, if_false] using endpoint
  obtain ⟨after, steps, reserved, reserveFrame, reset⟩ := fetched other extra vector acceptedAt
    (controls.transport bindingFrame (by decide)) reserveCode descriptor env ready.termCount
  rw [if_pos room] at reset
  obtain ⟨rfl, zero, tableBase, empty, doneAt⟩ := reset
  refine ⟨after, cost + 6, writes, cursor, X86FuelPrefix.fetches_then cost 6 before marked after ran reserved,
    (bindingFrame.trans reserveFrame).mono (Finset.Subset.refl _) (by simp), by simpa only [pair.2] using confined, ?_,
    tail, zero, tableBase, ?_, ?_, empty, doneAt⟩
  · exact ⟨ready.agendaReady.preserved reserveFrame, ready.termReady.preserved reserveFrame,
      (reserveFrame.lookup 5 (by decide)).trans ready.agendaBase,
      (reserveFrame.lookup 3 (by decide)).trans ready.termBase, (reserveFrame.lookup 11 (by decide)).trans ready.cursor,
      (reserveFrame.lookup 15 (by decide)).trans ready.termCount, (reserveFrame.lookup 12 (by decide)).trans ready.zero,
      (reserveFrame.lookup 13 (by decide)).trans ready.one, (reserveFrame.lookup 14 (by decide)).trans ready.two⟩
  · rw [← pair.1]
    exact (reserveFrame.lookup 8 (by decide)).trans name
  · rw [← pair.2]
    exact (reserveFrame.lookup 9 (by decide)).trans replacementReg

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapReserve
