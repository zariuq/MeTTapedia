import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindEntry

/-!
# The native finite-tree binding decision

The shared binding entry reserves a mark prefix. Its run through
the target gives the actual occurrence bit. The final branch
distinguishes a cyclic binding, a permitted elimination, and a
capacity refusal. None of these paths rewrites the pending terms.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingGate

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch)
open NativeArenaGeometry (Region)
open NativeOccurs (word)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start cycle exhausted malformed : ℕ) : List ℕ :=
  NativeBindEntry.setupCode start (start + 34) exhausted ++
    (NativeOccursLoop.emit (start + 34) (start + 264) malformed ++
      NativeDecisions.compareBytes .equal 0 12 (start + 264) cycle)

theorem emit_size (start cycle exhausted malformed : ℕ) : (emit start cycle exhausted malformed).length = 273 := by
  simp only [emit, List.length_append, NativeBindEntry.setup_size, NativeOccursLoop.emit_size, NativeDecisions.compare_size]

structure Placed (image : NativeImage.View) (start cycle exhausted malformed : ℕ) : Prop where
  extent : start + 273 ≤ image.size
  setup : NativeBindEntry.SetupPlaced image start (start + 34) exhausted
  loop : NativeOccursLoop.Placed image (start + 34) (start + 264) malformed
  decideBinding : CompareBranch image (start + 264) cycle .equal 0 12

theorem placed_of_emitted (image : NativeImage.View) (start cycle exhausted malformed : ℕ)
    (size : start + 273 ≤ image.size) (cyclic : cycle ≤ image.size) (noRoom : exhausted ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit start cycle exhausted malformed)) : Placed image start cycle exhausted malformed := by
  obtain ⟨setup, rest⟩ := NativeWords.code_append (show Code image start
    (NativeBindEntry.setupCode start (start + 34) exhausted ++ _) from installed)
  rw [NativeBindEntry.setup_size] at rest
  obtain ⟨looped, test⟩ := NativeWords.code_append rest
  rw [NativeOccursLoop.emit_size] at test
  exact ⟨size, NativeBindEntry.setup_placed image start (start + 34) exhausted (by omega) (by omega) noRoom short setup,
    NativeOccursLoop.placed_of_emitted image _ _ malformed (by omega) (by omega) bad short looped,
    NativeDecisions.compare_placed image .equal 0 12 _ cycle size cyclic short test⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeBindEntry.setupClobbers ∪ NativeOccursLoop.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

private theorem position (start cycle : ℕ) (bit : Bool) :
    (if Comparison.equal.evaluate (word bit) 0 = true then start + 264 + 9 else cycle) =
      if bit then cycle else start + 273 := by
  cases bit <;> rfl

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars]
variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {table : Region markCapacity} {descriptor : WordRegion.Region 2}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start cycle exhausted malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start cycle exhausted malformed)
    (geometry : NativeOccursLoop.Geometry layout agendaLayout table image base)
    (environment : NativeBindEntry.Environment layout arena agendaLayout table descriptor before)
    (symbols : UnifierHeaders.Symbols σ) (name : σ.vars) (query target : Word)
    (queryRead : lookup before 8 = some query) (targetRead : lookup before 9 = some target)
    (registered : symbols.vars.encode name = some query) (term : Term σ)
    (resolved : PackedTerms.lookup symbols arena target = some term) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if target.toNat < markCapacity then
        ∃ writes, X86StateFrame.Frame clobbers writes before after ∧
          NativeMarkTable.Within table 0 (target.toNat + 1) writes ∧
          steps ≤ 9 + NativeOccursLoop.workBound (arena.nodes.toList.take (target.toNat + 1)) ∧
          lookup after 0 = some (word (term.occursIn name)) ∧ lookup after 8 = some query ∧ lookup after 9 = some target ∧
          Nonempty (At image after base (if term.occursIn name then cycle else start + 273))
      else steps = 5 ∧ X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨prepared, steps, setup, setupFrame, attached⟩ := NativeBindEntry.fetched_setup other extra vector
    point controls placed.setup descriptor environment query target queryRead targetRead
  by_cases room : target.toNat < markCapacity
  · rw [if_pos room] at attached
    obtain ⟨rfl, input, ⟨atLoop⟩⟩ := attached
    obtain ⟨checked, loopSteps, loopWrites, run, cost, loopFrame, confined, result, ⟨atResult⟩⟩ :=
      NativeOccursLoop.fetched_target other extra vector atLoop (controls.transport setupFrame NativeBindEntry.setup_clobbers_data)
        placed.loop geometry symbols name query target registered term resolved room input
    have throughScan := setupFrame.trans loopFrame
    obtain ⟨after, decided, decisionFrame, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector atResult .equal 0 12 placed.decideBinding
      (word (term.occursIn name)) 0 result ((throughScan.lookup 12 (by decide)).trans environment.zero)
    rw [position] at endpoint
    have all : X86StateFrame.Frame clobbers loopWrites before after :=
      (throughScan.trans (X86StateFrame.registerOnly decisionFrame)).mono (by decide) (by simp)
    have computed := X86FuelPrefix.fetches_then (7 + loopSteps) 2 before checked after
      (X86FuelPrefix.fetches_then 7 loopSteps before prepared checked setup run) decided
    refine ⟨after, _, computed, ?_⟩
    rw [if_pos room]
    exact ⟨loopWrites, all, confined, by omega, (decisionFrame.lookup 0 (by decide)).trans result,
      (all.lookup 8 (by decide)).trans queryRead, (all.lookup 9 (by decide)).trans targetRead, ⟨endpoint⟩⟩
  · rw [if_neg room] at attached
    obtain ⟨rfl, endpoint⟩ := attached
    refine ⟨prepared, 5, setup, ?_⟩
    rw [if_neg room]
    exact ⟨rfl, setupFrame.mono Finset.subset_union_left (by simp), endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingGate
