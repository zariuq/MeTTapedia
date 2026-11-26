import Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectLoop

/-!
# Lowering the source collection TEST

The returned bit and the complete private mask decode to the
source instruction's observation over the original occurrence
identities. A refusal exposes no mask and does not extend the
list of seen claims. The store itself is unchanged by either result.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectRegion

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads Cell)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeGuardState (Stable counters)
open NativeGuardLoop (Normalized CanProbe)
open NativeGuardRegion (operand)
open NativeCollectMemory (Geometry Prefix mark)
open NativeBindingRootMemory (Covered)
open NativeSolverStep (Writes)
open SolverGuardTrichotomy (specification)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def endAt (start : ℕ) : ℕ := NativeCollectLoop.endAt (start + 27)

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeGuardEntry.emit 0 ++ NativeCollectLoop.emit (start + 27) next exhausted malformed

theorem emit_end (start next exhausted malformed : ℕ) : start + (emit start next exhausted malformed).length = endAt start := by
  simp only [emit, endAt, List.length_append, ← Nat.add_assoc, NativeGuardEntry.emit_size, NativeCollectLoop.emit_end]

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  entry : NativeGuardEntry.Placed image start 0
  loop : NativeCollectLoop.Placed image (start + 27) next exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : endAt start ≤ image.size) (ready : next ≤ image.size) (lack : exhausted ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨entry, loop⟩ := NativeWords.code_append (show Code image start (NativeGuardEntry.emit 0 ++ _) from code)
  rw [NativeGuardEntry.emit_size] at loop
  have limit := extent
  unfold endAt NativeCollectLoop.endAt NativeCollectLoop.failAt NativeCollectLoop.passAt NativeCollectLoop.advanceAt
    NativeCollectLoop.markAt NativeGuardLoop.policyAt NativeGuardLoop.solverAt NativeSolverImage.finish NativeSolverImage.bindingAt
    NativeSolverImage.shared NativeSolverImage.expandAt at limit
  exact ⟨NativeGuardEntry.placed_of_emitted image _ 0 (by omega) entry,
    NativeCollectLoop.placed_of_emitted image _ _ _ _ extent ready lack bad short loop⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeCollectLoop.clobbers

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def applyResult (state : SymbolicExecution.Frame σ) (level : ℕ) (destination : P1Source.Reg) :
    Option (Finset ℕ) → SymbolicExecution.Frame σ
  | none => state.write destination 0
  | some witnessed =>
    let entry := state.levels level
    (state.setLevel level {entry with seen := entry.seen ++ [witnessed]}).write destination 1

theorem source_test (state : SymbolicExecution.Frame σ) (base : SymbolicExecution.Equations σ)
    (level : ℕ) (destination : P1Source.Reg) (answer : Subst σ) (pattern : Term σ)
    (resolved : (state.levels level).bindings.answer = some answer) :
    executeInstructionWith (SymbolicExecution.profile base).step state
        (.transform (.test (.perform (.collect pattern)) level destination)) =
      .ok (applyResult state level destination (SymbolicExecution.collect answer state.store.occurrences pattern)) := by
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, SymbolicExecution.profile,
    SymbolicExecution.test, resolved]
  cases SymbolicExecution.collect answer state.store.occurrences pattern <;> rfl

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem store_unchanged (state : SymbolicExecution.Frame σ) (level : ℕ) (destination : P1Source.Reg)
    (result : Option (Finset ℕ)) : (applyResult state level destination result).store = state.store := by
  cases result <;> rfl

variable {cap : ℕ}

def Answer (frame : Frame) (output : Region cap) (pointer : Cell frame.pointer 144)
    (ids : List ℕ) (native : Native) : Option (Finset ℕ) → Prop
  | none => lookup native 0 = some 0
  | some selected =>
    lookup native 0 = some 1 ∧ ∃ bits : List Bool,
      Prefix frame output pointer bits.toArray native ∧ bits.length = ids.length ∧
      (OccurrenceMask.identities ids bits).toFinset = selected

private theorem finish_mask {frame : Frame} {output : Region cap} {pointer : Cell frame.pointer 144}
    {after : Native} {tags : List SolverGuardTrichotomy.Observation}
    (ids : List ℕ) (width : tags.length = ids.length)
    (done : NativeCollectLoop.Returned frame output pointer #[] after (OccurrenceMask.mask tags)) :
    Answer frame output pointer ids after
      ((OccurrenceMask.mask tags).map fun bits => (OccurrenceMask.identities ids bits).toFinset) := by
  cases collected : OccurrenceMask.mask tags with
  | none =>
    rw [collected] at done
    exact done
  | some bits =>
    rw [collected] at done
    obtain ⟨bit, kept⟩ := done
    exact ⟨bit, bits, kept, (OccurrenceMask.length_eq tags bits collected).trans width, rfl⟩

private theorem tags_exact (answer : Subst σ) (pattern : Term σ) (atoms : List (SymbolicExecution.Atom σ))
    {handles : Array Word} (width : handles.size = atoms.length) :
    List.ofFn (fun i => specification (answer.applyTerm pattern) (operand answer atoms width i)) =
      atoms.map (OccurrenceMask.tag answer pattern) := by
  apply List.ext_getElem
  · simp [width]
  · intro i left right
    simp only [List.getElem_ofFn, List.getElem_map, operand, OccurrenceMask.tag]

variable {nc ec mc ac tc oc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {table : Region oc} {output : Region cap} {pointer : Cell frame.pointer 144}

private theorem start_clobbers : NativeGuardEntry.clobbers ⊆ clobbers := by decide

private theorem alongside {work cursor : Finset ℕ} : cursor ∪ (work ∪ cursor) ⊆ work ∪ cursor :=
  Finset.union_subset Finset.subset_union_right (Finset.Subset.refl _)

/-- Successful decoding returns source occurrence IDs,
including both IDs when two occurrences share one handle.
Refusal has the same source behavior as a failed TEST. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image start next exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail table output pointer image base) (room : 0 < ac)
    (symbols : UnifierHeaders.Symbols σ) (source : PackedTerms.Arena) (needle : Word) (handles : Array Word)
    (state : SymbolicExecution.Frame σ) (program : SymbolicExecution.Equations σ)
    (level : ℕ) (destination : P1Source.Reg) (pattern : Term σ) (answer : Subst σ)
    (resolved : (state.levels level).bindings.answer = some answer)
    (width : handles.size = state.store.occurrences.length) (capacity : handles.size ≤ cap)
    (ready : Stable term map frame agenda trail table source needle handles before)
    (normalized : Normalized symbols source needle handles (answer.applyTerm pattern) (operand answer state.store.occurrences width))
    (plan : NativeCollectLoop.Plan (fun i => specification (answer.applyTerm pattern) (operand answer state.store.occurrences width i))
      (fun i => CanProbe nc ec mc ac tc source needle handles[i.val]) 0)
    (privateBase : Reads before pointer.address (output.atWord 0)) :
    let result := SymbolicExecution.collect answer state.store.occurrences pattern
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work marks, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ((work ∪ marks) ∪ counters frame) before after ∧
      Writes term map frame.solver agenda trail work ∧ Covered output marks ∧
      Stable term map frame agenda trail table source needle handles after ∧
      Answer frame output pointer (state.store.occurrences.map Prod.fst) after result ∧
      executeInstructionWith (SymbolicExecution.profile program).step state
        (.transform (.test (.perform (.collect pattern)) level destination)) =
        .ok (applyResult state level destination result) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, started, initFrame, atZero, ⟨atLoop⟩⟩ := NativeGuardEntry.fetched other extra vector point controls 0
    code.entry space.guard source needle handles ready
  have held : Prefix frame output pointer #[] before := ⟨privateBase, NativeMarkTable.PrefixReady.empty mark output before⟩
  obtain ⟨after, steps, work, marks, ran, loopFrame, wrote, used, stable, returned, done⟩ :=
    NativeCollectLoop.fetched other extra vector code.loop space room capacity symbols _ _ normalized plan atLoop
      (controls.transport initFrame NativeGuardEntry.clobbers_data) atZero #[] (held.afterCounters space initFrame) rfl
  have agreement := tags_exact answer pattern state.store.occurrences width
  simp only [List.drop_zero, agreement] at returned
  have observed := finish_mask (state.store.occurrences.map Prod.fst) (by simp) returned
  rw [OccurrenceMask.collect_exact] at observed
  exact ⟨after, 4 + steps, work, marks, X86FuelPrefix.fetches_then 4 steps before a after started ran,
    (initFrame.trans loopFrame).mono (Finset.union_subset start_clobbers (Finset.Subset.refl _)) alongside,
    wrote, used, stable, observed, source_test state program level destination answer pattern resolved, done⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectRegion
