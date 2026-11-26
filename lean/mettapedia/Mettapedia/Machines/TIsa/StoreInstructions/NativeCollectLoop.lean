import Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMark

/-!
# Native all-solutions collection

Use the same singleton probe as a guard. A merely possible
match closes the collection unsuccessfully; a decided match
adds one mark and advances. Only a successful terminal bit
exposes a complete mask, and the held occurrence array is
never changed by the scan.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectLoop

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch)
open X86PlacedMemory (Controls Reads Cell)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeGuardState (Stable counters)
open NativeGuardLoop (Normalized CanProbe ProbePlaced policyAt)
open NativeBindingRootMemory (Covered)
open NativeCollectMemory (Geometry Prefix slotBytes mark)
open NativeResolveTest (ReturnPlaced returnCode return_size)
open NativeSolverStep (Writes)
open SolverGuardTrichotomy (Observation specification)
open OccurrenceMask (mask)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def markAt (start : ℕ) : ℕ := policyAt start + 9
def advanceAt (start : ℕ) : ℕ := markAt start + 28
def passAt (start : ℕ) : ℕ := advanceAt start + 25
def failAt (start : ℕ) : ℕ := passAt start + 11
def endAt (start : ℕ) : ℕ := failAt start + 11

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeGuardLoop.emitProbe start (passAt start) (policyAt start) exhausted malformed ++
    (NativeDecisions.compareBytes .notEqual 0 13 (policyAt start) (failAt start) ++
      (NativeCollectMark.emit ++ (NativeGuardCursor.advance (advanceAt start) start ++
        (returnCode 0 1 (passAt start) next ++ returnCode 0 0 (failAt start) next))))

theorem emit_end (start next exhausted malformed : ℕ) : start + (emit start next exhausted malformed).length = endAt start := by
  simp only [emit, List.length_append, ← Nat.add_assoc, NativeGuardLoop.probe_end, NativeDecisions.compare_size,
    NativeCollectMark.emit_size, NativeGuardCursor.advance_size, return_size]
  rfl

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  probe : ProbePlaced image start (passAt start) (policyAt start) exhausted malformed
  decide : CompareBranch image (policyAt start) (failAt start) .notEqual 0 13
  mark : NativeCollectMark.Placed image (markAt start)
  advance : NativeGuardCursor.AdvancePlaced image (advanceAt start) start
  yes : ReturnPlaced image 0 1 (passAt start) next
  no : ReturnPlaced image 0 0 (failAt start) next

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : endAt start ≤ image.size) (ready : next ≤ image.size) (lack : exhausted ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨probe, rest⟩ := NativeWords.code_append (show Code image start
    (NativeGuardLoop.emitProbe start (passAt start) (policyAt start) exhausted malformed ++ _) from code)
  rw [NativeGuardLoop.probe_end] at rest
  obtain ⟨branch, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨write, rest⟩ := NativeWords.code_append rest
  rw [NativeCollectMark.emit_size] at rest
  obtain ⟨advance, rest⟩ := NativeWords.code_append rest
  rw [NativeGuardCursor.advance_size] at rest
  obtain ⟨yes, no⟩ := NativeWords.code_append rest
  rw [return_size] at no
  have limit := extent
  unfold endAt failAt passAt advanceAt markAt at limit
  have entry : start ≤ policyAt start := by
    unfold policyAt NativeGuardLoop.solverAt NativeSolverImage.finish NativeSolverImage.bindingAt NativeSolverImage.shared
      NativeSolverImage.expandAt
    omega
  exact ⟨NativeGuardLoop.probe_placed image _ _ _ _ _ (by omega) (by unfold passAt advanceAt markAt; omega)
      (by omega) lack bad short probe,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by unfold failAt passAt advanceAt markAt; omega) short branch,
    NativeCollectMark.placed_of_emitted image _ (by unfold markAt; omega) write,
    NativeGuardCursor.advance_placed image _ _ (by unfold advanceAt markAt; omega) (by omega) short advance,
    NativeResolveTest.return_placed image _ _ _ _ (by unfold passAt advanceAt markAt; omega) ready short yes,
    NativeResolveTest.return_placed image _ _ _ _ extent ready short no⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeGuardLoop.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := NativeGuardLoop.clobbers_data

variable {nc ec mc ac tc oc cap : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {table : Region oc} {output : Region cap} {pointer : Cell frame.pointer 144}
variable {source : PackedTerms.Arena} {needle : Word} {handles : Array Word}
variable {image : NativeImage.View} {base : BitVec 48}

private abbrev branchClobbers : Finset Register := {.rflags, .rip}

private theorem fetched_route (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image start next exhausted malformed) (point : At image before base (policyAt start))
    (one : lookup before 13 = some 1) (observed : Observation)
    (verdict : lookup before 0 = some (NativeGuardDecision.word observed)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame branchClobbers ∅ before after ∧
      Nonempty (At image after base (if observed = .possible then failAt start else markAt start)) := by
  obtain ⟨after, ran, regs, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector point .notEqual 0 13 code.decide _ _ verdict one
  refine ⟨after, ran, X86StateFrame.registerOnly regs, ⟨?_⟩⟩
  cases observed <;> exact endpoint

private theorem word_mark (observation : Observation) (settled : observation ≠ .possible) :
    NativeGuardDecision.word observation = mark observation.must := by
  cases observation
  · rfl
  · exact (settled rfl).elim
  · rfl

private theorem frame_counter (space : Geometry term map frame agenda trail table output pointer image base)
    (slot : Fin 16) (i : Fin cap) :
    Disjoint (NativeGuardInstall.slotBytes frame slot) (slotBytes output i) :=
  Covered.separate space.frameApart.symm (NativeGuardInstall.slots_cover frame slot) (Covered.word output i)

private theorem fetched_append (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native} (code : Placed image start next exhausted malformed)
    (space : Geometry term map frame agenda trail table output pointer image base)
    (point : At image before base (markAt start)) (controls : Controls before) (ordinal : ℕ) (bits : Array Bool)
    (size : bits.size = ordinal) (room : ordinal < cap)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles ordinal 0 before)
    (resident : Prefix frame output pointer bits before) (selected : Bool)
    (which : lookup before 0 = some (mark selected)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes output ⟨ordinal, room⟩ ∪ counters frame) before after ∧
      NativeGuardState.State term map frame agenda trail table source needle handles (ordinal + 1) 0 after ∧
      Prefix frame output pointer (bits.push selected) after ∧ Nonempty (At image after base start) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have inside : bits.size < cap := size.symm ▸ room
  have index : (⟨bits.size, inside⟩ : Fin cap) = ⟨ordinal, room⟩ := Fin.ext size
  obtain ⟨a, filled, wrote, new, ⟨atAdvance⟩⟩ := NativeCollectMark.fetched other extra vector code.mark point controls
    bits selected resident state.stable.scratch.stack (size.symm ▸ state.ordinalWord) which inside
    (space.code ⟨bits.size, inside⟩) (space.pointerMarks ⟨bits.size, inside⟩)
  rw [index] at wrote
  have stable := space.stable_after_marks state.stable wrote (Covered.word output ⟨ordinal, room⟩) (by decide) (by decide) (by decide)
  have cursor := state.ordinalWord.preserved wrote (frame_counter space 14 ⟨ordinal, room⟩)
  obtain ⟨after, ran, stepped, advanced, endpoint⟩ := NativeGuardCursor.fetched_advance other extra vector
    (show At image a base (advanceAt start) from atAdvance) (controls.transport wrote NativeCollectMark.clobbers_data)
    code.advance frame stable.scratch.stack ordinal cursor stable.scratch.one space.guard.ordinalCode
  have counts := stepped.mono (Finset.Subset.refl _) (show _ ⊆ counters frame from Finset.subset_union_left)
  have ready := stable.afterCounters space.guard counts (by decide) (by decide) (by decide)
  have counter := (state.counterWord.preserved wrote (frame_counter space 15 ⟨ordinal, room⟩)).preserved stepped
    (frame.separate_words (by decide : (15 : Fin 16) ≠ 14))
  exact ⟨after, X86FuelPrefix.fetches_then 5 5 before a after filled ran,
    (wrote.trans counts).mono (by decide) (Finset.Subset.refl _), ⟨ready, advanced, counter⟩, new.afterCounters space counts, endpoint⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

private theorem fetched_visit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image start next exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail table output pointer image base) (room : 0 < ac)
    (symbols : UnifierHeaders.Symbols σ) (pattern : Term σ) (item : Fin handles.size → Term σ)
    (normalized : Normalized symbols source needle handles pattern item) (i : Fin handles.size)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles i.val 0 before)
    (bits : Array Bool) (resident : Prefix frame output pointer bits before)
    (plan : CanProbe nc ec mc ac tc source needle handles[i.val]) :
    let seen := specification pattern (item i)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers work before after ∧ Writes term map frame.solver agenda trail work ∧
      NativeGuardState.State term map frame agenda trail table source needle handles i.val 0 after ∧
      Prefix frame output pointer bits after ∧ lookup after 0 = some (NativeGuardDecision.word seen) ∧
      Nonempty (At image after base (if seen = .possible then failAt start else markAt start)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, steps, work, ran, probeFrame, writes, probed, tag, ⟨atRoute⟩⟩ :=
    NativeGuardLoop.fetched_probe other extra vector code.probe point controls space.guard room
      symbols pattern item normalized i 0 state plan
  obtain ⟨after, tested, branch, endpoint⟩ := fetched_route other extra vector code atRoute
    probed.stable.scratch.one (specification pattern (item i)) tag
  have routed : X86StateFrame.Frame clobbers work before after :=
    (probeFrame.trans branch).mono (by decide) (by rw [Finset.union_empty])
  exact ⟨after, steps + 2, work, X86FuelPrefix.fetches_then steps 2 before a after ran tested, routed, writes,
    ⟨probed.stable.preserved branch (by decide) (by decide) (by decide), probed.ordinalWord.preserved branch (by simp),
      probed.counterWord.preserved branch (by simp)⟩,
    (resident.afterProbe space probeFrame writes).preserved branch, (branch.lookup 0 (by decide)).trans tag, endpoint⟩

inductive Plan {size : ℕ} (tag : Fin size → Observation) (fits : Fin size → Prop) : ℕ → Prop
  | exhausted : Plan tag fits size
  | reject {i : Fin size} : fits i → tag i = .possible → Plan tag fits i.val
  | record {i : Fin size} : fits i → tag i ≠ .possible → Plan tag fits (i.val + 1) → Plan tag fits i.val

theorem Plan.of_all {size : ℕ} (tag : Fin size → Observation) (fits : Fin size → Prop) (all : ∀ i, fits i)
    (ordinal : ℕ) (bound : ordinal ≤ size) : Plan tag fits ordinal := by
  generalize eq : size - ordinal = distance
  induction distance using Nat.strong_induction_on generalizing ordinal with
  | h n ih =>
    by_cases done : ordinal = size
    · subst ordinal; exact .exhausted
    · let i : Fin size := ⟨ordinal, by omega⟩
      by_cases may : tag i = .possible
      · exact .reject (all i) may
      · have smaller : size - (ordinal + 1) < n := by omega
        exact .record (all i) may (ih _ smaller (ordinal + 1) (by omega) rfl)

def Returned (frame : Frame) (output : Region cap) (pointer : Cell frame.pointer 144)
    (seen : Array Bool) (native : Native) : Option (List Bool) → Prop
  | none => lookup native 0 = some 0
  | some bits => lookup native 0 = some 1 ∧ Prefix frame output pointer (seen.toList ++ bits).toArray native

private theorem drop_tags {size : ℕ} (tag : Fin size → Observation) (i : Fin size) :
    (List.ofFn tag).drop i.val = tag i :: (List.ofFn tag).drop (i.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp), List.getElem_ofFn]

private theorem mask_cons (observed : Observation) (settled : observed ≠ .possible) (later : List Observation) :
    mask (observed :: later) = (mask later).map (observed.must :: ·) := by
  cases observed
  · rfl
  · exact (settled rfl).elim
  · rfl

private theorem append_answer {bits : Array Bool} {selected : Bool} {after : Native} {later : Option (List Bool)}
    (ready : Returned frame output pointer (bits.push selected) after later) :
    Returned frame output pointer bits after (later.map (selected :: ·)) := by
  cases later <;> simpa [Returned, Array.toList_push, List.append_assoc] using ready

private theorem merge_effects (probe wrote rest later cursor : Finset ℕ) :
    (probe ∪ (wrote ∪ cursor)) ∪ ((rest ∪ later) ∪ cursor) = ((probe ∪ rest) ∪ (wrote ∪ later)) ∪ cursor := by
  ext b
  simp only [Finset.mem_union]
  tauto

/-- A fitted scan runs to completion on the emitted bytes.
Uncertainty stops the scan and returns no collection; otherwise
the initialized private marks have exactly the occurrence order.
The departure bit is the point at which a complete mask is exposed. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} (code : Placed image start next exhausted malformed)
    (space : Geometry term map frame agenda trail table output pointer image base) (room : 0 < ac) (fits : handles.size ≤ cap)
    (symbols : UnifierHeaders.Symbols σ) (pattern : Term σ) (item : Fin handles.size → Term σ)
    (normalized : Normalized symbols source needle handles pattern item)
    {ordinal : ℕ}
    (plan : Plan (fun i => specification pattern (item i)) (fun i => CanProbe nc ec mc ac tc source needle handles[i.val]) ordinal)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles ordinal 0 before)
    (bits : Array Bool) (resident : Prefix frame output pointer bits before) (size : bits.size = ordinal) :
    let tags := List.ofFn (fun i : Fin handles.size => specification pattern (item i))
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work marks, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ((work ∪ marks) ∪ counters frame) before after ∧
      Writes term map frame.solver agenda trail work ∧ Covered output marks ∧
      Stable term map frame agenda trail table source needle handles after ∧
      Returned frame output pointer bits after (mask (tags.drop ordinal)) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let tag : Fin handles.size → Observation := fun i => specification pattern (item i)
  let tags := List.ofFn tag
  revert before bits
  induction plan with
  | exhausted =>
    intro before point controls state bits resident size
    obtain ⟨a, steps, read, readFrame, closed⟩ := NativeGuardOperands.fetched other extra vector point controls code.probe.operands
      state.stable.scratch.stack needle handles.size state.ordinalWord state.stable.directory (Nat.le_refl _)
    rw [dif_neg (Nat.lt_irrefl _)] at closed
    obtain ⟨rfl, ⟨atPass⟩⟩ := closed
    obtain ⟨after, returned, returnFrame, bit, done⟩ := NativeResolveTest.fetched_return other extra vector atPass 0 1 code.yes
    have only : X86StateFrame.Frame (NativeGuardOperands.clobbers ∪ NativeResolveTest.returnClobbers 0) ∅ before after :=
      (readFrame.trans returnFrame).mono (Finset.Subset.refl _) (by simp)
    have noneLeft : tags.drop handles.size = [] := List.drop_of_length_le (by simp [tags])
    have answer : Returned frame output pointer bits after (mask (tags.drop handles.size)) := by
      rw [noneLeft]
      refine ⟨bit, ?_⟩
      simpa only [List.append_nil, Array.toArray_toList] using resident.preserved only
    exact ⟨after, 7, ∅, ∅, X86FuelPrefix.fetches_then 5 2 before a after read returned, only.mono (by decide)
      (Finset.empty_subset _), .idle, Covered.empty _, state.stable.preserved only (by decide) (by decide) (by decide), answer, done⟩
  | @reject i can unsteady =>
    intro before point controls state bits resident size
    obtain ⟨a, steps, work, ran, framed, writes, stable, _, _, onBranch⟩ :=
      fetched_visit other extra vector code point controls space room symbols pattern item normalized i state bits resident can
    rw [unsteady, if_pos rfl] at onBranch
    obtain ⟨atFail⟩ := onBranch
    obtain ⟨after, returned, returnFrame, bit, done⟩ := NativeResolveTest.fetched_return other extra vector atFail 0 0 code.no
    have answer : Returned frame output pointer bits after (mask (tags.drop i.val)) := by
      rw [drop_tags _ i]
      rw [show tag i = .possible from unsteady]
      exact bit
    have all : X86StateFrame.Frame clobbers ((work ∪ ∅) ∪ counters frame) before after :=
      (framed.trans returnFrame).mono (by decide) (by simp)
    exact ⟨after, steps + 2, work, ∅, X86FuelPrefix.fetches_then steps 2 before a after ran returned, all, writes,
      Covered.empty _, stable.stable.preserved returnFrame (by decide) (by decide) (by decide), answer, done⟩
  | @record i can definite rest ih =>
    intro before point controls state bits resident size
    obtain ⟨a, first, work, classified, probeFrame, writes, ready, prefixReady, klass, onBranch⟩ :=
      fetched_visit other extra vector code point controls space room symbols pattern item normalized i state bits resident can
    rw [if_neg definite] at onBranch
    obtain ⟨atMark⟩ := onBranch
    have writable := i.isLt.trans_le fits
    have word := klass.trans (congrArg some (word_mark (tag i) definite))
    obtain ⟨b, marked, markFrame, nextState, grown, ⟨again⟩⟩ := fetched_append other extra vector code space atMark
      (controls.transport probeFrame clobbers_data) i.val bits size writable ready prefixReady (tag i).must word
    have newSize : (bits.push (tag i).must).size = i.val + 1 := by rw [Array.size_push, size]
    have between := probeFrame.trans markFrame
    obtain ⟨after, last, later, marks, ran, tailFrame, laterWrites, markWrites, stable, answer, done⟩ :=
      ih again (controls.transport between (by simp [clobbers_data])) nextState _ grown newSize
    let wrote := slotBytes output ⟨i.val, writable⟩
    have all : X86StateFrame.Frame clobbers ((work ∪ later) ∪ (wrote ∪ marks) ∪ counters frame) before after := by
      have regs : (clobbers ∪ clobbers) ∪ clobbers ⊆ clobbers := by simp
      have together := (between.trans tailFrame).mono regs (Finset.Subset.refl _)
      rw [merge_effects] at together
      exact together
    have exact : Returned frame output pointer bits after (mask (tags.drop i.val)) := by
      rw [drop_tags _ i, mask_cons _ definite]
      exact append_answer answer
    exact ⟨after, first + 10 + last, work ∪ later, wrote ∪ marks,
      X86FuelPrefix.fetches_then (first + 10) last before b after
        (X86FuelPrefix.fetches_then first 10 before a b classified marked) ran, all, .union writes laterWrites,
      (Covered.word output ⟨i.val, writable⟩).union markWrites, stable, exact, done⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectLoop
