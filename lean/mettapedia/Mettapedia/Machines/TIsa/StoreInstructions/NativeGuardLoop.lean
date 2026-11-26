import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardState
import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardTrial

/-!
# One native scan of normalized guard occurrences

The code uses one singleton solver image for every candidate.
Advancing resets only its private agenda, trail and lengths.
The loop visits occurrences, so repeated handles contribute
separately to an exact count.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardLoop

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeGuardState (Stable Geometry counters)
open NativeGuardPolicy (Decision choose adjust scan)
open NativeSolverStep (Writes)
open NativeSolverResources (Budget)
open NativeResolveTest (ReturnPlaced returnCode)
open IndexedGuard (Query)
open SolverGuardTrichotomy (Observation specification)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def trialAt (start : ℕ) : ℕ := start + 51
def solverAt (start : ℕ) : ℕ := start + 156
def policyAt (start : ℕ) : ℕ := NativeSolverImage.finish (solverAt start) + 59
def advanceAt (q : Query) (start : ℕ) : ℕ := policyAt start + NativeGuardPolicy.width q
def finishAt (q : Query) (start : ℕ) : ℕ := advanceAt q start + 25
def passAt (q : Query) (start : ℕ) : ℕ := finishAt q start + NativeGuardCursor.finishWidth q
def failAt (q : Query) (start : ℕ) : ℕ := passAt q start + 11
def endAt (q : Query) (start : ℕ) : ℕ := failAt q start + 11

def emitProbe (start empty classified exhausted malformed : ℕ) : List ℕ :=
  NativeGuardOperands.emit start empty ++
    (NativeGuardTrial.emit ++ NativeGuardDecision.emit 0 (solverAt start) classified exhausted malformed)

def emit (q : Query) (start next exhausted malformed : ℕ) : List ℕ :=
  emitProbe start (finishAt q start) (policyAt start) exhausted malformed ++
    (NativeGuardPolicy.emit q (policyAt start) (passAt q start) (failAt q start) ++
          (NativeGuardCursor.advance (advanceAt q start) start ++
            (NativeGuardCursor.finish q (finishAt q start) (passAt q start) (failAt q start) ++
              (returnCode 0 1 (passAt q start) next ++ returnCode 0 0 (failAt q start) next))))

private theorem decision_end (dst : Fin 16) (start next exhausted malformed : ℕ) :
    start + (NativeGuardDecision.emit dst start next exhausted malformed).length = NativeSolverImage.finish start + 59 := by
  simp only [NativeGuardDecision.emit, List.length_append, NativeGuardDecision.success_size, NativeResolveTest.return_size,
    ← Nat.add_assoc, NativeSolverImage.emit_size]

theorem probe_end (start empty classified exhausted malformed : ℕ) :
    start + (emitProbe start empty classified exhausted malformed).length = policyAt start := by
  simp only [emitProbe, List.length_append, NativeGuardOperands.emit_size, NativeGuardTrial.emit_size, ← Nat.add_assoc]
  change solverAt start + (NativeGuardDecision.emit 0 (solverAt start) classified exhausted malformed).length = _
  rw [decision_end]
  rfl

theorem emit_end (q : Query) (start next exhausted malformed : ℕ) :
    start + (emit q start next exhausted malformed).length = endAt q start := by
  simp only [emit, List.length_append, probe_end, NativeGuardPolicy.emit_size, NativeGuardCursor.advance_size,
    NativeGuardCursor.finish_size, NativeResolveTest.return_size, ← Nat.add_assoc]
  rfl

structure ProbePlaced (image : NativeImage.View) (start empty classified exhausted malformed : ℕ) : Prop where
  operands : NativeGuardOperands.Placed image start empty
  trial : NativeGuardTrial.Placed image (trialAt start)
  classify : NativeGuardDecision.Placed image 0 (solverAt start) classified exhausted malformed

theorem probe_placed (image : NativeImage.View) (start empty classified exhausted malformed : ℕ)
    (extent : policyAt start ≤ image.size) (finish : empty ≤ image.size) (decision : classified ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emitProbe start empty classified exhausted malformed)) :
    ProbePlaced image start empty classified exhausted malformed := by
  obtain ⟨operands, rest⟩ := NativeWords.code_append (show Code image start
    (NativeGuardOperands.emit start empty ++ _) from code)
  rw [NativeGuardOperands.emit_size] at rest
  obtain ⟨trial, solver⟩ := NativeWords.code_append rest
  rw [NativeGuardTrial.emit_size] at solver
  have bodyFits : start + 156 ≤ image.size := by
    unfold policyAt solverAt NativeSolverImage.finish NativeSolverImage.bindingAt NativeSolverImage.shared
      NativeSolverImage.expandAt at extent
    omega
  exact ⟨NativeGuardOperands.placed_of_emitted image _ _ (by omega) finish short operands,
    NativeGuardTrial.placed_of_emitted image _ bodyFits trial,
    NativeGuardDecision.placed_of_emitted image _ _ _ _ _ extent decision lack bad short solver⟩

structure Placed (image : NativeImage.View) (q : Query) (start next exhausted malformed : ℕ) : Prop where
  probe : ProbePlaced image start (finishAt q start) (policyAt start) exhausted malformed
  policy : NativeGuardPolicy.Placed image q (policyAt start) (passAt q start) (failAt q start)
  advance : NativeGuardCursor.AdvancePlaced image (advanceAt q start) start
  finish : NativeGuardCursor.FinishPlaced image q (finishAt q start) (passAt q start) (failAt q start)
  yes : ReturnPlaced image 0 1 (passAt q start) next
  no : ReturnPlaced image 0 0 (failAt q start) next

theorem placed_of_emitted (image : NativeImage.View) (q : Query) (start next exhausted malformed : ℕ)
    (extent : endAt q start ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit q start next exhausted malformed)) : Placed image q start next exhausted malformed := by
  obtain ⟨probe, rest⟩ := NativeWords.code_append (show Code image start
    (emitProbe start (finishAt q start) (policyAt start) exhausted malformed ++ _) from code)
  rw [probe_end] at rest
  obtain ⟨policy, rest⟩ := NativeWords.code_append rest
  rw [NativeGuardPolicy.emit_size] at rest
  obtain ⟨advance, rest⟩ := NativeWords.code_append rest
  rw [NativeGuardCursor.advance_size] at rest
  obtain ⟨finish, rest⟩ := NativeWords.code_append rest
  rw [NativeGuardCursor.finish_size] at rest
  obtain ⟨yes, no⟩ := NativeWords.code_append rest
  rw [NativeResolveTest.return_size] at no
  have size : policyAt start + NativeGuardPolicy.width q + 25 + NativeGuardCursor.finishWidth q + 11 + 11 ≤ image.size := extent
  have finishFits : finishAt q start + NativeGuardCursor.finishWidth q ≤ image.size := by unfold finishAt advanceAt; omega
  have starts : start ≤ image.size := by
    unfold policyAt solverAt NativeSolverImage.finish NativeSolverImage.bindingAt NativeSolverImage.shared
      NativeSolverImage.expandAt at size
    omega
  have passFits : passAt q start + 11 ≤ image.size := by unfold passAt finishAt advanceAt; omega
  have failFits : failAt q start + 11 ≤ image.size := extent
  exact ⟨probe_placed image _ _ _ _ _ (by omega) (by unfold finishAt advanceAt; omega) (by omega) lack bad short probe,
    NativeGuardPolicy.placed_of_emitted image _ _ _ _ (by omega) (by omega) (by omega) short policy,
    NativeGuardCursor.advance_placed image _ _ (show finishAt q start ≤ image.size by omega) starts short advance,
    NativeGuardCursor.finish_placed image _ _ _ _ finishFits (by omega) (by omega) short finish,
    NativeResolveTest.return_placed image _ _ _ _ passFits target short yes,
    NativeResolveTest.return_placed image _ _ _ _ failFits target short no⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register :=
  {.rax, .rcx, .rdx, .rbx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r13, .r14, .r15, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

universe u p
variable {σ : LPSignature.{u,u,p,u}} {source : PackedTerms.Arena} {needle : Word} {handles : Array Word}
variable {nc ec mc ac tc occ : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame} {table : Region occ}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

structure Normalized (symbols : UnifierHeaders.Symbols σ) (source : PackedTerms.Arena)
    (needle : Word) (handles : Array Word) (pattern : Term σ) (item : Fin handles.size → Term σ) : Prop where
  left : PackedTerms.lookup symbols source needle = some pattern
  right : ∀ i : Fin handles.size, PackedTerms.lookup symbols source handles[i.val] = some (item i)

def CanProbe (nc ec mc ac tc : ℕ) (source : PackedTerms.Arena) (needle : Word) (candidate : Word) : Prop :=
  ∃ fuel, PackedWorklist.Reserve fuel source.nodes.size source.children.size ∧
    ∃ needed : Budget, NativeSolverResources.planned fuel 1 0 (.working ⟨source, [(needle, candidate)], []⟩) = some needed ∧
      needed.Within ⟨nc, ec, mc, ac, tc⟩

def Destination (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (table : Region occ)
    (source : PackedTerms.Arena) (needle : Word) (handles : Array Word)
    (image : NativeImage.View) (base : BitVec 48) (q : Query) (start ordinal : ℕ) (native : Native) : Decision → Prop
  | .stop found => Nonempty (At image native base (if found then passAt q start else failAt q start))
  | .continue count => NativeGuardState.State term map frame agenda trail table source needle handles (ordinal + 1) count native ∧
      Nonempty (At image native base start)

private abbrev postClobbers : Finset Register := {.rax, .rcx, .rsi, .rflags, .rip}

private theorem policyClobbers : NativeGuardPolicy.clobbers ⊆ postClobbers := by decide

private theorem mergeCounters (frame : Frame) :
    NativeGuardPolicy.counterBytes frame ∪ NativeGuardCursor.ordinalBytes frame ⊆ counters frame :=
  Finset.union_subset Finset.subset_union_right Finset.subset_union_left

private theorem mergeWork {R : Finset Register} {a b common : Finset ℕ} {before middle after : Native}
    (first : X86StateFrame.Frame R (a ∪ common) before middle)
    (second : X86StateFrame.Frame R (b ∪ common) middle after) :
    X86StateFrame.Frame R ((a ∪ b) ∪ common) before after :=
  (first.trans second).mono (Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _))
    (Finset.union_subset
      (Finset.union_subset
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) Finset.subset_union_right)
      (Finset.union_subset
        (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left) Finset.subset_union_right))

private theorem fetched_post (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {q : Query} {start next exhausted malformed ordinal count : ℕ} {before : Native}
    (code : Placed image q start next exhausted malformed) (point : At image before base (policyAt start))
    (controls : Controls before) (space : Geometry term map frame agenda trail table image base)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles ordinal count before)
    (fits : count < 2 ^ 64) (observed : Observation) (tag : lookup before 0 = some (NativeGuardDecision.word observed)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame postClobbers (counters frame) before after ∧
      Stable term map frame agenda trail table source needle handles after ∧
      Destination term map frame agenda trail table source needle handles image base q start ordinal after
        (choose q count observed) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨d, steps, policy, policyFrame, chosen⟩ := NativeGuardPolicy.fetched other extra vector q point controls code.policy
    frame state.stable.scratch.stack count fits state.counterWord observed tag state.stable.scratch.zero state.stable.scratch.one space.countCode
  have readable := state.stable.afterCounters space (policyFrame.mono (Finset.Subset.refl _) Finset.subset_union_right)
    (by decide) (by decide) (by decide)
  cases outcome : choose q count observed with
  | stop answer =>
    rw [outcome] at chosen
    exact ⟨d, steps, policy, policyFrame.mono policyClobbers Finset.subset_union_right, readable, chosen⟩
  | «continue» n =>
    rw [outcome] at chosen
    obtain ⟨counter, ⟨atAdvance⟩⟩ := chosen
    have cursor := state.ordinalWord.preserved policyFrame (frame.separate_words (by decide : (14 : Fin 16) ≠ 15))
    obtain ⟨after, advanced, advancing, cursorAfter, endpoint⟩ := NativeGuardCursor.fetched_advance
      other extra vector (show At image d base (advanceAt q start) from atAdvance)
      (controls.transport policyFrame NativeGuardPolicy.clobbers_data) code.advance frame readable.scratch.stack ordinal cursor
      readable.scratch.one space.ordinalCode
    have stable := readable.afterCounters space (advancing.mono (Finset.Subset.refl _) Finset.subset_union_left)
      (by decide) (by decide) (by decide)
    have counterKept := counter.preserved advancing (frame.separate_words (by decide : (15 : Fin 16) ≠ 14))
    have all : X86StateFrame.Frame postClobbers (counters frame) before after :=
      (policyFrame.trans advancing).mono (Finset.union_subset policyClobbers (Finset.Subset.refl _)) (mergeCounters frame)
    exact ⟨after, steps + 5, X86FuelPrefix.fetches_then steps 5 before d after policy advanced,
      all, stable, ⟨⟨stable, cursorAfter, counterKept⟩, endpoint⟩⟩

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Fetch the normalized operand and classify it in the
same solver image for every observer. The observer runs only
after this prefix has restored the stable view and counters. -/
theorem fetched_probe (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start empty classifiedAt exhausted malformed : ℕ} {before : Native}
    (code : ProbePlaced image start empty classifiedAt exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail table image base) (room : 0 < ac)
    (symbols : UnifierHeaders.Symbols σ) (pattern : Term σ) (item : Fin handles.size → Term σ)
    (normalized : Normalized symbols source needle handles pattern item) (i : Fin handles.size) (remaining : ℕ)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles i.val remaining before)
    (plan : CanProbe nc ec mc ac tc source needle handles[i.val]) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧ Writes term map frame.solver agenda trail bytes ∧
      NativeGuardState.State term map frame agenda trail table source needle handles i.val remaining after ∧
      lookup after 0 = some (NativeGuardDecision.word (specification pattern (item i))) ∧
      Nonempty (At image after base classifiedAt) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, count, fetched, readFrame, pointed⟩ := NativeGuardOperands.fetched other extra vector point controls code.operands
    state.stable.scratch.stack needle i.val state.ordinalWord state.stable.directory i.isLt.le
  rw [dif_pos i.isLt] at pointed
  obtain ⟨rfl, left, right, ⟨atTrial⟩⟩ := pointed
  have ready := state.stable.preserved readFrame (by decide) (by decide) (by decide)
  obtain ⟨b, prepared, prepFrame, prepWrites, seed, single, empty, ⟨atSolver⟩⟩ := NativeGuardTrial.fetched
    other extra vector atTrial (controls.transport readFrame NativeGuardOperands.clobbers_data) code.trial space.workspace
    source ready.scratch needle handles[i.val] left right room
  have throughPrep := readFrame.trans prepFrame
  obtain ⟨fuel, fit, need, required, available⟩ := plan
  have planned : NativeSolverResources.planned fuel seed.equations.size seed.bindings.size
      (.working ⟨source, [(needle, handles[i.val])], []⟩) = some need := by
    rw [single, empty]
    exact required
  obtain ⟨c, classified, solveBytes, ran, solved, solveWrites, classification, sourceReady, one, ⟨atPolicy⟩⟩ :=
    NativeGuardDecision.fetched other extra vector 0 code.classify
      (show At image b base (solverAt start) from atSolver) (controls.transport throughPrep (by decide)) space.workspace.solver
      symbols source needle handles[i.val] pattern (item i) seed normalized.left (normalized.right i) fuel fit need planned available
  let workBytes := NativeGuardTrial.bytes frame agenda trail room ∪ solveBytes
  have work : Writes term map frame.solver agenda trail workBytes := .union prepWrites solveWrites
  have throughSolve : X86StateFrame.Frame clobbers workBytes before c :=
    (throughPrep.trans solved).mono (by decide) (by simp only [Finset.empty_union, workBytes]; exact Finset.Subset.refl _)
  have inPolicy := state.stable.afterSolver space throughSolve work sourceReady (by decide) (by decide) (one (by decide))
  have cursor := state.ordinalWord.preserved throughSolve ((space.workspace.saved 14 (by decide) (by decide)).kept work)
  have counter := state.counterWord.preserved throughSolve ((space.workspace.saved 15 (by decide) (by decide)).kept work)
  have throughRead := X86FuelPrefix.fetches_then 9 18 before a b fetched prepared
  have throughClassify := X86FuelPrefix.fetches_then 27 classified before b c throughRead ran
  exact ⟨c, 27 + classified, workBytes, throughClassify, throughSolve, work, ⟨inPolicy, cursor, counter⟩,
    classification, ⟨atPolicy⟩⟩

/-- One actual candidate is fetched, classified, and either
closes the guard or advances to the next occurrence. -/
theorem fetched_visit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {q : Query} {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image q start next exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail table image base) (room : 0 < ac)
    (symbols : UnifierHeaders.Symbols σ) (pattern : Term σ) (item : Fin handles.size → Term σ)
    (normalized : Normalized symbols source needle handles pattern item) (i : Fin handles.size) (remaining : ℕ)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles i.val remaining before)
    (countFits : remaining < 2 ^ 64) (plan : CanProbe nc ec mc ac tc source needle handles[i.val]) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (bytes ∪ counters frame) before after ∧ Writes term map frame.solver agenda trail bytes ∧
      Stable term map frame agenda trail table source needle handles after ∧
      Destination term map frame agenda trail table source needle handles image base q start i.val after
        (choose q remaining (specification pattern (item i))) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨mid, first, bytes, classified, probeFrame, writes, prepared, observation, ⟨atPolicy⟩⟩ :=
    fetched_probe other extra vector code.probe point controls space room symbols pattern item normalized i remaining state plan
  obtain ⟨after, second, policy, policyFrame, stable, chosen⟩ := fetched_post other extra vector code atPolicy
    (controls.transport probeFrame clobbers_data) space prepared countFits _ observation
  exact ⟨after, first + second, bytes, X86FuelPrefix.fetches_then first second before mid after classified policy,
    (probeFrame.trans policyFrame).mono (by decide) (Finset.Subset.refl _), writes, stable, chosen⟩

inductive Plan (q : Query) {size : ℕ} (tag : Fin size → Observation) (fits : Fin size → Prop) : ℕ → ℕ → Prop
  | exhausted {count : ℕ} : Plan q tag fits size count
  | stop {i : Fin size} {count : ℕ} {answer : Bool} :
      fits i → choose q count (tag i) = .stop answer → Plan q tag fits i.val count
  | more {i : Fin size} {count next : ℕ} :
      fits i → choose q count (tag i) = .continue next → Plan q tag fits (i.val + 1) next → Plan q tag fits i.val count

/-- Per-candidate resource bounds suffice. The shorter
certificate never asks about candidates after a decisive result. -/
theorem Plan.of_all (q : Query) {size : ℕ} (tag : Fin size → Observation) (fits : Fin size → Prop)
    (all : ∀ i, fits i) (ordinal count : ℕ) (bound : ordinal ≤ size) : Plan q tag fits ordinal count := by
  generalize eq : size - ordinal = distance
  induction distance using Nat.strong_induction_on generalizing ordinal count with
  | h n ih =>
    by_cases ended : ordinal = size
    · subst ordinal; exact .exhausted
    · let i : Fin size := ⟨ordinal, by omega⟩
      cases decision : choose q count (tag i) with
      | stop answer => exact .stop (all i) decision
      | «continue» next =>
        have smaller : size - (ordinal + 1) < n := by omega
        exact .more (all i) decision (ih _ smaller (ordinal + 1) next (by omega) rfl)

private theorem drop_tags {size : ℕ} (tag : Fin size → Observation) (i : Fin size) :
    (List.ofFn tag).drop i.val = tag i :: (List.ofFn tag).drop (i.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp), List.getElem_ofFn]

private theorem scan_stop {size : ℕ} (tag : Fin size → Observation) (i : Fin size) (q : Query) (count : ℕ) (answer : Bool)
    (declared : choose q count (tag i) = .stop answer) :
    scan (adjust q count) ((List.ofFn tag).drop i.val) = answer := by
  rw [drop_tags, NativeGuardPolicy.scan_cons, declared]

private theorem scan_more {size : ℕ} (tag : Fin size → Observation) (i : Fin size) (q : Query) (count later : ℕ)
    (declared : choose q count (tag i) = .continue later) :
    scan (adjust q count) ((List.ofFn tag).drop i.val) =
      scan (adjust q later) ((List.ofFn tag).drop (i.val + 1)) := by
  rw [drop_tags, NativeGuardPolicy.scan_cons, declared]

private theorem counter_nonincreasing (q : Query) (observed : Observation) (first second : ℕ)
    (action : choose q first observed = .continue second) : second ≤ first := by
  cases q <;> cases observed <;> cases first <;> simp_all [choose]

private theorem fetched_return_bit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {q : Query} {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image q start next exhausted malformed) (answer : Bool)
    (point : At image before base (if answer then passAt q start else failAt q start)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame (NativeResolveTest.returnClobbers 0) ∅ before after ∧
      lookup after 0 = some (booleanWord answer) ∧ Nonempty (At image after base next) := by
  cases answer
  · exact NativeResolveTest.fetched_return other extra vector point 0 0 code.no
  · exact NativeResolveTest.fetched_return other extra vector point 0 1 code.yes

/-- The actual guard region returns the corresponding
all-solutions scan bit. It preserves the normalized terms
and occurrence order for the caller's next operation. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {q : Query} {start next exhausted malformed : ℕ}
    (code : Placed image q start next exhausted malformed) (space : Geometry term map frame agenda trail table image base)
    (room : 0 < ac) (symbols : UnifierHeaders.Symbols σ) (pattern : Term σ) (item : Fin handles.size → Term σ)
    (normalized : Normalized symbols source needle handles pattern item)
    {ordinal count : ℕ} {before : Native} (point : At image before base start) (controls : Controls before)
    (state : NativeGuardState.State term map frame agenda trail table source needle handles ordinal count before)
    (countFits : count < 2 ^ 64)
    (plan : Plan q (fun i => specification pattern (item i)) (fun i => CanProbe nc ec mc ac tc source needle handles[i.val])
      ordinal count) :
    let tags := List.ofFn (fun i : Fin handles.size => specification pattern (item i))
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (work ∪ counters frame) before after ∧ Writes term map frame.solver agenda trail work ∧
      Stable term map frame agenda trail table source needle handles after ∧
      lookup after 0 = some (booleanWord (scan (adjust q count) (tags.drop ordinal))) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let tags := List.ofFn (fun i : Fin handles.size => specification pattern (item i))
  induction plan generalizing before with
  | @exhausted count =>
    obtain ⟨a, steps, fetched, readFrame, closed⟩ := NativeGuardOperands.fetched other extra vector point controls code.probe.operands
      state.stable.scratch.stack needle handles.size state.ordinalWord state.stable.directory (Nat.le_refl _)
    rw [dif_neg (Nat.lt_irrefl _)] at closed
    obtain ⟨rfl, ⟨atFinish⟩⟩ := closed
    let answer := scan (adjust q count) []
    have stack := (readFrame.lookup 4 (by decide)).trans state.stable.scratch.stack
    obtain ⟨b, work, finished, testFrame, ⟨atReturn⟩⟩ := NativeGuardCursor.fetched_finish other extra vector q atFinish
      (controls.transport readFrame NativeGuardOperands.clobbers_data) code.finish frame stack count countFits
      (state.counterWord.preserved readFrame (by simp)) ((readFrame.lookup 12 (by decide)).trans state.stable.scratch.zero)
    obtain ⟨after, returned, returnFrame, bit, done⟩ := fetched_return_bit other extra vector code answer atReturn
    have readOnly : X86StateFrame.Frame (NativeGuardOperands.clobbers ∪ NativeGuardCursor.clobbers ∪
        NativeResolveTest.returnClobbers 0) ∅ before after :=
      ((readFrame.trans testFrame).trans returnFrame).mono (Finset.Subset.refl _) (by simp)
    have all : X86StateFrame.Frame clobbers ∅ before after := readOnly.mono (by decide) (Finset.Subset.refl _)
    have ran := X86FuelPrefix.fetches_then (5 + work) 2 before b after
      (X86FuelPrefix.fetches_then 5 work before a b fetched finished) returned
    have noTags : tags.drop handles.size = [] := by
      apply List.drop_of_length_le
      simp [tags]
    refine ⟨after, _, ∅, ran, all.mono (Finset.Subset.refl _) (by simp), .idle,
      state.stable.preserved readOnly (by decide) (by decide) (by decide), ?_, done⟩
    change lookup after 0 = some (booleanWord (scan (adjust q count) (tags.drop handles.size)))
    rw [noTags]
    exact bit
  | @stop i count answer can decisive =>
    obtain ⟨a, first, touched, visited, visitedFrame, workspaceWrites, stable, performed⟩ :=
      fetched_visit other extra vector code point controls space room symbols pattern item normalized i count state countFits can
    rw [decisive] at performed
    obtain ⟨atReturn⟩ := performed
    obtain ⟨after, returned, returnFrame, bit, done⟩ := fetched_return_bit other extra vector code answer atReturn
    refine ⟨after, first + 2, touched, X86FuelPrefix.fetches_then first 2 before a after visited returned,
      (visitedFrame.trans returnFrame).mono (by decide) (by simp), workspaceWrites,
      stable.preserved returnFrame (by decide) (by decide) (by decide), ?_, done⟩
    have said := scan_stop (fun i => specification pattern (item i)) i q count answer decisive
    exact bit.trans (congrArg (fun ok => some (booleanWord ok)) said.symm)
  | @more i count later can proceeds suffix ih =>
    obtain ⟨a, first, touched, visited, visitedFrame, workspaceWrites, _, performed⟩ :=
      fetched_visit other extra vector code point controls space room symbols pattern item normalized i count state countFits can
    rw [proceeds] at performed
    obtain ⟨updated, ⟨again⟩⟩ := performed
    have laterFits := lt_of_le_of_lt (counter_nonincreasing q (specification pattern (item i)) count later proceeds) countFits
    obtain ⟨after, rest, tailWrites, resumed, tailFrame, writes, stable, bit, done⟩ :=
      ih again (controls.transport visitedFrame clobbers_data) updated laterFits
    have all := mergeWork visitedFrame tailFrame
    refine ⟨after, first + rest, touched ∪ tailWrites, X86FuelPrefix.fetches_then first rest before a after visited resumed,
      all, .union workspaceWrites writes, stable, ?_, done⟩
    have said := scan_more (fun i => specification pattern (item i)) i q count later proceeds
    exact bit.trans (congrArg (fun ok => some (booleanWord ok)) said.symm)

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardLoop
