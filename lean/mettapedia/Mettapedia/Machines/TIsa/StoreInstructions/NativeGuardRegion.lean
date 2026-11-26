import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardLoop
import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardEntry
import Mettapedia.Machines.TIsa.StoreInstructions.PackedGuardRoots

/-!
# Lowering an all-solutions TEST from a normalized occurrence view

Every native operand decodes to the corresponding term under
the current principal substitution. The scan and the source
instruction therefore observe the same occurrences. A target
larger than a machine word cannot be their count, so that case
emits a normal false result without entering the scan.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardRegion

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeGuardState (Stable Geometry counters)
open NativeGuardLoop (Normalized CanProbe Plan)
open NativeGuardPolicy (scan)
open NativeSolverStep (Writes)
open NativeResolveTest (ReturnPlaced returnCode)
open SolverGuardTrichotomy (Observation specification)
open IndexedGuard (Query)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def endAt (query : Query) (start : ℕ) : ℕ :=
  if query.target < 2 ^ 64 then NativeGuardLoop.endAt query (start + 27) else start + 11

def emit (query : Query) (start next exhausted malformed : ℕ) : List ℕ :=
  if query.target < 2 ^ 64 then
    NativeGuardEntry.emit (BitVec.ofNat 64 query.target) ++ NativeGuardLoop.emit query (start + 27) next exhausted malformed
  else returnCode 0 0 start next

theorem emit_end (query : Query) (start next exhausted malformed : ℕ) :
    start + (emit query start next exhausted malformed).length = endAt query start := by
  by_cases fits : query.target < 2 ^ 64
  · simp only [emit, endAt, if_pos fits, List.length_append, NativeGuardEntry.emit_size, ← Nat.add_assoc, NativeGuardLoop.emit_end]
  · simp only [emit, endAt, if_neg fits, NativeResolveTest.return_size]

inductive Placed (image : NativeImage.View) (query : Query) (start next exhausted malformed : ℕ) : Prop
  | normal (fits : query.target < 2 ^ 64) :
      NativeGuardEntry.Placed image start (BitVec.ofNat 64 query.target) →
      NativeGuardLoop.Placed image query (start + 27) next exhausted malformed →
      Placed image query start next exhausted malformed
  | wide (large : ¬ query.target < 2 ^ 64) :
      ReturnPlaced image 0 0 start next → Placed image query start next exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (query : Query) (start next exhausted malformed : ℕ)
    (extent : endAt query start ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit query start next exhausted malformed)) : Placed image query start next exhausted malformed := by
  by_cases fits : query.target < 2 ^ 64
  · simp only [emit, endAt, if_pos fits] at code extent
    obtain ⟨entry, body⟩ := NativeWords.code_append code
    rw [NativeGuardEntry.emit_size] at body
    have room := extent
    unfold NativeGuardLoop.endAt NativeGuardLoop.failAt NativeGuardLoop.passAt NativeGuardLoop.finishAt NativeGuardLoop.advanceAt
      NativeGuardLoop.policyAt NativeGuardLoop.solverAt NativeSolverImage.finish NativeSolverImage.bindingAt NativeSolverImage.shared
      NativeSolverImage.expandAt at room
    exact .normal fits (NativeGuardEntry.placed_of_emitted image _ _ (by omega) entry)
      (NativeGuardLoop.placed_of_emitted image _ _ _ _ _ extent target lack bad short body)
  · simp only [emit, endAt, if_neg fits] at code extent
    exact .wide fits (NativeResolveTest.return_placed image _ _ _ _ extent target short code)

noncomputable abbrev handlers := X86IndexedAddress.handlers

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def operand (answer : Subst σ) (atoms : List (SymbolicExecution.Atom σ)) {handles : Array Word}
    (width : handles.size = atoms.length) (i : Fin handles.size) : Term σ :=
  answer.applyTerm (atoms[i.val]'(width ▸ i.isLt)).2

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- A packed binding trail constructs the normalized view;
it need not be asserted independently of the original store. -/
theorem prepare_packed (symbols : UnifierHeaders.Symbols σ)
    (snapshot : PackedTerms.Arena) (raw : PackedWorklist.Words) (trail : Derivation.FiniteUnifier.Trail σ)
    (canonical : PackedGuardRoots.Canonical symbols snapshot raw trail)
    (current : PackedGuardRoots.State) (pattern : Term σ) (atoms : List (SymbolicExecution.Atom σ))
    (decoded : PackedGuardRoots.Decodes symbols current pattern (atoms.map Prod.snd))
    (held : PackedSubstitution.Keeps symbols snapshot current.arena) (slack : ℕ)
    (budget : PackedWorklist.Reserve (raw.length + slack) current.arena.nodes.size current.arena.children.size) :
    let answer := Derivation.FiniteUnifier.readTrail (Subst.id σ) trail
    ∃ out, PackedGuardRoots.replay raw current = some out ∧ PackedSubstitution.Keeps symbols snapshot out.arena ∧
      PackedWorklist.Reserve slack out.arena.nodes.size out.arena.children.size ∧
      ∃ width : out.occurrences.size = atoms.length,
        Normalized symbols out.arena out.pattern out.occurrences (answer.applyTerm pattern) (operand answer atoms width) := by
  dsimp only
  obtain ⟨out, ran, kept, _, reserve, normalized⟩ :=
    PackedGuardRoots.replay_exact symbols snapshot raw trail canonical current pattern (atoms.map Prod.snd)
      decoded held slack budget
  obtain ⟨width, coordinates⟩ := normalized.coordinates
  have complete : out.occurrences.size = atoms.length := by simpa using width
  refine ⟨out, ran, kept, reserve, complete, ⟨normalized.patternWord, fun i => ?_⟩⟩
  simpa only [Fin.getElem_fin, List.getElem_map, operand] using coordinates i

theorem scan_grounded (answer : Subst σ) (atoms : List (SymbolicExecution.Atom σ)) (pattern : Term σ)
    {handles : Array Word} (width : handles.size = atoms.length) (query : Query) :
    scan query (List.ofFn (fun i => specification (answer.applyTerm pattern) (operand answer atoms width i))) =
      SymbolicExecution.guard answer atoms (query.check pattern) := by
  have tags : List.ofFn (fun i => specification (answer.applyTerm pattern) (operand answer atoms width i)) =
      atoms.map (fun o => specification (answer.applyTerm pattern) (answer.applyTerm o.2)) := by
    apply List.ext_getElem
    · simp [width]
    · intro i a b
      simp only [List.getElem_ofFn, List.getElem_map, operand]
  let classify (a : SymbolicExecution.Atom σ) := specification (answer.applyTerm pattern) (answer.applyTerm a.2)
  have must : Observation.must ∘ classify = SymbolicExecution.assured answer pattern := by
    funext a
    exact SolverGuardTrichotomy.must_exact _ _
  have may : Observation.may ∘ classify = SymbolicExecution.possible answer pattern := by
    funext a
    simpa only [Function.comp_apply, classify, SymbolicExecution.possible, unifyTotalStructural_eq_unifyTotal] using
      SolverGuardTrichotomy.may_exact (answer.applyTerm pattern) (answer.applyTerm a.2)
  unfold scan
  rw [tags, SymbolicGuardScan.scan_map, must, may]
  cases query <;> rfl

theorem count_false_of_fewer_occurrences (tags : List Observation) (n : ℕ) (few : tags.length < n) :
    scan (.count n) tags = false := by
  cases verdict : scan (.count n) tags
  · rfl
  · have count := (SymbolicGuardScan.countRemaining_correct Observation.must Observation.may n tags).mp verdict
    have limit : n ≤ tags.length := count.1 ▸ List.countP_le_length
    exact (Nat.not_le_of_lt few limit).elim

/-- With only a suffix length known, no smaller upper bound
on the number of certain occurrences is valid. -/
theorem count_possible_at_length (n slots : ℕ) :
    (∃ tags : List Observation, tags.length = slots ∧ scan (.count n) tags = true) ↔ n ≤ slots := by
  constructor
  · rintro ⟨tags, width, succeeds⟩
    by_contra gt
    have falseBit := count_false_of_fewer_occurrences tags n (width ▸ Nat.lt_of_not_ge gt)
    rw [falseBit] at succeeds
    contradiction
  · intro h
    let tags := List.replicate n Observation.assured ++ List.replicate (slots - n) Observation.impossible
    refine ⟨tags, ?_, (SymbolicGuardScan.countRemaining_correct Observation.must Observation.may n tags).2 ⟨?_, ?_⟩⟩
    · simp only [tags, List.length_append, List.length_replicate]
      omega
    · simp [tags, List.countP_replicate, Observation.must]
    · intro seen member can
      simp only [tags, List.mem_append] at member
      rcases member with here | there
      · obtain rfl := List.eq_of_mem_replicate here
        rfl
      · obtain rfl := List.eq_of_mem_replicate there
        cases can

private theorem impossible_target (query : Query) (tags : List Observation) (fits : tags.length < 2 ^ 64)
    (wide : ¬ query.target < 2 ^ 64) : scan query tags = false := by
  cases query with
  | any => exact (wide (by decide)).elim
  | absent => exact (wide (by decide)).elim
  | count target => exact count_false_of_fewer_occurrences tags target (fits.trans_le (Nat.le_of_not_gt wide))

private theorem test_bit (base : SymbolicExecution.Equations σ) (state : SymbolicExecution.Frame σ) (level : ℕ)
    (destination : P1Source.Reg) (query : Query) (pattern : Term σ) (answer : Subst σ)
    (resolved : (state.levels level).bindings.answer = some answer) :
    executeInstructionWith (SymbolicExecution.profile base).step state
        (.transform (.test (.perform (.check (query.check pattern))) level destination)) =
      .ok (state.write destination (booleanWord (SymbolicExecution.guard answer state.store.occurrences (query.check pattern)))) := by
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, SymbolicExecution.profile,
    SymbolicExecution.test, resolved]
  cases SymbolicExecution.guard answer state.store.occurrences (query.check pattern) <;>
    simp [StoreInstructions.State.setLevel, Function.update_eq_self, booleanWord]

variable {nc ec mc ac tc occ : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame} {table : Region occ}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}

private theorem entryClobbers : NativeGuardEntry.clobbers ⊆ NativeGuardLoop.clobbers := by decide

private theorem returnClobbers : NativeResolveTest.returnClobbers 0 ⊆ NativeGuardLoop.clobbers := by decide

private theorem keepsCounters {left right privateWork : Finset ℕ} :
    (left ∪ right) ∪ (privateWork ∪ (left ∪ right)) ⊆ privateWork ∪ (left ∪ right) :=
  Finset.union_subset Finset.subset_union_right (Finset.Subset.refl _)

private theorem adjust_target (query : Query) : NativeGuardPolicy.adjust query query.target = query := by
  cases query <;> rfl

/-- A native guard reads the same observation as its source
TEST. The normalized view and principal answer are inputs
from the firing that owns this guard. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next exhausted malformed : ℕ} {before : Native}
    (query : Query) (code : Placed image query start next exhausted malformed)
    (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail table image base) (room : 0 < ac)
    (symbols : UnifierHeaders.Symbols σ) (source : PackedTerms.Arena) (needle : Word) (handles : Array Word)
    (state : SymbolicExecution.Frame σ) (knowledge : SymbolicExecution.Equations σ)
    (level : ℕ) (destination : P1Source.Reg) (pattern : Term σ) (answer : Subst σ)
    (resolved : (state.levels level).bindings.answer = some answer)
    (width : handles.size = state.store.occurrences.length)
    (ready : Stable term map frame agenda trail table source needle handles before)
    (view : Normalized symbols source needle handles (answer.applyTerm pattern) (operand answer state.store.occurrences width))
    (plan : query.target < 2 ^ 64 →
      Plan query (fun i => specification (answer.applyTerm pattern) (operand answer state.store.occurrences width i))
        (fun i => CanProbe nc ec mc ac tc source needle handles[i.val]) 0 query.target) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work abstract, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame NativeGuardLoop.clobbers (work ∪ counters frame) before after ∧
      Writes term map frame.solver agenda trail work ∧ Stable term map frame agenda trail table source needle handles after ∧
      executeInstructionWith (SymbolicExecution.profile knowledge).step state
        (.transform (.test (.perform (.check (query.check pattern))) level destination)) = .ok abstract ∧
      lookup after 0 = some (abstract.machine.registers destination) ∧ abstract.store = state.store ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let atoms := state.store.occurrences
  let tags := List.ofFn (fun i => specification (answer.applyTerm pattern) (operand answer atoms width i))
  let bit := SymbolicExecution.guard answer atoms (query.check pattern)
  let abstract := state.write destination (booleanWord bit)
  have checked := test_bit knowledge state level destination query pattern answer resolved
  have known : scan query tags = bit := scan_grounded answer atoms pattern width query
  have virtual : abstract.machine.registers destination = booleanWord bit := by
    simp [abstract, StoreInstructions.State.write, P1WordExecution.State.write]
  cases code with
  | normal fit entry body =>
    obtain ⟨a, entered, entryFrame, initial, ⟨atLoop⟩⟩ := NativeGuardEntry.fetched other extra vector point controls
      query.target entry space source needle handles ready
    obtain ⟨after, steps, work, scanned, bodyFrame, writes, stable, result, endpoint⟩ :=
      NativeGuardLoop.fetched other extra vector body space room symbols _ _ view atLoop
        (controls.transport entryFrame NativeGuardEntry.clobbers_data) initial fit (plan fit)
    have all : X86StateFrame.Frame NativeGuardLoop.clobbers (work ∪ counters frame) before after := by
      exact (entryFrame.trans bodyFrame).mono (Finset.union_subset entryClobbers (Finset.Subset.refl _)) keepsCounters
    have bitExact : scan (NativeGuardPolicy.adjust query query.target) (tags.drop 0) = bit :=
      (congrArg (fun q => scan q tags) (adjust_target query)).trans known
    have actual : lookup after 0 = some (abstract.machine.registers destination) :=
      (result.trans (congrArg (fun yes => some (booleanWord yes)) bitExact)).trans (congrArg some virtual.symm)
    exact ⟨after, _, work, abstract, X86FuelPrefix.fetches_then 4 steps before a after entered scanned, all, writes, stable,
      checked, actual, rfl, endpoint⟩
  | wide large returned =>
    obtain ⟨after, ran, returnedFrame, result, endpoint⟩ :=
      NativeResolveTest.fetched_return other extra vector point 0 0 returned
    have fits : tags.length < 2 ^ 64 := by
      have exactCount := NativeSubstitutionReserve.word_of_region table handles.size ready.directory.occurrences.fits
      have countFits := (BitVec.ofNat 64 handles.size).isLt
      rw [exactCount] at countFits
      simpa [tags] using countFits
    have falseBit : bit = false := known.symm.trans (impossible_target query tags fits large)
    have actual : lookup after 0 = some (abstract.machine.registers destination) := by
      rw [virtual, falseBit]
      exact result
    exact ⟨after, 2, ∅, abstract, ran, returnedFrame.mono returnClobbers (Finset.empty_subset _), .idle,
      ready.preserved returnedFrame (by decide) (by decide) (by decide), checked, actual, rfl, endpoint⟩

namespace Examples

theorem two_certain_occurrences_count_twice :
    scan (.count 2) [.assured, .assured] = true := by decide +kernel

theorem one_uncertain_occurrence_prevents_an_exact_count :
    scan (.count 1) [.assured, .possible] = false := by decide +kernel

theorem a_wide_target_returns_false_without_emitting_a_scan :
    emit (.count (2 ^ 64)) 0 11 11 11 = returnCode 0 0 0 11 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardRegion
