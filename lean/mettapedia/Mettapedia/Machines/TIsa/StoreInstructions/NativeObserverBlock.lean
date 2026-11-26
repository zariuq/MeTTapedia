import Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverSelect
import Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectRegion

/-!
# Native observers of a rooted resolution

A block selects its pattern and runs the appropriate
observer over the borrowed occurrence window. All count,
presence, absence, and collection results refer to the
same original occurrence list. Rooted resolution supplies
the actually normalized graph; the source store is not
materialized again for any observer.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverBlock

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads Cell CodeApart footprint)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeBindingRootMemory (Covered)
open NativeLiveRootEntry (Descriptor Held)
open NativeGuardInstall (guardFrame)
open NativeGuardState (Stable counters)
open NativeGuardLoop (CanProbe)
open NativeObserverSelect (Mode)
open NativeRootSlices (View)
open NativeSolverStep (Writes)
open IndexedGuard (Query)
open SolverGuardTrichotomy (specification)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Observer where
  | check (query : Query)
  | collect

def Observer.emit (which : Observer) (start next exhausted malformed : ℕ) : List ℕ :=
  match which with
  | .check query => NativeGuardRegion.emit query start next exhausted malformed
  | .collect => NativeCollectRegion.emit start next exhausted malformed

def Observer.endAt (which : Observer) (start : ℕ) : ℕ :=
  match which with
  | .check query => NativeGuardRegion.endAt query start
  | .collect => NativeCollectRegion.endAt start

theorem Observer.emit_end (which : Observer) (start next exhausted malformed : ℕ) :
    start + (which.emit start next exhausted malformed).length = which.endAt start := by
  cases which
  · exact NativeGuardRegion.emit_end _ _ _ _ _
  · exact NativeCollectRegion.emit_end _ _ _ _

private theorem guard_prefix (start : ℕ) : start ≤ NativeGuardLoop.policyAt start := by
  unfold NativeGuardLoop.policyAt NativeGuardLoop.solverAt NativeSolverImage.finish NativeSolverImage.bindingAt
    NativeSolverImage.shared NativeSolverImage.expandAt
  omega

theorem Observer.start_le_end (which : Observer) (start : ℕ) : start ≤ which.endAt start := by
  cases which with
  | check query =>
    change start ≤ NativeGuardRegion.endAt query start
    unfold NativeGuardRegion.endAt
    split
    · have lower := guard_prefix (start + 27)
      unfold NativeGuardLoop.endAt NativeGuardLoop.failAt NativeGuardLoop.passAt NativeGuardLoop.finishAt NativeGuardLoop.advanceAt
      omega
    · omega
  | collect =>
    have lower := guard_prefix (start + 27)
    change start ≤ NativeCollectRegion.endAt start
    unfold NativeCollectRegion.endAt NativeCollectLoop.endAt NativeCollectLoop.failAt NativeCollectLoop.passAt NativeCollectLoop.advanceAt
      NativeCollectLoop.markAt
    omega

def Observer.Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Observer → Prop
  | .check query => NativeGuardRegion.Placed image query start next exhausted malformed
  | .collect => NativeCollectRegion.Placed image start next exhausted malformed

def emit (mode : Mode) (pattern offset count : ℕ) (which : Observer) (start next exhausted malformed : ℕ) : List ℕ :=
  NativeObserverSelect.emit mode pattern offset count ++ which.emit (start + mode.size) next exhausted malformed

theorem emit_end (mode : Mode) (pattern offset count : ℕ) (which : Observer) (start next exhausted malformed : ℕ) :
    start + (emit mode pattern offset count which start next exhausted malformed).length = which.endAt (start + mode.size) := by
  simp only [emit, List.length_append, ← Nat.add_assoc, NativeObserverSelect.emit_size, Observer.emit_end]

structure Placed (image : NativeImage.View) (mode : Mode) (pattern offset count : ℕ) (which : Observer)
    (start next exhausted malformed : ℕ) : Prop where
  select : NativeObserverSelect.Placed image start pattern offset count mode
  body : Observer.Placed image (start + mode.size) next exhausted malformed which

theorem placed_of_emitted (image : NativeImage.View) (mode : Mode) (pattern offset count : ℕ)
    (which : Observer) (start next exhausted malformed : ℕ)
    (extent : which.endAt (start + mode.size) ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit mode pattern offset count which start next exhausted malformed)) :
    Placed image mode pattern offset count which start next exhausted malformed := by
  obtain ⟨select, body⟩ := NativeWords.code_append (show Code image start
    (NativeObserverSelect.emit mode pattern offset count ++ _) from installed)
  rw [NativeObserverSelect.emit_size] at body
  refine ⟨NativeObserverSelect.placed_of_emitted image mode _ _ _ _ ((which.start_le_end _).trans extent) select, ?_⟩
  cases which
  · exact NativeGuardRegion.placed_of_emitted image _ _ _ _ _ extent target lack bad short body
  · exact NativeCollectRegion.placed_of_emitted image _ _ _ _ extent target lack bad short body

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeGuardLoop.clobbers

private theorem select_clobbers : NativeObserverSelect.clobbers ⊆ clobbers := by decide

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

structure Request (σ : LPSignature.{u,u,p,u}) where
  state : SymbolicExecution.Frame σ
  program : SymbolicExecution.Equations σ
  patterns : List (Term σ)
  pattern : Fin patterns.length
  level : ℕ
  destination : P1Source.Reg
  answer : Subst σ
  resolved : (state.levels level).bindings.answer = some answer

def Request.atoms (r : Request σ) : List (SymbolicExecution.Atom σ) := r.state.store.occurrences
def Request.needle (r : Request σ) : Term σ := r.patterns[r.pattern]
def Request.operands (r : Request σ) : List (Term σ) := RootedObserverLayout.operands r.patterns r.atoms
def Request.view (r : Request σ) (words : Array Word) (size : words.size = r.patterns.length + r.atoms.length) : View words :=
  RootedObserverLayout.view r.patterns r.atoms words size r.pattern

private def Request.tag (r : Request σ) {words : Array Word} {size : words.size = r.patterns.length + r.atoms.length}
    (i : Fin (r.view words size).occurrences.size) :=
  specification (r.answer.applyTerm r.needle) (NativeGuardRegion.operand r.answer r.atoms (r.view words size).size i)

variable {nc ec mc ac tc rc out : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {graph : PackedTerms.Arena} {words : Array Word} {region : Region rc} {fits : words.size ≤ rc}
variable {d : Descriptor} {output : Region out} {pointer : Cell (guardFrame d).pointer 144}
variable {image : NativeImage.View} {base : BitVec 48}

/-- The first or later native guard executes after reading
the correct pattern of the retained root vector. -/
theorem fetched_guard (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (request : Request σ) (mode : Mode) (query : Query) (symbols : UnifierHeaders.Symbols σ)
    (size : words.size = request.patterns.length + request.atoms.length)
    (decoded : PackedRootedMeaning.roots symbols graph words = some (request.operands.map request.answer.applyTerm))
    (code : Placed image mode request.pattern.val request.patterns.length request.atoms.length (.check query) start next exhausted malformed)
    (point : At image before base start) (controls : Controls before)
    (input : NativeObserverSelect.Ready term map d agenda trail region words fits graph (request.view words size) before mode)
    (space : NativeGuardState.Geometry term map (guardFrame d) agenda trail ((request.view words size).region region fits) image base)
    (rootSpace : NativeBindingRootMemory.Geometry region d term map agenda trail image base)
    (apart : Separated region (guardFrame d).region) (safe : CodeApart image base (mode.writes (guardFrame d)))
    (room : 0 < ac)
    (plan : query.target < 2 ^ 64 →
      NativeGuardLoop.Plan query (request.tag (size := size)) (fun i => CanProbe nc ec mc ac tc graph (request.view words size).needle
        (request.view words size).occurrences[i.val]) 0 query.target) :
    let view := request.view words size
    let I := (SymbolicExecution.profile request.program).step
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work abstract, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (mode.writes (guardFrame d) ∪ (work ∪ counters (guardFrame d))) before after ∧
      Writes term map (guardFrame d).solver agenda trail work ∧
      Stable term map (guardFrame d) agenda trail (view.region region fits) graph view.needle view.occurrences after ∧
      Held d region words after ∧
      executeInstructionWith I request.state (.transform (.test (.perform (.check (query.check request.needle)))
        request.level request.destination)) = .ok abstract ∧
      lookup after 0 = some (abstract.machine.registers request.destination) ∧ abstract.store = request.state.store ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let v := request.view words size
  obtain ⟨a, selected, selectFrame, ready, held, ⟨atBody⟩⟩ := NativeObserverSelect.fetched other extra vector mode d v
    code.select point controls graph input space apart safe
  have normalized := RootedObserverLayout.normalized symbols graph words request.patterns request.atoms request.answer decoded size request.pattern
  obtain ⟨after, steps, work, abstract, observed, probeFrame, writes, stable, exact, bit, store, endpoint⟩ :=
    NativeGuardRegion.fetched other extra vector query code.body atBody
      (controls.transport selectFrame NativeObserverSelect.clobbers_data) space room symbols graph v.needle v.occurrences
      request.state request.program request.level request.destination request.needle request.answer request.resolved v.size ready normalized plan
  have hold := NativeObserverSelect.keep_roots rootSpace apart held writes (marks := ∅) (by simp) (by simp)
    (by simpa only [Finset.union_empty] using probeFrame)
  exact ⟨after, mode.cost + steps, work, abstract, X86FuelPrefix.fetches_then mode.cost steps before a after selected observed,
    (selectFrame.trans probeFrame).mono (Finset.union_subset select_clobbers (Finset.Subset.refl _)) (Finset.Subset.refl _),
    writes, stable, hold, exact, bit, store, endpoint⟩

/-- Collection uses the same setup and unifier. Its
success stores a private mask rather than a scalar answer. -/
theorem fetched_collect (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (request : Request σ) (mode : Mode) (symbols : UnifierHeaders.Symbols σ)
    (size : words.size = request.patterns.length + request.atoms.length)
    (decoded : PackedRootedMeaning.roots symbols graph words = some (request.operands.map request.answer.applyTerm))
    (code : Placed image mode request.pattern.val request.patterns.length request.atoms.length .collect start next exhausted malformed)
    (point : At image before base start) (controls : Controls before)
    (input : NativeObserverSelect.Ready term map d agenda trail region words fits graph (request.view words size) before mode)
    (space : NativeCollectMemory.Geometry term map (guardFrame d) agenda trail ((request.view words size).region region fits)
      output pointer image base)
    (rootSpace : NativeBindingRootMemory.Geometry region d term map agenda trail image base)
    (apart : Separated region (guardFrame d).region) (safe : CodeApart image base (mode.writes (guardFrame d)))
    (keepAll : Separated region output) (keepDescriptor : Separated d.region output)
    (privateBase : Reads before pointer.address (output.atWord 0))
    (keepPointer : Disjoint (footprint pointer.address) (mode.writes (guardFrame d)))
    (room : 0 < ac) (capacity : request.atoms.length ≤ out)
    (plan : NativeCollectLoop.Plan (request.tag (size := size)) (fun i => CanProbe nc ec mc ac tc graph (request.view words size).needle
      (request.view words size).occurrences[i.val]) 0) :
    let view := request.view words size
    let result := SymbolicExecution.collect request.answer request.atoms request.needle
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps work marks, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (mode.writes (guardFrame d) ∪ ((work ∪ marks) ∪ counters (guardFrame d))) before after ∧
      Writes term map (guardFrame d).solver agenda trail work ∧ Covered output marks ∧
      Stable term map (guardFrame d) agenda trail (view.region region fits) graph view.needle view.occurrences after ∧
      Held d region words after ∧
      NativeCollectRegion.Answer (guardFrame d) output pointer (request.atoms.map Prod.fst) after result ∧
      executeInstructionWith (SymbolicExecution.profile request.program).step request.state
        (.transform (.test (.perform (.collect request.needle)) request.level request.destination)) =
        .ok (NativeCollectRegion.applyResult request.state request.level request.destination result) ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let v := request.view words size
  obtain ⟨a, selected, selectFrame, ready, held, ⟨atBody⟩⟩ := NativeObserverSelect.fetched other extra vector mode d v
    code.select point controls graph input space.guard apart safe
  have normalized := RootedObserverLayout.normalized symbols graph words request.patterns request.atoms request.answer decoded size request.pattern
  obtain ⟨after, steps, work, marks, observed, probeFrame, writes, marked, stable, answered, exact, endpoint⟩ :=
    NativeCollectRegion.fetched other extra vector code.body atBody
      (controls.transport selectFrame NativeObserverSelect.clobbers_data) space room symbols graph v.needle v.occurrences
      request.state request.program request.level request.destination request.needle request.answer request.resolved v.size
      (v.size ▸ capacity) ready normalized plan (privateBase.preserved selectFrame keepPointer)
  have retained := NativeObserverSelect.keep_roots rootSpace apart held writes
    (fun i => Covered.separate keepAll (Covered.word region i) marked)
    (fun i _ => Covered.separate keepDescriptor (Covered.field d i) marked) probeFrame
  exact ⟨after, mode.cost + steps, work, marks, X86FuelPrefix.fetches_then mode.cost steps before a after selected observed,
    (selectFrame.trans probeFrame).mono (Finset.union_subset select_clobbers (Finset.Subset.refl _)) (Finset.Subset.refl _),
    writes, marked, stable, retained, answered, exact, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverBlock
