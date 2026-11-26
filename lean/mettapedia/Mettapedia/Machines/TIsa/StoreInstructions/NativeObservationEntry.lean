import Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedResolution
import Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverBlock

/-!
# Resolution either refuses or enters the first observer

The emitted conditional depends on the actual native
resolution bit. A failed solve skips observation. A
successful solve supplies the original roots under the
principal answer and the initialized graph descriptor
needed for first observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeObservationEntry

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch)
open NativeArenaGeometry (Region)
open NativeLiveRootEntry (Descriptor Held)
open NativeGuardInstall (guardFrame)
open NativeBindingStep (Live)
open NativeBindingRootMemory (Covered Geometry)
open NativeSolverResources (Budget)
open NativeSolverStep (Writes)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def branchAt (start : ℕ) : ℕ := NativeRootedResolution.endAt start
def observerAt (start : ℕ) : ℕ := branchAt start + 9

def emit (start refused exhausted malformed : ℕ) : List ℕ :=
  NativeRootedResolution.emit start (branchAt start) exhausted malformed ++
    NativeDecisions.compareBytes .notEqual 0 12 (branchAt start) refused

theorem emit_end (start refused exhausted malformed : ℕ) :
    start + (emit start refused exhausted malformed).length = observerAt start := by
  simp only [emit, List.length_append, ← Nat.add_assoc, NativeRootedResolution.extent, NativeDecisions.compare_size, observerAt, branchAt]

structure Placed (image : NativeImage.View) (start refused exhausted malformed : ℕ) : Prop where
  resolution : NativeRootedResolution.Placed image start (branchAt start) exhausted malformed
  branch : CompareBranch image (branchAt start) refused .notEqual 0 12

theorem placed_of_emitted (image : NativeImage.View) (start refused exhausted malformed : ℕ)
    (extent : observerAt start ≤ image.size) (denied : refused ≤ image.size) (lack : exhausted ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start refused exhausted malformed)) : Placed image start refused exhausted malformed := by
  obtain ⟨resolve, branch⟩ := NativeWords.code_append (show Code image start
    (NativeRootedResolution.emit start (branchAt start) exhausted malformed ++ _) from code)
  rw [NativeRootedResolution.extent] at branch
  have atBranch : branchAt start ≤ image.size := (Nat.le_add_right _ _).trans extent
  exact ⟨NativeRootedResolution.placed_of_emitted image _ _ _ _ atBranch atBranch lack bad short resolve,
    NativeDecisions.compare_placed image _ _ _ _ _ extent denied short branch⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeRootedResolution.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide
theorem keeps_zero : key (12 : Fin 16) ∉ clobbers := by decide
private theorem compare_regs : ({.rflags, .rip} : Finset Register) ⊆ clobbers := by decide

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def sourceResult (state : SymbolicExecution.Frame σ) (level : ℕ) (target : P1Source.Reg) :
    Option (Subst σ) → SymbolicExecution.Frame σ
  | none => state.write target 0
  | some answer =>
    let entry := state.levels level
    (state.setLevel level {entry with bindings := {entry.bindings with answer := some answer}}).write target 1

theorem source_resolved (state : SymbolicExecution.Frame σ) (level : ℕ) (target : P1Source.Reg) (answer : Subst σ) :
    ((sourceResult state level target (some answer)).levels level).bindings.answer = some answer := by
  simp [sourceResult, StoreInstructions.State.write, StoreInstructions.State.setLevel]

theorem source_store (state : SymbolicExecution.Frame σ) (level : ℕ) (target : P1Source.Reg) (answer : Option (Subst σ)) :
    (sourceResult state level target answer).store = state.store := by cases answer <;> rfl

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {rootRegion : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

def Routed (symbols : UnifierHeaders.Symbols σ) (d : Descriptor) (rootRegion : Region rc)
    (term : NativeTermArena.Layout nc ec) (map : Region mc) (agenda : NativeAgendaRecords.Layout ac)
    (trail : NativeAgendaRecords.Layout tc) (image : NativeImage.View) (base : BitVec 48)
    (start refused : ℕ) (original : List (Term σ)) (native : Native) : Option (Subst σ) → Prop
  | none => lookup native 0 = some 0 ∧ Nonempty (At image native base refused)
  | some ans =>
    ∃ (graph : PackedTerms.Arena) (words : Array Word),
      NativeGuardInstall.Input term map (guardFrame d) agenda trail d rootRegion graph words native ∧
      PackedRootedMeaning.roots symbols graph words = some (original.map ans.applyTerm) ∧
      Nonempty (At image native base (observerAt start))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Resolve from the encoded inputs, then use the emitted
conditional to reach exactly the source's next phase. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start refused exhausted malformed : ℕ} {before : Native}
    (code : Placed image start refused exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : NativeBindingMemory.Geometry term map d.solver agenda trail image base)
    (rootSpace : Geometry rootRegion d term map agenda trail image base)
    (symbols : UnifierHeaders.Symbols σ) (terms : PackedTerms.Arena) (stored oldTrail : Arena)
    (localRoot baseRoot : Word) (newer originalBase : Words)
    (live : Live term map d.solver agenda trail terms stored localRoot oldTrail before)
    (basePointer : lookup before 7 = some baseRoot)
    (localChain : readWords stored localRoot = some newer) (baseChain : readWords stored baseRoot = some originalBase.reverse)
    (trailEmpty : readWords oldTrail (NativeBindingTrail.root oldTrail) = some [])
    (facts : SymbolicExecution.Equations σ) (state : SymbolicExecution.Frame σ) (level : ℕ) (target : P1Source.Reg)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (baseRead : PackedWorklist.readEquations symbols terms originalBase = some facts)
    (source : PackedEquations.read (PackedTerms.codebook decoded) stored localRoot = some (state.levels level).bindings.newer)
    (old : Array Word) (original : List (Term σ)) (retained : Held d rootRegion old before)
    (readRoots : PackedRootedMeaning.roots symbols terms old = some original)
    (savedAgenda : Reads before ((guardFrame d).cell 10).address agenda.words.pointer)
    (fuel : ℕ) (wordBudget : PackedWorklist.Reserve fuel terms.nodes.size terms.children.size)
    (needed : Budget)
    (plan : NativeSolverResources.planned fuel (stored.size + (newer.length + originalBase.length)) oldTrail.size
      (.working ⟨terms, originalBase ++ newer.reverse, []⟩) = some needed)
    (available : needed.Within ⟨nc, ec, mc, ac, tc⟩) :
    let solution := unifyTotal ((state.levels level).bindings.problem facts)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps scratch rootWrites, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (scratch ∪ rootWrites) before after ∧ Writes term map d.solver agenda trail scratch ∧
      Covered rootRegion rootWrites ∧ NativeTermArena.Ready term terms after ∧
      executeInstructionWith (SymbolicExecution.profile facts).step state (.transform (.test .resolve level target)) =
        .ok (sourceResult state level target solution) ∧
      Routed symbols d rootRegion term map agenda trail image base start refused original after solution := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let solution := unifyTotal ((state.levels level).bindings.problem facts)
  obtain ⟨middle, steps, scratch, rootWrites, ran, framed, writes, roots, oldGraph, result, exact, ⟨atBranch⟩⟩ :=
    NativeRootedResolution.fetched other extra vector code.resolution point controls space rootSpace symbols terms stored oldTrail
      localRoot baseRoot newer originalBase live basePointer localChain baseChain trailEmpty facts state level target interned baseRead
      source old original retained readRoots fuel wordBudget needed plan available
  have zero := (framed.lookup 12 keeps_zero).trans live.dispatch.zero
  have saved : Reads middle ((guardFrame d).cell 10).address agenda.words.pointer := by
    rw [NativeGuardInstall.guard_field] at savedAgenda ⊢
    exact savedAgenda.preserved framed (Finset.disjoint_union_right.mpr ⟨
      NativeRootedSolverStep.keep_writes rootSpace.descriptor (Covered.field d 10)
        (NativeBindingRootMemory.descriptor_lengths d 10 (by decide) (by decide)) writes,
      Covered.separate rootSpace.rootFrame.symm (Covered.field d 10) roots⟩)
  have finished : ∃ after, (X86FuelPrefix.fetches 2).run middle = .ok () after ∧
      X86StateFrame.Frame {.rflags, .rip} ∅ middle after ∧
      Routed symbols d rootRegion term map agenda trail image base start refused original after solution := by
    change NativeRootedResolution.Answer _ _ _ _ _ _ _ _ _ solution at result
    cases selected : solution with
    | none =>
      rw [selected] at result
      obtain ⟨after, ran, compared, ⟨refuse⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
        extra vector atBranch .notEqual 0 12 code.branch 0 0 result zero
      have only := X86StateFrame.registerOnly compared
      exact ⟨after, ran, only, (only.lookup 0 (by decide)).trans result, ⟨refuse⟩⟩
    | some answer =>
      rw [selected] at result
      obtain ⟨bit, graph, words, _, _, _, originalGraph, held, _, staged, aux, _, one, _, _, _, correct⟩ := result
      obtain ⟨after, ran, compared, ⟨accept⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
        extra vector atBranch .notEqual 0 12 code.branch 1 0 bit zero
      have only := X86StateFrame.registerOnly compared
      exact ⟨after, ran, only, graph, words, ⟨rfl, originalGraph.preserved only,
        ⟨held.descriptor.kept only (by simp) (by simp), held.words.preserved only⟩, staged.preserved only (by decide), aux.preserved only,
        saved.preserved only (by simp), (only.lookup 12 (by decide)).trans zero, (only.lookup 13 (by decide)).trans one⟩,
        correct, ⟨accept⟩⟩
  obtain ⟨after, branch, regs, routed⟩ := finished
  exact ⟨after, steps + 2, scratch, rootWrites, X86FuelPrefix.fetches_then steps 2 before middle after ran branch,
    (framed.trans regs).mono (Finset.union_subset (Finset.Subset.refl _) compare_regs) (by rw [Finset.union_empty]),
    writes, roots, oldGraph.preserved regs, exact, routed⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeObservationEntry
