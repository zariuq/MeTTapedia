import Mettapedia.Machines.TIsa.StoreInstructions.NativeResolvePrepare
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverRun
import Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedMeaning

/-!
# From original equation chains to normalized native roots

Prepare the equations with the ordinary resolution prefix.
Then retain the caller's roots through binding rather than
replaying the trail after success. The returned true bit
comes with a physical vector for exactly the original terms
under the principal answer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedResolution

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeLiveRootEntry (Descriptor Held)
open NativeBindingStep (Live)
open NativeBindingRootMemory (Geometry Covered)
open NativeSolverStep (Arrived Writes clobbers_data handlers)
open NativeSolverResources (Budget)
open NativeResolveTest (ReturnPlaced returnCode return_size returnClobbers)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def atSolver (start : ℕ) : ℕ := start + 505
def atAccept (start : ℕ) : ℕ := NativeSolverImage.finishRooted (atSolver start)
def atRefuse (start : ℕ) : ℕ := atAccept start + 11
def endAt (start : ℕ) : ℕ := atRefuse start + 11

def exits (start exhausted malformed : ℕ) : NativeSolverImage.Exits :=
  ⟨atAccept start, atRefuse start, atRefuse start, exhausted, malformed⟩

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeResolvePrepare.emit start (atSolver start) exhausted malformed ++
    (NativeSolverImage.emitRooted (atSolver start) (exits start exhausted malformed) ++
      (returnCode 0 1 (atAccept start) next ++ returnCode 0 0 (atRefuse start) next))

theorem extent (start next exhausted malformed : ℕ) : start + (emit start next exhausted malformed).length = endAt start := by
  simp only [emit, List.length_append, NativeResolvePrepare.emit_size, return_size, ← Nat.add_assoc]
  change (atSolver start + (NativeSolverImage.emitRooted (atSolver start) (exits start exhausted malformed)).length) + 11 + 11 =
    endAt start
  rw [NativeSolverImage.emitRooted_size]
  rfl

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  prepare : NativeResolvePrepare.Placed image start (atSolver start) exhausted malformed
  solver : NativeSolverImage.RootedPlaced image (atSolver start) (exits start exhausted malformed)
  accepted : ReturnPlaced image 0 1 (atAccept start) next
  refused : ReturnPlaced image 0 0 (atRefuse start) next

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (space : endAt start ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨prepare, rest⟩ := NativeWords.code_append (show Code image start
    (NativeResolvePrepare.emit start (atSolver start) exhausted malformed ++ _) from bytes)
  rw [NativeResolvePrepare.emit_size] at rest
  change Code image (atSolver start) _ at rest
  obtain ⟨solver, rest⟩ := NativeWords.code_append rest
  rw [NativeSolverImage.emitRooted_size] at rest
  obtain ⟨yes, no⟩ := NativeWords.code_append rest
  rw [return_size] at no
  have lower : start + 505 ≤ atAccept start := by
    unfold atAccept atSolver NativeSolverImage.finishRooted NativeBindingRoots.endAt NativeBindingRoots.atTail
      NativeBindingRoots.atLoop NativeBindingRoots.atRoots NativeSolverImage.bindingAt NativeSolverImage.shared NativeSolverImage.expandAt
    omega
  have room : atAccept start + 22 ≤ image.size := space
  have ends : (exits start exhausted malformed).inImage image :=
    ⟨by change atAccept start ≤ image.size; omega, by change atAccept start + 11 ≤ image.size; omega,
      by change atAccept start + 11 ≤ image.size; omega, lack, bad⟩
  exact ⟨NativeResolvePrepare.placed_of_emitted image _ _ _ _ (by omega) (by exact lower.trans ends.1) lack bad short prepare,
    NativeSolverImage.rooted_placed_of_emitted image _ _ ends.1 ends short solver,
    NativeResolveTest.return_placed image _ _ _ _ (by omega) target short yes,
    NativeResolveTest.return_placed image _ _ _ _ space target short no⟩

abbrev clobbers : Finset Register := (NativeResolvePrepare.clobbers ∪ NativeSolverStep.clobbers) ∪ returnClobbers 0

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {rootRegion : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def Answer (symbols : UnifierHeaders.Symbols σ) (d : Descriptor) (rootRegion : Region rc)
    (term : NativeTermArena.Layout nc ec) (map : Region mc)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (original : List (Term σ)) (native : Native) : Option (Subst σ) → Prop
  | none => lookup native 0 = some 0
  | some ans =>
    lookup native 0 = some 1 ∧
      ∃ (graph : PackedTerms.Arena) (words : Array Word) (binding : Arena) (history : Words) (logical : Derivation.FiniteUnifier.Trail σ),
        NativeTermArena.Ready term graph native ∧ Held d rootRegion words native ∧ NativeAgendaRecords.Ready trail binding native ∧
        NativeSubstitutionFrame.Ready term map d.solver.substitution graph native ∧ NativeBindingStep.Aux term d.solver agenda trail native ∧
        lookup native 12 = some 0 ∧ lookup native 13 = some 1 ∧
        readWords binding (NativeBindingTrail.root binding) = some history ∧
        PackedWorklist.readTrail symbols graph history = some logical ∧ Derivation.FiniteUnifier.readTrail (Subst.id σ) logical = ans ∧
        PackedRootedMeaning.roots symbols graph words = some (original.map ans.applyTerm)

private theorem merge_frame (a b c : Finset ℕ) :
    (a ∪ (b ∪ c)) ∪ ∅ ⊆ (a ∪ b) ∪ c := by
  rw [Finset.union_empty, Finset.union_assoc]

/-- Emitted from original local and inherited equations.
The resulting vector needs no second graph traversal or
replay when a caller proceeds to the guards. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image start next exhausted malformed) (point : At image before base start) (controls : Controls before)
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
      Answer symbols d rootRegion term map agenda trail original after solution ∧
      executeInstructionWith (SymbolicExecution.profile facts).step state (.transform (.test .resolve level target)) =
        .ok (match solution with
          | none => state.write target 0
          | some answer =>
            let entry := state.levels level
            (state.setLevel level {entry with bindings := {entry.bindings with answer := some answer}}).write target 1) ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let work : PackedWorklist.Worklist := ⟨terms, originalBase ++ newer.reverse, []⟩
  let problem := (state.levels level).bindings.problem facts
  have used := NativeSolverResources.occupied_at_start fuel (stored.size + (newer.length + originalBase.length))
    oldTrail.size (.working work) needed plan
  have sizeFit : stored.size + (newer.length + originalBase.length) ≤ ac := (used.trans available).agenda
  obtain ⟨a, steps, prepBytes, started, prepFrame, prepEffects, installed⟩ :=
    NativeResolvePrepare.fetched other extra vector code.prepare point controls space terms stored oldTrail localRoot baseRoot newer
      originalBase live basePointer localChain baseChain trailEmpty
  rw [if_pos sizeFit] at installed
  obtain ⟨seed, size, history, _, sourceSeed, ⟨atSolve⟩⟩ := installed
  obtain ⟨typed, exactSeed, _, typedRead⟩ := PackedResolution.prepare_packed_exact symbols terms stored localRoot originalBase facts
    (state.levels level).bindings interned baseRead source
  have same : typed = work := PackedWorklist.State.working.inj (Option.some.inj (exactSeed.symm.trans sourceSeed))
  rw [same] at typedRead
  have planned : NativeSolverResources.planned fuel seed.equations.size seed.bindings.size (.working work) = some needed := by
    rw [size, history]
    exact plan
  have fits := NativeSolverResources.fitted symbols fuel seed.equations.size seed.bindings.size (.working work)
    (Derivation.FiniteUnifier.start problem) typedRead wordBudget needed ⟨nc, ec, mc, ac, tc⟩ planned available
  have solverEntry : Arrived term map d.solver agenda trail image base (atSolver start) (exits start exhausted malformed)
      seed.equations.size seed.bindings.size a (.working work) := ⟨seed, rfl, rfl, ⟨atSolve⟩⟩
  have oldValid := PackedRootedMeaning.valid_of_read symbols terms old original readRoots
  have kept := NativeRootedSolverStep.held_after rootSpace retained prepFrame prepEffects
  obtain ⟨b, second, touched, rootBytes, _, _, result, words, _, rooted, terminal, solved, solveFrame, solveEffects,
    rootEffects, preserved, _, resident, _, _, arrived⟩ :=
    NativeRootedSolverRun.fetched other extra vector code.solver space rootSpace symbols fits solverEntry
      (controls.transport prepFrame NativeResolvePrepare.clobbers_data) old kept
      (fun _ seen => Option.some.inj seen ▸ oldValid)
  obtain ⟨_, calculation, interpretation⟩ := PackedRootedMeaning.run_exact symbols original fuel (.working work) result
    old words (Derivation.FiniteUnifier.start problem) typedRead
    (PackedRootedMeaning.entered symbols terms work.pending old original readRoots) wordBudget rooted
  have finish : ∃ after, (X86FuelPrefix.fetches 2).run b = .ok () after ∧
      X86StateFrame.Frame (returnClobbers 0) ∅ b after ∧ Answer symbols d rootRegion term map agenda trail original after (unifyTotal problem) ∧
      Nonempty (At image after base next) := by
    cases result with
    | working _ => cases terminal
    | inconsistent why =>
      have falseResult := Derivation.FiniteUnifier.inconsistent_exact fuel problem why (Option.some.inj calculation).symm
      have point : Nonempty (At image b base (atRefuse start)) := by
        cases why <;> exact arrived
      obtain ⟨atNo⟩ := point
      obtain ⟨after, returned, frame, bit, endpoint⟩ := NativeResolveTest.fetched_return other extra vector atNo 0 0 code.refused
      exact ⟨after, returned, frame, by rw [falseResult]; exact bit, endpoint⟩
    | solved graph history =>
      obtain ⟨record, graphReady, trailReady, trace, staged, aux, zero, one, ⟨atYes⟩⟩ := arrived
      obtain ⟨logical, traceRead, complete⟩ := Option.map_eq_some_iff.mp calculation
      let answer := Derivation.FiniteUnifier.readTrail (Subst.id σ) logical
      have accepted : unifyTotal problem = some answer := Derivation.FiniteUnifier.solved_exact fuel problem logical complete.symm
      obtain ⟨after, returned, frame, bit, endpoint⟩ := NativeResolveTest.fetched_return other extra vector atYes 0 1 code.accepted
      have residents : Held d rootRegion words after :=
        ⟨resident.descriptor.kept frame (by simp) (by simp), resident.words.preserved frame⟩
      refine ⟨after, returned, frame, ?_, endpoint⟩
      rw [accepted]
      exact ⟨bit, graph, words, record, history, logical, graphReady.preserved frame, residents, trailReady.preserved frame,
        staged.preserved frame (by decide), aux.preserved frame, (frame.lookup 12 (by decide)).trans zero,
        (frame.lookup 13 (by decide)).trans one, trace, traceRead, rfl, interpretation graph history logical rfl traceRead⟩
  obtain ⟨after, returned, returnFrame, answer, endpoint⟩ := finish
  have all := ((prepFrame.trans solveFrame).trans returnFrame).mono (Finset.Subset.refl _) (merge_frame prepBytes touched rootBytes)
  have ran := X86FuelPrefix.fetches_then (steps + second) 2 before b after
    (X86FuelPrefix.fetches_then steps second before a b started solved) returned
  exact ⟨after, _, prepBytes ∪ touched, rootBytes, ran, all, .union prepEffects solveEffects, rootEffects,
    (preserved terms rfl).preserved returnFrame, answer, NativeResolveTest.source_test state facts level target, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedResolution
