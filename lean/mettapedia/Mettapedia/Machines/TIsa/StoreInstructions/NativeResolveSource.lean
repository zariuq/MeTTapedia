import Mettapedia.Machines.TIsa.StoreInstructions.NativeResolvePrepare

/-!
# The emitted resolution TEST on the original equation chains

Both preparation and the solver execute in the same image.
The corresponding source instruction runs from the original
abstract knowledge, not from a manually prepared solver
state. Capacity bounds are taken from the reference run's
resource plan and refer to real initialized backing arenas.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveSource

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeBindingMemory (Geometry)
open NativeBindingStep (Live)
open NativeSolverStep (Writes)
open NativeSolverResources (Budget)
open NativeTrailReserve (Descriptor)
open NativeArenaGeometry (Region)
open NativeResolveTest (Answer)
open PackedEquations (Arena readWords)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (destination : Fin 16) (start next exhausted malformed : ℕ) : List ℕ :=
  NativeResolvePrepare.emit start (start + 505) exhausted malformed ++
    NativeResolveTest.emit destination (start + 505) next exhausted malformed

theorem extent (destination : Fin 16) (start next exhausted malformed : ℕ) :
    start + (emit destination start next exhausted malformed).length = NativeSolverImage.finish (start + 505) + 22 := by
  simp only [emit, List.length_append, NativeResolvePrepare.emit_size, ← Nat.add_assoc, NativeResolveTest.extent]

structure Placed (image : NativeImage.View) (destination : Fin 16) (start next exhausted malformed : ℕ) : Prop where
  prepare : NativeResolvePrepare.Placed image start (start + 505) exhausted malformed
  test : NativeResolveTest.Placed image destination (start + 505) next exhausted malformed

theorem placed_of_emitted (image : NativeImage.View) (destination : Fin 16) (start next exhausted malformed : ℕ)
    (space : NativeSolverImage.finish (start + 505) + 22 ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit destination start next exhausted malformed)) :
    Placed image destination start next exhausted malformed := by
  obtain ⟨prepare, test⟩ := NativeWords.code_append (show Code image start
    (NativeResolvePrepare.emit start (start + 505) exhausted malformed ++ _) from code)
  rw [NativeResolvePrepare.emit_size] at test
  have bound := space
  unfold NativeSolverImage.finish NativeSolverImage.bindingAt NativeSolverImage.shared NativeSolverImage.expandAt at bound
  exact ⟨NativeResolvePrepare.placed_of_emitted image _ _ _ _ (by omega) (by omega) lack bad short prepare,
    NativeResolveTest.placed_of_emitted image _ _ _ _ _ space target lack bad short test⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
def clobbers (destination : Fin 16) : Finset Register := NativeResolvePrepare.clobbers ∪ NativeResolveTest.clobbers destination

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}

/-- The original encoded local and base knowledge have a
complete native TEST execution when its plan fits. The usual
p1 boolean and the readable principal trail agree with the
same source resolution instruction. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start next exhausted malformed : ℕ} {before : Native}
    (dst : Fin 16) (code : Placed image dst start next exhausted malformed)
    (point : At image before codeBase start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image codeBase)
    (symbols : UnifierHeaders.Symbols σ) (terms : PackedTerms.Arena) (stored oldTrail : Arena)
    (localRoot baseRoot : Word) (newer originalBase : Words)
    (live : Live term map frame agenda trail terms stored localRoot oldTrail before)
    (basePointer : lookup before 7 = some baseRoot)
    (localChain : readWords stored localRoot = some newer) (baseChain : readWords stored baseRoot = some originalBase.reverse)
    (trailEmpty : readWords oldTrail (NativeBindingTrail.root oldTrail) = some [])
    (facts : SymbolicExecution.Equations σ) (state : SymbolicExecution.Frame σ) (level : ℕ) (target : P1Source.Reg)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (baseRead : PackedWorklist.readEquations symbols terms originalBase = some facts)
    (held : PackedEquations.read (PackedTerms.codebook decoded) stored localRoot = some (state.levels level).bindings.newer)
    (fuel : ℕ) (wordBudget : PackedWorklist.Reserve fuel terms.nodes.size terms.children.size)
    (needed : Budget)
    (plan : NativeSolverResources.planned fuel (stored.size + (newer.length + originalBase.length)) oldTrail.size
      (.working ⟨terms, originalBase ++ newer.reverse, []⟩) = some needed)
    (available : needed.Within ⟨nc, ec, mc, ac, tc⟩) :
    let solution := unifyTotal ((state.levels level).bindings.problem facts)
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers dst) bytes before after ∧ Writes term map frame agenda trail bytes ∧
      Answer symbols term trail dst after solution ∧
      executeInstructionWith (SymbolicExecution.profile facts).step state (.transform (.test .resolve level target)) =
        .ok (match solution with
          | none => state.write target 0
          | some answer =>
            let entry := state.levels level
            (state.setLevel level {entry with bindings := {entry.bindings with answer := some answer}}).write target 1) ∧
      Nonempty (At image after codeBase next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let work : PackedWorklist.Worklist := ⟨terms, originalBase ++ newer.reverse, []⟩
  have used := NativeSolverResources.occupied_at_start fuel (stored.size + (newer.length + originalBase.length))
    oldTrail.size (.working work) needed plan
  have fits : stored.size + (newer.length + originalBase.length) ≤ ac := (used.trans available).agenda
  obtain ⟨mid, first, prepBytes, started, prepFrame, prepared, installed⟩ :=
    NativeResolvePrepare.fetched other extra vector code.prepare point controls space terms stored oldTrail localRoot baseRoot newer
      originalBase live basePointer localChain baseChain trailEmpty
  rw [if_pos fits] at installed
  obtain ⟨seed, size, history, _, sourceSeed, ⟨atTest⟩⟩ := installed
  obtain ⟨typed, exactSeed, _, typedRead⟩ := PackedResolution.prepare_packed_exact symbols terms stored localRoot originalBase facts
    (state.levels level).bindings interned baseRead held
  have same : typed = work := PackedWorklist.State.working.inj (Option.some.inj (exactSeed.symm.trans sourceSeed))
  rw [same] at typedRead
  have planned : NativeSolverResources.planned fuel seed.equations.size seed.bindings.size (.working work) = some needed := by
    rw [size, history]
    exact plan
  obtain ⟨after, second, testBytes, ran, testFrame, writes, answer, endpoint⟩ :=
    NativeResolveTest.fetched other extra vector dst code.test atTest (controls.transport prepFrame NativeResolvePrepare.clobbers_data)
      space symbols work seed _ typedRead fuel wordBudget needed planned available
  exact ⟨after, first + second, prepBytes ∪ testBytes, X86FuelPrefix.fetches_then first second before mid after started ran,
    prepFrame.trans testFrame, .union prepared writes, answer,
    NativeResolveTest.source_test state facts level target, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveSource
