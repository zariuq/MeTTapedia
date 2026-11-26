import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverResources
import Mettapedia.Machines.TIsa.StoreInstructions.PackedResolution

/-!
# Returning a native resolution TEST from a prepared problem

The solver works on the packed equations at entry. Solved
and inconsistent executions enter the two ordinary return
blocks. A solved result retains the physical trail that
decodes to the principal substitution. Neither a malformed
image nor exhausted workspace is a normal TEST result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveTest

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code Jump jumpDelta)
open NativeSolverStep (Outcome Writes Resident Arrived)
open NativeSolverResources (Budget)
open NativeBindingMemory (Geometry)
open NativeTrailReserve (Descriptor)
open NativeArenaGeometry (Region)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def exits (start exhausted malformed : ℕ) : NativeSolverImage.Exits :=
  ⟨NativeSolverImage.finish start, NativeSolverImage.finish start + 11, NativeSolverImage.finish start + 11, exhausted, malformed⟩

def returnCode (destination : Fin 16) (literal : BitVec 32) (start next : ℕ) : List ℕ :=
  X86Immediate32.code destination literal ++ X86UnconditionalJump.Block.code (jumpDelta (start + 6) next)

theorem return_size (destination : Fin 16) (literal : BitVec 32) (start next : ℕ) :
    (returnCode destination literal start next).length = 11 := rfl

def emit (destination : Fin 16) (start next exhausted malformed : ℕ) : List ℕ :=
  NativeSolverImage.emit start (exits start exhausted malformed) ++
    (returnCode destination 1 (NativeSolverImage.finish start) next ++
      returnCode destination 0 (NativeSolverImage.finish start + 11) next)

theorem extent (destination : Fin 16) (start next exhausted malformed : ℕ) :
    start + (emit destination start next exhausted malformed).length = NativeSolverImage.finish start + 22 := by
  simp only [emit, List.length_append, return_size, ← Nat.add_assoc, NativeSolverImage.emit_size]

structure ReturnPlaced (image : NativeImage.View) (destination : Fin 16) (literal : BitVec 32)
    (start next : ℕ) : Prop where
  room : start + 6 ≤ image.size
  bytes : Code image start (X86Immediate32.code destination literal)
  jump : Jump image (start + 6) next

theorem return_placed (image : NativeImage.View) (dst : Fin 16) (word : BitVec 32) (start next : ℕ)
    (space : start + 11 ≤ image.size) (target : next ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (returnCode dst word start next)) :
    ReturnPlaced image dst word start next := by
  obtain ⟨literal, jump⟩ := NativeWords.code_append (show Code image start
    (X86Immediate32.code dst word ++ _) from installed)
  refine ⟨by omega, literal, ⟨by omega, target, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

structure Placed (image : NativeImage.View) (destination : Fin 16) (start next exhausted malformed : ℕ) : Prop where
  solver : NativeSolverImage.Placed image start (exits start exhausted malformed)
  accepted : ReturnPlaced image destination 1 (NativeSolverImage.finish start) next
  refused : ReturnPlaced image destination 0 (NativeSolverImage.finish start + 11) next

theorem placed_of_emitted (image : NativeImage.View) (dst : Fin 16) (start next exhausted malformed : ℕ)
    (space : NativeSolverImage.finish start + 22 ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit dst start next exhausted malformed)) :
    Placed image dst start next exhausted malformed := by
  obtain ⟨solver, rest⟩ := NativeWords.code_append
    (show Code image start (NativeSolverImage.emit start (exits start exhausted malformed) ++ _) from installed)
  rw [NativeSolverImage.emit_size] at rest
  obtain ⟨yes, no⟩ := NativeWords.code_append rest
  rw [return_size] at no
  exact ⟨NativeSolverImage.placed_of_emitted image _ _ (by omega)
    ⟨by exact Nat.le_trans (Nat.le_add_right _ _) space,
      by change NativeSolverImage.finish start + 11 ≤ image.size; omega,
      by change NativeSolverImage.finish start + 11 ≤ image.size; omega, lack, bad⟩ short solver,
    return_placed image _ _ _ _ (by omega) target short yes, return_placed image _ _ _ _ (by omega) target short no⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
def returnClobbers (destination : Fin 16) : Finset Register := {key destination, .rip}
def clobbers (destination : Fin 16) : Finset Register := NativeSolverStep.clobbers ∪ returnClobbers destination

theorem fetched_return (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next : ℕ} {before : Native}
    (point : At image before base start) (dst : Fin 16) (literal : BitVec 32) (placed : ReturnPlaced image dst literal start next) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame (returnClobbers dst) ∅ before after ∧
      lookup after dst = some (literal.zeroExtend 64) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨a, wrote, written, value, ⟨atJump⟩⟩ := X86PlacedScalar.rex_immediate
    (X86PlacedFrameAddress.nativeBase other) extra vector point placed.room dst literal placed.bytes
  obtain ⟨after, ran, hopped, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector atJump placed.jump
  refine ⟨after, X86FuelPrefix.fetches_then 1 1 before a after wrote ran,
    (X86StateFrame.registerOnly (written.trans hopped)).mono (by simp [returnClobbers, X86Immediate32.writes]) (by simp),
    (hopped.lookup dst ?_).trans value, endpoint⟩
  exact (by decide : ∀ i : Fin 16, key i ∉ ({.rip} : Finset Register)) dst

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}

def Answer (symbols : UnifierHeaders.Symbols σ) (term : NativeTermArena.Layout nc ec) (trail : NativeAgendaRecords.Layout tc)
    (dst : Fin 16) (native : Native) : Option (Subst σ) → Prop
  | none => lookup native dst = some 0
  | some solution => lookup native dst = some 1 ∧
      ∃ (terms : PackedTerms.Arena) (records : PackedEquations.Arena) (history : PackedWorklist.Words)
        (decoded : Derivation.FiniteUnifier.Trail σ),
        NativeTermArena.Ready term terms native ∧ NativeAgendaRecords.Ready trail records native ∧
        PackedEquations.readWords records (NativeBindingTrail.root records) = some history ∧
        PackedWorklist.readTrail symbols terms history = some decoded ∧
        Derivation.FiniteUnifier.readTrail (Subst.id σ) decoded = solution

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem source_test (st : SymbolicExecution.Frame σ) (base : SymbolicExecution.Equations σ) (level : ℕ) (destination : P1Source.Reg)
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    executeInstructionWith (SymbolicExecution.profile base).step st (.transform (.test .resolve level destination)) =
      .ok (match unifyTotal ((st.levels level).bindings.problem base) with
        | none => st.write destination 0
        | some answer =>
          let entry := st.levels level
          (st.setLevel level {entry with bindings := {entry.bindings with answer := some answer}}).write destination 1) := by
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, SymbolicExecution.profile,
    SymbolicExecution.test, SymbolicExecution.resolve_exact]
  cases unifyTotal ((st.levels level).bindings.problem base) <;> rfl

/-- A fitted, prepared resolution runs on the emitted image,
materializes precisely the TEST bit, and has a resident
principal substitution on the successful path. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next exhausted malformed : ℕ} {before : Native}
    (dst : Fin 16) (code : Placed image dst start next exhausted malformed)
    (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image base)
    (symbols : UnifierHeaders.Symbols σ) (work : PackedWorklist.Worklist)
    (seed : Resident term map frame agenda trail work before)
    (problem : Derivation.FiniteUnifier.Equations σ)
    (decoded : PackedWorklist.read symbols (.working work) = some (Derivation.FiniteUnifier.start problem))
    (fuel : ℕ) (wordBudget : PackedWorklist.Reserve fuel work.arena.nodes.size work.arena.children.size)
    (needed : Budget) (plan : NativeSolverResources.planned fuel seed.equations.size seed.bindings.size (.working work) = some needed)
    (available : needed.Within ⟨nc, ec, mc, ac, tc⟩) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers dst) bytes before after ∧ Writes term map frame agenda trail bytes ∧
      Answer symbols term trail dst after (unifyTotal problem) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have fits := NativeSolverResources.fitted symbols fuel seed.equations.size seed.bindings.size _ _ decoded wordBudget
    needed ⟨nc, ec, mc, ac, tc⟩ plan available
  have input : Arrived term map frame agenda trail image base start (exits start exhausted malformed)
      seed.equations.size seed.bindings.size before (.working work) := ⟨seed, rfl, rfl, ⟨point⟩⟩
  obtain ⟨mid, count, bytes, a, t, result, pureRun, terminal, fetchedRun, framed, effects, _, _, arrived⟩ :=
    NativeSolverRun.fetched other extra vector code.solver space symbols fits input controls
  obtain ⟨observed, simulated, interpreted⟩ := PackedWorklist.run_exact symbols fuel (.working work) _ decoded wordBudget
  obtain rfl := Option.some.inj (simulated.symm.trans pureRun)
  have exactMeaning := Derivation.FiniteUnifier.start_exact fuel problem
  cases observed with
  | working work => cases terminal
  | inconsistent why =>
    have answer : (none : Option (Subst σ)) = unifyTotal problem := by
      rw [← Option.some.inj interpreted] at exactMeaning
      exact exactMeaning
    obtain ⟨atNo⟩ := arrived
    have refuse : At image mid base (NativeSolverImage.finish start + 11) := by cases why <;> exact atNo
    obtain ⟨after, ran, returned, bit, endpoint⟩ := fetched_return other extra vector refuse dst 0 code.refused
    refine ⟨after, count + 2, bytes, X86FuelPrefix.fetches_then count 2 before mid after fetchedRun ran,
      (framed.trans returned).mono (Finset.Subset.refl _) (by simp), effects, ?_, endpoint⟩
    rw [← answer]
    exact bit
  | solved terms history =>
    obtain ⟨packed, nativeTerms, nativeTrail, readback, _, _, _, _, ⟨atYes⟩⟩ := arrived
    obtain ⟨abstractTrail, decodedTrail, solved⟩ := Option.map_eq_some_iff.mp interpreted
    have answer : some (Derivation.FiniteUnifier.readTrail (Subst.id σ) abstractTrail) = unifyTotal problem := by
      rw [← solved] at exactMeaning
      exact exactMeaning
    obtain ⟨after, ran, returned, bit, endpoint⟩ := fetched_return other extra vector atYes dst 1 code.accepted
    refine ⟨after, count + 2, bytes, X86FuelPrefix.fetches_then count 2 before mid after fetchedRun ran,
      (framed.trans returned).mono (Finset.Subset.refl _) (by simp), effects, ?_, endpoint⟩
    rw [← answer]
    exact ⟨bit, terms, packed, history, abstractTrail, nativeTerms.preserved returned, nativeTrail.preserved returned, readback, decodedTrail, rfl⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveTest
