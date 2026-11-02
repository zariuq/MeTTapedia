import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationFunction
import Mettapedia.Machines.BranchLocalNeed.OrderedPaths
import Mettapedia.Machines.BranchLocalNeed.SharedContinuationInstance

/-!
# Scoped natural evaluation in recorded execution representations

The source is the existing sharing-aware natural semantics. The compact Need
executor and shared-continuation program are independently implemented owners.
Exact recorded worlds retain the heap, captured origins, identities, branch
paths and receipt graph; work and the execution bound are existential.

One natural derivation supplies one completed branch of the breadth-first
executor. It does not imply that a depth-first schedule visits that branch or
finishes its siblings. Every answer in a recorded shared prefix nevertheless
has its own independent natural derivation. Receipt effects here are not an
irreversible external world, and captured native-domain functions are not a
first-class computation-lambda grammar.
-/

open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedRecordedExecution

open NeedReference ScopedNeedMachine ScopedNeedNaturalSemantics

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat}

def initial (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    NeedMachine Head Operation Effect StableFault NativeFault m :=
  ⟨world, .run (.evaluate origin .done) [], {}⟩

def recordedFrontier
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat) (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :=
  NeedExecution.runFrontier (spec primitive) fuel [NeedExecution.projectMachine true (initial origin world)]

theorem recorded_frontier_exact
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat) (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    (recordedFrontier primitive fuel origin world).mapM NeedExecution.CoreMachine.readback? =
      some (NeedReference.runFrontier (spec primitive) fuel [initial origin world]) := by
  simpa only [recordedFrontier, List.map_singleton] using
    NeedExecution.recording_runFrontier_readback (spec primitive) fuel [initial origin world]

/-- Exact-world preservation and no invention for completed branches of the
recorded compact executor. No all-branches-termination premise is hidden here. -/
theorem eval_iff_recorded_completion
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} :
    Nonempty (Eval primitive origin world outcome final) ↔
      ∃ fuel work, NeedExecution.projectMachine true
        (⟨final, .halted outcome, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)
          ∈ recordedFrontier primitive fuel origin world := by
  constructor
  · rintro ⟨evaluation⟩
    obtain ⟨length, work, path⟩ := evaluation.halts {}
    refine ⟨length, work, ?_⟩
    rw [recordedFrontier, ← List.map_singleton, ← NeedExecution.project_runFrontier_commutes]
    exact List.mem_map.mpr ⟨_, OrderedPaths.path_mem_frontier (spec primitive) path
      (by simp [initial]), rfl⟩
  · rintro ⟨fuel, work, member⟩
    rw [recordedFrontier, ← List.map_singleton, ← NeedExecution.project_runFrontier_commutes] at member
    obtain ⟨machine, present, equal⟩ := List.mem_map.mp member
    have same := congrArg NeedExecution.CoreMachine.readback? equal
    simp only [NeedExecution.readback_projectMachine, Option.some.injEq] at same
    subst machine
    obtain ⟨first, firstMember, length, _, path⟩ := runFrontier_reachable primitive present
    cases List.mem_singleton.mp firstMember
    exact Reflection.eval_of_steps path

abbrev SharedState (Head Operation Effect StableFault NativeFault : Type) (m : Nat) :=
  NeedContinuation.NeedState (Closure Head Operation Effect m)
    (Local Head Operation Effect StableFault NativeFault m) (Resume Head Operation Effect m)
    ScopedNeedMachine.Rule (Tm Head m) StableFault (Fault NativeFault) Effect

def sharedInitial (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    SharedState Head Operation Effect StableFault NativeFault m :=
  ⟨[⟨⟨NeedExecution.projectWorld true world, {}⟩, .run (.evaluate origin .done), []⟩], []⟩

def sharedReadback
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (steps : Nat) (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :=
  (NeedContinuation.machines
    ((Mettapedia.Machines.SharedContinuation.step (NeedContinuation.program (spec primitive)))^[steps]
      (sharedInitial origin world))).mapM NeedExecution.CoreMachine.readback?

theorem shared_readback_prefix
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (steps : Nat) (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    ∃ count ≤ steps, sharedReadback primitive steps origin world =
      some (((NeedRepresentation.needSystem (spec primitive)).expandFirst)^[count]
        [initial origin world]) := by
  obtain ⟨count, bounded, _, readback⟩ :=
    NeedContinuation.recorded_prefix_of_program (spec primitive) steps (sharedInitial origin world)
      (NeedContinuation.settled_single _ rfl) [initial origin world] rfl
  exact ⟨count, bounded, readback⟩

/-- Even before the entire depth-first frontier finishes, an actually
completed branch has the exact natural source outcome and world. -/
theorem shared_prefix_no_invention
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {steps : Nat} {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} {work : Work}
    {frontier : List (NeedMachine Head Operation Effect StableFault NativeFault m)}
    (readback : sharedReadback primitive steps origin world = some frontier)
    (completed : ⟨final, .halted outcome, work⟩ ∈ frontier) :
    Nonempty (Eval primitive origin world outcome final) := by
  obtain ⟨count, _, exactPrefix⟩ := shared_readback_prefix primitive steps origin world
  have same := Option.some.inj (readback.symm.trans exactPrefix)
  rw [same] at completed
  obtain ⟨length, _, path⟩ := OrderedPaths.depthFirst_reachable (spec primitive) count
    (initial origin world) _ completed
  exact Reflection.eval_of_steps path

/-- A completed reference frontier supplies the missing global termination
condition for depth-first realization. This is an explicit operational
condition on all alternatives, not a consequence of one natural derivation. -/
theorem shared_of_complete_reference
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (fuel : Nat) (origin : Closure Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (complete : (NeedReference.runFrontier (spec primitive) fuel
      [initial origin world]).all NeedReference.isHalted = true) :
    ∃ steps,
      ((Mettapedia.Machines.SharedContinuation.step (NeedContinuation.program (spec primitive)))^[steps]
        (sharedInitial origin world)).frontier = [] ∧
      sharedReadback primitive steps origin world =
        some (NeedReference.runFrontier (spec primitive) fuel [initial origin world]) := by
  have coreComplete : (NeedExecution.runFrontier (spec primitive) fuel
      (NeedContinuation.machines (sharedInitial origin world))).all NeedExecution.isHalted = true := by
    change (NeedExecution.runFrontier (spec primitive) fuel
      ([initial origin world].map (NeedExecution.projectMachine true))).all
        NeedExecution.isHalted = true
    rw [← NeedExecution.project_runFrontier_commutes]
    simpa only [List.all_map, Function.comp_def, NeedExecution.isHalted_project] using complete
  obtain ⟨steps, done, exactFrontier⟩ := NeedContinuation.program_of_runFrontier
    (spec primitive) fuel (sharedInitial origin world)
    (NeedContinuation.settled_single _ rfl) coreComplete
  refine ⟨steps, done, ?_⟩
  unfold sharedReadback
  rw [exactFrontier]
  exact recorded_frontier_exact primitive fuel origin world

/-- Native-domain captured application uses the same source opening and the
same exact-world representation theorem. It does not turn the function body
interface into a new first-class runtime value representation. -/
theorem captured_application_iff
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (function : ScopedNeedComputationFunction.Function Head Operation Effect n k)
    (values : Sub Head n m) (needs : Fin k → CellId) (argument : Tm Head m)
    (world final : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head StableFault NativeFault m) :
    Nonempty (Eval primitive (function.open values needs argument) world outcome final) ↔
      ∃ fuel work, NeedExecution.projectMachine true
        (⟨final, .halted outcome, work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)
          ∈ recordedFrontier primitive fuel (function.open values needs argument) world :=
  eval_iff_recorded_completion

end ScopedNeedRecordedExecution
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
