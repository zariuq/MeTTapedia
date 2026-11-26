import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverStep

/-!
# Complete native runs of the finite unifier

The proof follows the packed reference run, charging newly
allocated records rather than the number of distinct equations.
Its resource analysis is independent of the fetched x86 run.
A packed terminal state has no further native solver step.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverRun

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedMemory (Controls)
open NativeArenaGeometry (Region)
open NativeTrailReserve (Descriptor)
open NativeBindingMemory (Geometry)
open NativeSolverImage (Exits Placed)
open NativeSolverStep (Outcome Room Resident Arrived Writes arenaOf agendaDemand trailDemand mapDemand clobbers clobbers_data handlers)
open PackedWorklist (Worklist Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u p
variable {σ : LPSignature.{u,u,p,u}}

inductive Fits (symbols : UnifierHeaders.Symbols σ) (nc ec mc ac tc : ℕ) : ℕ → ℕ → ℕ → Outcome → Prop
  | terminal {fuel a t : ℕ} {state : Outcome} :
      PackedWorklist.terminal state = true → Fits symbols nc ec mc ac tc fuel a t state
  | empty {fuel a t : ℕ} {terms : PackedTerms.Arena} {history : Words} :
      Fits symbols nc ec mc ac tc (fuel + 1) a t (.working ⟨terms, [], history⟩)
  | step {fuel a t : ℕ} {terms : PackedTerms.Arena} {left right : Word} {pending history : Words}
      {lTerm rTerm : Term σ} {action : PackedUnifierAction.Encoded} {next : Outcome} :
      PackedTerms.lookup symbols terms left = some lTerm → PackedTerms.lookup symbols terms right = some rTerm →
      PackedUnifierAction.inspect terms left right = some action →
      PackedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ = some next →
      Room nc ec mc ac tc terms a t pending action next →
      Fits symbols nc ec mc ac tc fuel (a + agendaDemand pending action) (t + trailDemand action) next →
      Fits symbols nc ec mc ac tc (fuel + 1) a t (.working ⟨terms, (left, right) :: pending, history⟩)

theorem terminal_run (fuel : ℕ) (state : Outcome) (terminal : PackedWorklist.terminal state = true) :
    PackedWorklist.run fuel state = some state := by
  have once : PackedWorklist.step state = some state := by cases state <;> simp_all [PackedWorklist.terminal, PackedWorklist.step]
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [PackedWorklist.run, once, Option.bind_some] using ih

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {exits : Exits}

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem arrived_terms {a t : ℕ} {native : Native} {state : Outcome}
    (input : Arrived term map frame agenda trail image base start exits a t native state)
    (source : PackedTerms.Arena) (graph : arenaOf state = some source) :
    NativeTermArena.Ready term source native := by
  cases state with
  | working work =>
    obtain rfl := Option.some.inj graph
    obtain ⟨resident, _, _, _⟩ := input
    exact resident.live.dispatch.termReady
  | solved terms history =>
    obtain rfl := Option.some.inj graph
    obtain ⟨_, ready, _, _, _⟩ := input
    exact ready
  | inconsistent why => cases graph

/-- All the recursive edges in a fitted packed run execute on
the one installed solver image, ending at its proper terminal
continuation. The fetched length counts the actual instructions. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (code : Placed image start exits) (space : Geometry term map frame agenda trail image base)
    (symbols : UnifierHeaders.Symbols σ) {fuel a t : ℕ} {state : Outcome}
    (fit : Fits symbols nc ec mc ac tc fuel a t state)
    {before : Native} (input : Arrived term map frame agenda trail image base start exits a t before state)
    (controls : Controls before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes a' t' result, PackedWorklist.run fuel state = some result ∧ PackedWorklist.terminal result = true ∧
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧ Writes term map frame agenda trail bytes ∧
      (∀ source, arenaOf state = some source → NativeTermArena.Ready term source after) ∧
      lookup after 13 = lookup before 13 ∧
      Arrived term map frame agenda trail image base start exits a' t' after result := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction fit generalizing before with
  | @terminal fuel a t state terminal =>
    exact ⟨before, 0, ∅, a, t, state, terminal_run fuel state terminal, terminal, X86FuelPrefix.fetches_zero before,
      X86StateFrame.Frame.refl _ _ _, .idle, arrived_terms input, rfl, input⟩
  | @empty fuel a t terms history =>
    obtain ⟨resident, used, bound, ⟨point⟩⟩ := input
    obtain ⟨after, ran, footprint, one, terminal⟩ :=
      NativeSolverStep.fetched_empty other extra vector code.toCorePlaced point controls terms history resident
    have reference : PackedWorklist.run (fuel + 1) (.working ⟨terms, [], history⟩) = some (.solved terms history) := by
      exact terminal_run fuel (.solved terms history) rfl
    exact ⟨after, 2, ∅, resident.equations.size, resident.bindings.size, _, reference, rfl, ran, footprint, .idle,
      fun source graph => arrived_terms terminal source graph, one, terminal⟩
  | @step fuel a t terms left right pending history lTerm rTerm action next lRead rRead looked advanced room further ih =>
    obtain ⟨resident, aSize, tSize, ⟨point⟩⟩ := input
    have localRoom : Room nc ec mc ac tc terms resident.equations.size resident.bindings.size pending action next := by
      rwa [aSize, tSize]
    obtain ⟨middle, first, changed, taken, framed, localWrites, stillThere, extendsGraph, one, following⟩ :=
      NativeSolverStep.fetched_nonempty other extra vector code point controls space terms left right pending history
        resident symbols lTerm rTerm lRead rRead action looked next advanced localRoom
    have received : Arrived term map frame agenda trail image base start exits (a + agendaDemand pending action)
        (t + trailDemand action) middle next := by rwa [aSize, tSize] at following
    by_cases stops : PackedWorklist.terminal next = true
    · have reference : PackedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) = some next :=
        by simp only [PackedWorklist.run, PackedWorklist.step, advanced, Option.bind_some, terminal_run fuel next stops]
      exact ⟨middle, first, changed, _, _, next, reference, stops, taken, framed, localWrites,
        fun _ stored => Option.some.inj stored ▸ stillThere, one.trans resident.live.dispatch.one.symm, received⟩
    · obtain ⟨laterWork, rfl⟩ : ∃ w, next = .working w := by
        cases next with
        | working w => exact ⟨w, rfl⟩
        | solved _ _ => exact (stops rfl).elim
        | inconsistent _ => exact (stops rfl).elim
      obtain ⟨after, second, more, finalAgenda, finalTrail, result, rest, terminal, ran, lastFrame, tailWrites, retained, lastOne, final⟩ :=
        ih received (controls.transport framed clobbers_data)
      have reference : PackedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) = some result :=
        by simp only [PackedWorklist.run, PackedWorklist.step, advanced, Option.bind_some, rest]
      have oldest := NativeRemapSnapshot.ready_restrict (extendsGraph laterWork.arena rfl) (retained laterWork.arena rfl)
      exact ⟨after, first + second, changed ∪ more, finalAgenda, finalTrail, result, reference, terminal,
        X86FuelPrefix.fetches_then first second before middle after taken ran,
        (framed.trans lastFrame).mono (by simp) (Finset.Subset.refl _), .union localWrites tailWrites,
        fun _ stored => Option.some.inj stored ▸ oldest, lastOne.trans (one.trans resident.live.dispatch.one.symm), final⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverRun
