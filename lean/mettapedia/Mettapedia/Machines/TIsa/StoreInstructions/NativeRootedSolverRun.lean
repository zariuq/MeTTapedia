import Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverStep
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverRun

/-!
# Complete runs with retained roots

Rooted and ordinary execution have the same finite-unifier
outcome and traversal of the equations. Only the rooted
execution returns the current coordinates of the caller's
private values. An inconsistent run has no normalized
output world.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverRun

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedMemory (Controls)
open NativeArenaGeometry (Region)
open NativeLiveRootEntry (Descriptor Held)
open NativeSolverImage (Exits RootedPlaced)
open NativeSolverRun (Fits arrived_terms)
open NativeSolverStep (Outcome Room Arrived Writes arenaOf agendaDemand trailDemand clobbers clobbers_data handlers)
open NativeBindingRootMemory (Geometry Covered)
open NativeRootedSolverStep (ValidAt)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {roots : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {exits : Exits}

private theorem regroup (firstRoots firstScratch nextRoots nextScratch : Finset ℕ) :
    (firstScratch ∪ firstRoots) ∪ (nextScratch ∪ nextRoots) =
      (firstScratch ∪ nextScratch) ∪ (firstRoots ∪ nextRoots) := by
  ext byte
  simp only [Finset.mem_union]
  tauto

private theorem keep_idle {before after : Native} {regs : Finset Register} {words : Array Word}
    (held : Held d roots words before) (framed : X86StateFrame.Frame regs ∅ before after) :
    Held d roots words after :=
  ⟨held.descriptor.kept framed (by simp) (by simp), held.words.preserved framed⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- A fitted run actually executes all selected x86
instructions and produces the exact packed root vector. The
capacity and logical decisions are those of the same solver. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (code : RootedPlaced image start exits) (space : NativeBindingMemory.Geometry term map d.solver agenda trail image base)
    (rootSpace : Geometry roots d term map agenda trail image base)
    (symbols : UnifierHeaders.Symbols σ) {fuel a t : ℕ} {state : Outcome}
    (fit : Fits symbols nc ec mc ac tc fuel a t state)
    {before : Native} (input : Arrived term map d.solver agenda trail image base start exits a t before state)
    (controls : Controls before) (old : Array Word) (held : Held d roots old before) (valid : ValidAt state old) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps scratch rootWrites a' t' result new,
      PackedWorklist.run fuel state = some result ∧ PackedRootedWorklist.run fuel state old = some (result, new) ∧
      PackedWorklist.terminal result = true ∧ (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (scratch ∪ rootWrites) before after ∧ Writes term map d.solver agenda trail scratch ∧
      Covered roots rootWrites ∧ (∀ source, arenaOf state = some source → NativeTermArena.Ready term source after) ∧
      lookup after 13 = lookup before 13 ∧
      Held d roots new after ∧ ValidAt result new ∧ new.size = old.size ∧
      Arrived term map d.solver agenda trail image base start exits a' t' after result := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction fit generalizing before old with
  | @terminal fuel a t state terminal =>
    exact ⟨before, 0, ∅, ∅, a, t, state, old, NativeSolverRun.terminal_run fuel state terminal,
      PackedRootedWorklist.terminal_run fuel state old terminal, terminal, X86FuelPrefix.fetches_zero before,
      X86StateFrame.Frame.refl _ _ _, .idle, Covered.empty _, arrived_terms input, rfl, held, valid, rfl, input⟩
  | @empty fuel a t terms history =>
    obtain ⟨resident, _, _, ⟨point⟩⟩ := input
    obtain ⟨after, ran, framed, one, terminal⟩ :=
      NativeSolverStep.fetched_empty other extra vector code.toCorePlaced point controls terms history resident
    have reference : PackedWorklist.run (fuel + 1) (.working ⟨terms, [], history⟩) = some (.solved terms history) :=
      NativeSolverRun.terminal_run fuel (.solved terms history) rfl
    have rooted : PackedRootedWorklist.run (fuel + 1) (.working ⟨terms, [], history⟩) old = some (.solved terms history, old) :=
      PackedRootedWorklist.terminal_run fuel (.solved terms history) old rfl
    exact ⟨after, 2, ∅, ∅, _, _, _, old, reference, rooted, rfl, ran, framed.mono (Finset.Subset.refl _) (Finset.empty_subset _),
      .idle, Covered.empty _, fun src graph => arrived_terms terminal src graph, one, keep_idle held framed,
      valid, rfl, terminal⟩
  | @step fuel a t terms left right pending history lTerm rTerm action next lRead rRead looked advanced room further ih =>
    obtain ⟨resident, aSize, tSize, ⟨point⟩⟩ := input
    have localRoom : Room nc ec mc ac tc terms resident.equations.size resident.bindings.size pending action next := by
      rwa [aSize, tSize]
    obtain ⟨middle, first, scratch, changes, moved, rooted, ran, framed, workWrites, rootWrites, preserved,
      extendsGraph, one, carried, movedValid, movedSize, arrives⟩ :=
      NativeRootedSolverStep.fetched other extra vector code point controls space rootSpace terms left right pending history
        resident symbols lTerm rTerm lRead rRead action looked next advanced localRoom old held (valid terms rfl)
    have received : Arrived term map d.solver agenda trail image base start exits (a + agendaDemand pending action)
        (t + trailDemand action) middle next := by rwa [aSize, tSize] at arrives
    by_cases stop : PackedWorklist.terminal next = true
    · have ref : PackedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) = some next := by
        simp only [PackedWorklist.run, PackedWorklist.step, advanced, Option.bind_some, NativeSolverRun.terminal_run fuel next stop]
      have rootsRef : PackedRootedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) old =
          some (next, moved) := by
        simp only [PackedRootedWorklist.run, PackedRootedWorklist.step, rooted, Option.bind_some,
          PackedRootedWorklist.terminal_run fuel next moved stop]
      exact ⟨middle, first, scratch, changes, _, _, next, moved, ref, rootsRef, stop, ran, framed, workWrites, rootWrites,
        fun _ seen => Option.some.inj seen ▸ preserved, one.trans resident.live.dispatch.one.symm, carried, movedValid, movedSize, received⟩
    · obtain ⟨later, rfl⟩ : ∃ work, next = .working work := by
        cases next with
        | working work => exact ⟨work, rfl⟩
        | solved _ _ => exact (stop rfl).elim
        | inconsistent _ => exact (stop rfl).elim
      obtain ⟨after, second, scratch', changes', a', t', result, new, rest, restRoot, terminal, fetched, finalFrame, work, writes,
        older, finalOne, ready, finalValid, finalSize, done⟩ :=
        ih received (controls.transport framed clobbers_data) moved carried movedValid
      have ref : PackedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) = some result := by
        simp only [PackedWorklist.run, PackedWorklist.step, advanced, Option.bind_some, rest]
      have rootsRef : PackedRootedWorklist.run (fuel + 1) (.working ⟨terms, (left, right) :: pending, history⟩) old =
          some (result, new) := by
        simp only [PackedRootedWorklist.run, PackedRootedWorklist.step, rooted, Option.bind_some, restRoot]
      have earlier := NativeRemapSnapshot.ready_restrict (extendsGraph later.arena rfl) (older later.arena rfl)
      have whole : X86StateFrame.Frame clobbers ((scratch ∪ scratch') ∪ (changes ∪ changes')) before after := by
        have fixed := (framed.trans finalFrame).mono
          (Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _)) (Finset.Subset.refl _)
        rw [regroup] at fixed
        exact fixed
      exact ⟨after, first + second, scratch ∪ scratch', changes ∪ changes', a', t', result, new, ref, rootsRef,
        terminal, X86FuelPrefix.fetches_then first second before middle after ran fetched, whole,
        .union workWrites work, rootWrites.union writes, fun _ seen => Option.some.inj seen ▸ earlier,
        finalOne.trans (one.trans resident.live.dispatch.one.symm), ready, finalValid, finalSize.trans movedSize, done⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverRun
