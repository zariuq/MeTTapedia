import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverStep
import Mettapedia.Machines.TIsa.StoreInstructions.PackedRootedWorklist

/-!
# The rooted native solver's transition

The ordinary dispatch has no root work. Only an actual
elimination transports the vector, before its completed
map can be overwritten by the next equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverStep

open Mettapedia.Logic.LP
open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open NativeArenaGeometry (Region)
open NativeLiveRootEntry (Descriptor Held)
open NativeSolverImage (Exits RootedPlaced targets bind_target)
open NativeSolverStep (Outcome Extends Room Resident Arrived Writes agendaDemand trailDemand handlers clobbers)
open NativeBindingRootMemory (Geometry Covered External descriptor_lengths root_lengths)
open PackedRootedWorklist (Valid)
open PackedWorklist (Words)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {d : Descriptor} {roots : Region rc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {exits : Exits}

def ValidAt (state : Outcome) (words : Array Word) : Prop :=
  ∀ terms, NativeSolverStep.arenaOf state = some terms → Valid terms words

/-- The private vector becomes irrelevant to the result on
refutation; even then the proof records exactly what remains
physically in its initialized slots. -/
theorem keep_writes {n : ℕ} {held : Region n} (space : External held term map agenda trail)
    {seen : Finset ℕ} (read : Covered held seen)
    (lengths : Disjoint seen (NativeSubstitutionFrame.mutableBytes d.solver.substitution))
    {bytes : Finset ℕ} (effect : Writes term map d.solver agenda trail bytes) : Disjoint seen bytes := by
  induction effect with
  | idle => simp
  | graph region => exact space.kept_graph read lengths region
  | pending region => exact Covered.separate space.agenda read (Covered.agendaWrites region)
  | binding region => exact Covered.separate space.trail read (Covered.agendaWrites region)
  | header => exact Covered.separate space.agenda read (Covered.header agenda)
  | trailHeader => exact Covered.separate space.trail read (Covered.header trail)
  | headers =>
    exact Finset.disjoint_union_right.mpr ⟨Covered.separate space.trail read (Covered.header trail),
      Covered.separate space.agenda read (Covered.header agenda)⟩
  | union _ _ first later => exact Finset.disjoint_union_right.mpr ⟨first, later⟩

theorem held_after (space : Geometry roots d term map agenda trail image base) {bytes : Finset ℕ}
    {before after : Native} {regs : Finset Register} {words : Array Word}
    (retained : Held d roots words before) (run : X86StateFrame.Frame regs bytes before after)
    (effect : Writes term map d.solver agenda trail bytes) : Held d roots words after :=
  ⟨retained.descriptor.kept run
    (keep_writes space.descriptor (Covered.field d 16) (descriptor_lengths d 16 (by decide) (by decide)) effect)
    (keep_writes space.descriptor (Covered.field d 17) (descriptor_lengths d 17 (by decide) (by decide)) effect),
    retained.words.kept run (fun i => keep_writes space.rootSpace (Covered.word roots i) (root_lengths d space.rootFrame i) effect)⟩

private theorem regroup (graph held trace pending headers : Finset ℕ) :
    (graph ∪ held) ∪ (trace ∪ pending ∪ headers) = (graph ∪ trace ∪ pending ∪ headers) ∪ held := by
  ext byte
  simp only [Finset.mem_union]
  tauto

private theorem binding_clobbers : NativeBindingRoots.clobbers ⊆ clobbers := by decide

private theorem bind_target_case {terms : PackedTerms.Arena} {left right name value : Word}
    (looked : PackedUnifierAction.inspect terms left right = some (.bindVar name value)) :
    ∃ side : NativeBindEntry.Side, NativeTermDispatch.choose terms left right = side.exiting :=
  NativeSolverStep.route terms left right (.bindVar name value) looked

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} (code : RootedPlaced image start exits) (point : At image before base start) (controls : Controls before)
    (space : NativeBindingMemory.Geometry term map d.solver agenda trail image base)
    (rootSpace : Geometry roots d term map agenda trail image base)
    (terms : PackedTerms.Arena) (left right : Word) (pending history : Words)
    (resident : Resident term map d.solver agenda trail ⟨terms, (left, right) :: pending, history⟩ before)
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols terms left = some lTerm) (rightRead : PackedTerms.lookup symbols terms right = some rTerm)
    (action : PackedUnifierAction.Encoded) (looked : PackedUnifierAction.inspect terms left right = some action) (result : Outcome)
    (advanced : PackedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ = some result)
    (bounds : Room nc ec mc ac tc terms resident.equations.size resident.bindings.size pending action result)
    (old : Array Word) (held : Held d roots old before) (valid : Valid terms old) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps scratch rootWrites new, PackedRootedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ old = some (result, new) ∧
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (scratch ∪ rootWrites) before after ∧ Writes term map d.solver agenda trail scratch ∧
      Covered roots rootWrites ∧
      NativeTermArena.Ready term terms after ∧ Extends terms result ∧ lookup after 13 = some 1 ∧
      Held d roots new after ∧ ValidAt result new ∧ new.size = old.size ∧
      Arrived term map d.solver agenda trail image base start exits (resident.equations.size + agendaDemand pending action)
        (resident.bindings.size + trailDemand action) after result := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases binding : ∃ name value, action = .bindVar name value
  · obtain ⟨name, value, rfl⟩ := binding
    obtain ⟨side, selected⟩ := bind_target_case looked
    have next := advanced
    simp only [PackedWorklist.advance, looked, bind, Option.bind_some] at next
    obtain ⟨mapState, computed, suffix⟩ := Option.bind_eq_some_iff.mp next
    obtain ⟨future, remapped, same⟩ := Option.bind_eq_some_iff.mp suffix
    obtain rfl := Option.some.inj same
    have boundSide : NativeBindEntry.EntryPlaced image side ((targets start exits).at side.exiting) (NativeSolverImage.shared start) := by
      rw [bind_target]; exact code.bind side
    have canAppend : resident.bindings.size < tc := by
      have fit := bounds.trail
      change resident.bindings.size + 1 ≤ tc at fit
      omega
    obtain ⟨new, moved, relocated⟩ := PackedRootedWorklist.bind_valid looked computed valid
    obtain ⟨after, steps, updated, nextRoot, graph, assigned, trace, pendingWrites, ran, framed, graphUsed, rootUsed,
      traceUsed, pendingUsed, parked, nextHeld, count, equationsRead, traceRead, _, extendsSource, endpoint⟩ :=
      NativeBindingRoots.fetched other extra vector point controls side code.dispatch boundSide code.gate code.binding
        space rootSpace terms resident.equations resident.bindings resident.root left right pending history resident.live resident.pending
        resident.history symbols lTerm rTerm leftRead rightRead selected name value looked mapState computed future remapped bounds.map
        bounds.nodes bounds.edges bounds.agenda canAppend old new held moved
    let scratch := graph ∪ trace ∪ pendingWrites ∪ NativeBindingPublish.written agenda trail
    have all : X86StateFrame.Frame clobbers (scratch ∪ assigned) before after := by
      have selected := framed.mono binding_clobbers (Finset.Subset.refl _)
      rw [regroup] at selected
      exact selected
    have exact := (PackedRemapCoordinates.coordinates mapState.mapped old new moved).1
    have rooted : PackedRootedWorklist.advance ⟨terms, (left, right) :: pending, history⟩ old =
        some (.working ⟨mapState.target, future, (name, value) :: history⟩, new) := by
      simp [PackedRootedWorklist.advance, looked, computed, remapped, moved]
    refine ⟨after, steps, scratch, assigned, new, rooted, ran, all,
      .union (.union (.union (.graph graphUsed) (.binding traceUsed)) (.pending pendingUsed)) .headers,
      Covered.rootWrites rootUsed, NativeRemapSnapshot.ready_restrict extendsSource parked.dispatch.termReady,
      (fun _ seen => Option.some.inj seen ▸ extendsSource), parked.dispatch.one,
      nextHeld, (fun _ seen => Option.some.inj seen ▸ relocated), exact, ?_⟩
    exact ⟨⟨updated, _, nextRoot, parked, equationsRead, traceRead⟩, count, by simp [trailDemand], endpoint⟩
  · have notBound : ∀ name value, action ≠ .bindVar name value := fun n v eq => binding ⟨n, v, eq⟩
    obtain ⟨after, steps, bytes, ran, framed, writes, original, later, one, arrived⟩ :=
      NativeSolverStep.fetched_other other extra vector code.toCorePlaced point controls space terms left right pending history
        resident symbols lTerm rTerm leftRead rightRead action looked result advanced bounds notBound
    exact ⟨after, steps, bytes, ∅, old, PackedRootedWorklist.advance_other looked advanced notBound old, ran,
      framed.mono (Finset.Subset.refl _) Finset.subset_union_left,
      writes, Covered.empty roots, original, later, one, held_after rootSpace held framed writes,
      (fun _ seen => valid.keep (later _ seen)), rfl, arrived⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverStep
