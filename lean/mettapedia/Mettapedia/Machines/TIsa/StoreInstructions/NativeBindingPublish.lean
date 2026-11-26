import Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailPublish
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaPublish
import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingTrail
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionMemory

/-!
# Entering the next solver state after staging a binding

Both record sequences are initialized before this block runs.
It advances the trail count, restores the term view, then
advances the agenda count and returns to dispatch. No solver
transition is taken between these instructions. This is a
single transition of the sequential solver, not an assertion
of an atomic multiword store for concurrent observers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingPublish

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeArenaGeometry (Region)
open NativeTrailReserve (Descriptor)
open NativeAgendaRecords (Ready Records)
open PackedEquations (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def rootCode : List ℕ := registerCode 0x89 0 11
def termCode : List ℕ := X86DataLoad.code true 15 6 24 ++ X86DataLoad.code true 3 6 16
def agendaLenCode : List ℕ := registerCode 0x89 0 14

def emit (start next : ℕ) : List ℕ :=
  NativeTrailPublish.emit ++ (NativeDecisions.compareBytes .notEqual 0 3 (start + 27) (start + 39) ++
    (rootCode ++ (termCode ++ (agendaLenCode ++ NativeAgendaPublish.emit (start + 56) next))))

theorem emit_size (start next : ℕ) : (emit start next).length = 77 := by
  simp only [emit, List.length_append, NativeTrailPublish.emit_size, NativeDecisions.compare_size,
    show rootCode.length = 3 from rfl, show termCode.length = 14 from rfl, show agendaLenCode.length = 3 from rfl,
    NativeAgendaPublish.emit_size]

structure Placed (image : NativeImage.View) (start next : ℕ) : Prop where
  extent : start + 77 ≤ image.size
  trail : NativeTrailPublish.Placed image start
  nonempty : CompareBranch image (start + 27) (start + 39) .notEqual 0 3
  root : Code image (start + 36) rootCode
  terms : Code image (start + 39) termCode
  length : Code image (start + 53) agendaLenCode
  agenda : NativeAgendaPublish.Placed image (start + 56) next

theorem placed_of_emitted (image : NativeImage.View) (start next : ℕ)
    (extent : start + 77 ≤ image.size) (continues : next ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next)) : Placed image start next := by
  obtain ⟨trail, rest⟩ := NativeWords.code_append (show Code image start (NativeTrailPublish.emit ++ _) from code)
  rw [NativeTrailPublish.emit_size] at rest
  obtain ⟨check, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨root, rest⟩ := NativeWords.code_append rest
  obtain ⟨terms, rest⟩ := NativeWords.code_append rest
  obtain ⟨length, agenda⟩ := NativeWords.code_append rest
  exact ⟨extent, NativeTrailPublish.placed_of_emitted image _ (by omega) trail,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by omega) short check, root, terms, length,
    NativeAgendaPublish.placed_of_emitted image _ next (by omega) continues short agenda⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rbx, .rdx, .rsi, .r11, .r14, .r15, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity mapCapacity agendaCapacity trailCapacity : ℕ}
variable {term : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {agenda : NativeAgendaRecords.Layout agendaCapacity} {trail : NativeAgendaRecords.Layout trailCapacity}
variable {frame : Descriptor}

def header {capacity : ℕ} (layout : NativeAgendaRecords.Layout capacity) : Finset ℕ :=
  footprint (layout.header.cell 0).address

def written (agenda : NativeAgendaRecords.Layout agendaCapacity) (trail : NativeAgendaRecords.Layout trailCapacity) : Finset ℕ :=
  header trail ∪ header agenda

structure Geometry (term : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (agenda : NativeAgendaRecords.Layout agendaCapacity) (trail : NativeAgendaRecords.Layout trailCapacity)
    (frame : Descriptor) (image : NativeImage.View) (base : BitVec 48) : Prop where
  agendaCode : CodeApart image base (header agenda)
  trailCode : CodeApart image base (header trail)
  counts : Disjoint (header trail) (header agenda)
  agendaRecord : ∀ i j, Disjoint (footprint ((agenda.record i).cell j).address) (header trail)
  trailRecord : ∀ i j, Disjoint (footprint ((trail.record i).cell j).address) (header agenda)
  node : ∀ i j, Disjoint (NativeSubstitutionMemory.nodeBytes term i j) (written agenda trail)
  edge : ∀ i, Disjoint (NativeSubstitutionMemory.edgeBytes term i) (written agenda trail)
  frame : ∀ j : Fin 8, Disjoint (footprint (frame.cell j).address) (written agenda trail)

def newRoot (old updated : Arena) : Word :=
  if updated.size = old.size then 0 else BitVec.ofNat 64 updated.size

structure Input (term : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (agenda : NativeAgendaRecords.Layout agendaCapacity) (trail : NativeAgendaRecords.Layout trailCapacity)
    (frame : Descriptor) (terms : PackedTerms.Arena) (old updated oldTrail newTrail : Arena) (native : Native) : Prop where
  staged : NativeSubstitutionFrame.Ready term map frame.substitution terms native
  terms : NativeTermArena.Ready term terms native
  agendaOld : Ready agenda old native
  agendaNew : Records agenda updated native
  traceOld : Ready trail oldTrail native
  traceNew : Records trail newTrail native
  trailPtr : Reads native (frame.cell 7).address trail.words.pointer
  agendaPtr : lookup native 5 = some agenda.words.pointer
  floor : lookup native 3 = some (BitVec.ofNat 64 old.size)
  length : lookup native 0 = some (BitVec.ofNat 64 updated.size)
  emptyCursor : lookup native 11 = some 0
  one : lookup native 13 = some 1
  zero : lookup native 12 = some 0

private def stackBase : NativeLoads.Base := ⟨6, by decide, by decide⟩
private def countLoad (frame : Descriptor) (terms : PackedTerms.Arena) : NativeLoads.Load stackBase frame.pointer :=
  ⟨15, by decide, 24, frame.cell 3, BitVec.ofNat 64 terms.nodes.size⟩
private def nodesLoad (frame : Descriptor) (term : NativeTermArena.Layout nodeCapacity edgeCapacity) :
    NativeLoads.Load stackBase frame.pointer := ⟨3, by decide, 16, frame.cell 2, term.nodes.pointer⟩
private def loads (frame : Descriptor) (term : NativeTermArena.Layout nodeCapacity edgeCapacity) (terms : PackedTerms.Arena) :
    List (NativeLoads.Load stackBase frame.pointer) := [countLoad frame terms, nodesLoad frame term]

private theorem word_count (layout : NativeAgendaRecords.Layout agendaCapacity) (size : ℕ) (bound : size ≤ agendaCapacity) :
    (BitVec.ofNat 64 size).toNat = size := by
  have limit := layout.words.positive_room (show 0 < 3 * (agendaCapacity + 1) by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Restore the solver entry with the exact new term extent,
agenda head, and live trail. The only stores of this block
are the two count words. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start next)
    (space : Geometry term agenda trail frame image base)
    (terms : PackedTerms.Arena) (old updated oldTrail newTrail : Arena) (advanced : newTrail.size = oldTrail.size + 1)
    (input : Input term map agenda trail frame terms old updated oldTrail newTrail before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      steps = 14 + (if updated.size = old.size then 0 else 1) ∧
      X86StateFrame.Frame clobbers (written agenda trail) before after ∧
      NativeAgendaDispatch.Context agenda term updated terms (newRoot old updated) after ∧
      Ready trail newTrail after ∧ NativeSubstitutionFrame.Ready term map frame.substitution terms after ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have stack : lookup before 4 = some frame.pointer :=
    frame.substitution_pointer ▸ input.staged.pointer
  obtain ⟨a, finishedTrail, trailFrame, trailReady, stackKnown, ⟨atEmpty⟩⟩ := NativeTrailPublish.fetched other extra vector
    point controls placed.trail frame stack input.trailPtr input.traceOld input.traceNew advanced input.one space.trailCode
  have length := (trailFrame.lookup 0 (by decide)).trans input.length
  obtain ⟨b, checked, cmp, ⟨test⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector atEmpty .notEqual 0 3 placed.nonempty _ _ length ((trailFrame.lookup 3 (by decide)).trans input.floor)
  have equal : BitVec.ofNat 64 updated.size = BitVec.ofNat 64 old.size ↔ updated.size = old.size := by
    constructor
    · intro same
      exact (word_count agenda _ input.agendaNew.fits).symm.trans
        ((congrArg BitVec.toNat same).trans input.agendaOld.count_word)
    · exact congrArg (BitVec.ofNat 64)
  simp only [Comparison.evaluate, bne_iff_ne, ne_eq, equal] at test
  let branchEffects : Finset Register := {.r11, .rflags, .rip}
  have selected : ∃ c count, (X86FuelPrefix.fetches count).run a = .ok () c ∧
      count = 2 + (if updated.size = old.size then 0 else 1) ∧
      X86StateFrame.Frame branchEffects ∅ a c ∧ lookup c 11 = some (newRoot old updated) ∧
      Nonempty (At image c base (start + 39)) := by
    by_cases same : updated.size = old.size
    · simp only [same, not_true_eq_false, if_false] at test
      exact ⟨b, 2, checked, by simp [same],
        (X86StateFrame.registerOnly cmp).mono (by decide) (Finset.Subset.refl _), by
          simpa only [newRoot, if_pos same] using (cmp.lookup 11 (by decide)).trans
            ((trailFrame.lookup 11 (by decide)).trans input.emptyCursor), ⟨test⟩⟩
    · have atNew : At image b base (start + 36) := by simpa [same] using test
      obtain ⟨c, installed, move, root, arrival⟩ := X86PlacedRegisterMove.executes
        (handlers other extra) vector atNew (by omega) 0 11 (BitVec.ofNat 64 updated.size)
        ((cmp.lookup 0 (by decide)).trans length) placed.root
      refine ⟨c, 3, X86FuelPrefix.fetches_then 2 1 a b c checked installed, by simp [same],
        (X86StateFrame.registerOnly (cmp.trans move)).mono (by decide) (Finset.Subset.refl _), ?_, arrival⟩
      simpa only [newRoot, if_neg same] using root
  obtain ⟨c, rootCount, routed, routeCount, routeFrame, rootKnown, ⟨atTerms⟩⟩ := selected
  have throughRoot := trailFrame.trans routeFrame
  have held (move : NativeLoads.Load stackBase frame.pointer) (member : move ∈ loads frame term terms) :
      Reads c move.cell.address move.value := by
    simp only [loads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have word := input.staged.word 3
      rw [frame.substitution_cell] at word
      exact word.preserved throughRoot (by
        simp only [Finset.union_empty]
        exact (Finset.disjoint_union_right.mp (space.frame 3)).1)
    · have word := input.staged.word 2
      rw [frame.substitution_cell] at word
      exact word.preserved throughRoot (by
        simp only [Finset.union_empty]
        exact (Finset.disjoint_union_right.mp (space.frame 2)).1)
  obtain ⟨d, loaded, termFrame, termWords, ⟨atLen⟩⟩ := NativeLoads.fetched other extra vector
    atTerms (controls.transport throughRoot (by decide)) (loads frame term terms)
    (by change start + 39 + 14 ≤ image.size; omega) placed.terms
    ((routeFrame.lookup 6 (by decide)).trans stackKnown) held (by simp [loads, countLoad, nodesLoad])
  have regEffects : NativeLoads.clobbers (loads frame term terms) =
      ({key 15, .rip} ∪ ({key 3, .rip} ∪ ∅) : Finset Register) := rfl
  rw [regEffects] at termFrame
  have pastTerms := throughRoot.trans termFrame
  obtain ⟨e, copied, move, lengthForPublish, ⟨atPublish⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image d base (start + 53) from atLen) (by omega) 0 14
    (BitVec.ofNat 64 updated.size) ((pastTerms.lookup 0 (by decide)).trans input.length) placed.length
  have throughLen := pastTerms.trans (X86StateFrame.registerOnly move)
  have agendaRecords : Records agenda updated e :=
    ⟨input.agendaNew.fits, fun i j => (input.agendaNew.node i j).preserved throughLen
      (by simp only [Finset.union_empty]; exact space.agendaRecord _ j)⟩
  obtain ⟨after, finished, publishFrame, agendaReady, tagTwo, endpoint⟩ := NativeAgendaPublish.fetched
    other extra vector (show At image e base (start + 56) from atPublish) (controls.transport throughLen (by decide))
    placed.agenda agendaRecords ((throughLen.lookup 5 (by decide)).trans input.agendaPtr) lengthForPublish space.agendaCode
  have all : X86StateFrame.Frame clobbers (written agenda trail) before after :=
    (throughLen.trans publishFrame).mono (by decide) (by
      simp only [Finset.union_empty, written, header]
      exact Finset.Subset.refl _)
  have afterLoads := (X86StateFrame.registerOnly move).trans publishFrame
  have finalTerm : NativeAgendaDispatch.Context agenda term updated terms (newRoot old updated) after :=
    ⟨agendaReady, input.terms.kept all space.node space.edge, (all.lookup 5 (by decide)).trans input.agendaPtr,
      (afterLoads.lookup 3 (by decide)).trans (termWords (nodesLoad frame term) (by simp [loads])),
      ((termFrame.trans afterLoads).lookup 11 (by decide)).trans rootKnown,
      (afterLoads.lookup 15 (by decide)).trans (termWords (countLoad frame terms) (by simp [loads])),
      (all.lookup 12 (by decide)).trans input.zero, (all.lookup 13 (by decide)).trans input.one, tagTwo⟩
  have newTrace : Ready trail newTrail after := by
    have afterRoute := routeFrame.trans (termFrame.trans afterLoads)
    refine ⟨trailReady.fits, trailReady.count.preserved afterRoute ?_,
      fun i j => (trailReady.node i j).preserved afterRoute ?_⟩
    · simp only [Finset.empty_union]
      exact space.counts
    · simp only [Finset.empty_union]
      exact space.trailRecord _ j
  have descriptors := input.staged.kept all (by decide) (fun j => by
    rw [frame.substitution_cell]
    exact space.frame ⟨j.val, by have := j.isLt; omega⟩)
  have chosen := X86FuelPrefix.fetches_then 5 rootCount before a c finishedTrail routed
  have throughCopy := X86FuelPrefix.fetches_then (5 + rootCount + 2) 1 before d e
    (X86FuelPrefix.fetches_then (5 + rootCount) 2 before c d chosen loaded) copied
  refine ⟨after, _, X86FuelPrefix.fetches_then (5 + rootCount + 2 + 1) 4 before e after throughCopy finished,
    ?_, all, finalTerm, newTrace, descriptors, endpoint⟩
  rw [routeCount]
  omega

namespace Examples

theorem nonempty_allocation_is_not_a_nonempty_agenda :
    newRoot #[⟨0, 2, 2⟩] #[⟨0, 2, 2⟩] = 0 := by decide +kernel

theorem an_appended_equation_is_the_new_head :
    newRoot #[⟨0, 2, 2⟩] #[⟨0, 2, 2⟩, ⟨0, 5, 7⟩] = 2 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingPublish
