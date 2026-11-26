import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaDispatch
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# The native solver loop through its discard prefix

A discard transfers back to the installed agenda entry. Arbitrarily
many discard transitions run without copying the agenda or changing
its memory. A non-discard action is entered with its operands and
remaining root, rather than skipped or mistaken for an empty agenda.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeDiscardRun

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open PackedEquations (readWords)
open NativeTermDispatch (Targets choose)
open NativeAgendaDispatch (Context Placed handlers clobbers)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Prefix where
  discarded : ℕ
  fetches : ℕ
  pending : PackedWorklist.Words
  deriving DecidableEq, Repr

def discardPrefix (terms : PackedTerms.Arena) : PackedWorklist.Words → Prefix
  | [] => ⟨0, 2, []⟩
  | (left, right) :: rest =>
    let front := 15 + NativeTermDispatch.cost terms left right
    if choose terms left right = .discard then
      let later := discardPrefix terms rest
      ⟨later.discarded + 1, front + later.fetches, later.pending⟩
    else ⟨0, front, (left, right) :: rest⟩

theorem discard_action (terms : PackedTerms.Arena) (left right : Word)
    (discard : choose terms left right = .discard) :
    PackedUnifierAction.inspect terms left right = some .discard := by
  unfold choose at discard
  cases l : terms.nodes[left.toNat]? with
  | none => simp [l] at discard
  | some lNode =>
    cases r : terms.nodes[right.toNat]? with
    | none => simp [l, r] at discard
    | some rNode =>
      simp only [l, r] at discard
      simp [PackedUnifierAction.inspect, l, r, discard]

theorem packed_exact (terms : PackedTerms.Arena) (pending trail : PackedWorklist.Words) :
    PackedWorklist.run (discardPrefix terms pending).discarded (.working ⟨terms, pending, trail⟩) =
      some (.working ⟨terms, (discardPrefix terms pending).pending, trail⟩) := by
  induction pending with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨left, right⟩
    by_cases stop : choose terms left right = .discard
    · have inspect := discard_action terms left right stop
      simp only [discardPrefix, if_pos stop, PackedWorklist.run, PackedWorklist.step, PackedWorklist.advance,
        inspect, bind, Option.bind_some]
      exact ih
    · simp only [discardPrefix, if_neg stop, PackedWorklist.run]

def Boundary (agenda : PackedEquations.Arena) (terms : PackedTerms.Arena) (image : NativeImage.View)
    (base : BitVec 48) (done : ℕ) (target : Targets) (after : Native) : PackedWorklist.Words → Prop
  | [] => lookup after 11 = some 0 ∧ Nonempty (At image after base done)
  | (left, right) :: rest =>
    choose terms left right ≠ .discard ∧
      ∃ root, readWords agenda root = some rest ∧ lookup after 11 = some root ∧
        lookup after 1 = some left ∧ lookup after 2 = some right ∧
        Nonempty (At image after base (target.at (choose terms left right)))

/-- Actual fetched iterations skip exactly the discard prefix.
They reach either the completion label or a non-discard handler
with the original equation and the exact remaining agenda. -/
theorem fetched_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done : ℕ} {target : Targets}
    (placed : Placed image start done target) (returns : target.discard = start)
    {agendaCapacity nodeCapacity edgeCapacity : ℕ} {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
    {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {agenda : PackedEquations.Arena}
    {terms : PackedTerms.Arena} (pending : PackedWorklist.Words)
    {before : Native} (point : At image before base start) (controls : Controls before)
    {root : Word} (context : Context agendaLayout termLayout agenda terms root before)
    (known : readWords agenda root = some pending) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (discardPrefix terms pending).fetches).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      Boundary agenda terms image base done target after (discardPrefix terms pending).pending := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction pending generalizing before root with
  | nil =>
    have empty : NativeAgendaRecords.top agenda root = .empty :=
      NativeAgendaRecords.top_of_read agenda root [] known
    have zero := NativeAgendaRead.empty_cursor agenda root empty
    obtain ⟨after, ran, frame, atDone⟩ := NativeAgendaDispatch.fetched other extra vector point controls placed context
    simp only [NativeAgendaDispatch.Arrival, empty] at atDone
    rw [zero] at atDone
    rw [NativeAgendaDispatch.cost, empty, Nat.add_zero, NativeAgendaRead.cost_empty agenda root empty] at ran
    exact ⟨after, ran, frame, atDone⟩
  | cons first rest ih =>
    rcases first with ⟨left, right⟩
    obtain ⟨node, entry, pair, later⟩ := NativeAgendaRecords.top_of_read agenda root ((left, right) :: rest) known
    obtain ⟨equalLeft, equalRight⟩ := Prod.mk.inj pair
    obtain ⟨middle, ran, frame, atAction⟩ :=
      NativeAgendaDispatch.fetched other extra vector point controls placed context
    simp only [NativeAgendaDispatch.Arrival, entry] at atAction
    rw [equalLeft, equalRight] at atAction
    simp only [NativeAgendaDispatch.cost, entry, NativeAgendaRead.cost_pop agenda root node entry, equalLeft, equalRight] at ran
    obtain ⟨head, currentLeft, currentRight, _, ⟨address⟩⟩ := atAction
    by_cases discards : choose terms left right = .discard
    · have back : At image middle base start := by
        simpa only [discards, Targets.at, returns] using address
      obtain ⟨after, continued, laterFrame, terminal⟩ := ih back
        (controls.transport frame NativeAgendaDispatch.clobbers_data) (context.next frame head) later
      simp only [discardPrefix, if_pos discards]
      exact ⟨after, X86FuelPrefix.fetches_then _ _ before middle after ran continued,
        (frame.trans laterFrame).mono (by simp) (by simp), terminal⟩
    · simp only [discardPrefix, if_neg discards, Boundary]
      exact ⟨middle, ran, frame, discards, node.older, later, head, currentLeft, currentRight, ⟨address⟩⟩

theorem exhausts_if_all_discard (terms : PackedTerms.Arena) (pending : PackedWorklist.Words)
    (same : ∀ p ∈ pending, choose terms p.1 p.2 = .discard) : (discardPrefix terms pending).pending = [] := by
  induction pending with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨left, right⟩
    simp only [discardPrefix, if_pos (same (left, right) (by simp))]
    exact ih (fun p member => same p (List.mem_cons_of_mem _ member))

namespace Examples

private def terms : PackedTerms.Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 1⟩, 0, 0⟩, ⟨⟨1, 2⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩], #[0]⟩

theorem every_equal_occurrence_is_popped :
    (discardPrefix terms [(0, 0), (0, 0), (1, 1)]).discarded = 3 ∧
      (discardPrefix terms [(0, 0), (0, 0), (1, 1)]).pending = [] := by decide +kernel

theorem a_repeated_compound_is_not_a_discard_prefix :
    (discardPrefix terms [(0, 0), (3, 3), (1, 1)]).pending = [(3, 3), (1, 1)] := by decide +kernel

theorem a_malformed_handle_is_not_a_discard_prefix :
    (discardPrefix terms [(4, 4), (1, 1)]).discarded = 0 ∧
      (discardPrefix terms [(4, 4), (1, 1)]).pending = [(4, 4), (1, 1)] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeDiscardRun
