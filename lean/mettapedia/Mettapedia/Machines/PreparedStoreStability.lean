import Mettapedia.Machines.PreparedStoreProtocol

/-!
# Reusing preparation across changes outside its dependencies

The existing primitive publication profile has append and complete key-region
removal. A writer preserves an append's readiness when it does not allocate
its reserved occurrences. It preserves a removal's ordered selection when
neither its takes nor its makes match that removal's keys. These sufficient
conditions derive readiness after the writer; they do not assume it.

This is not a general independence test for source code, guards, knowledge,
absence queries, or concurrency. No revision equality or second selection
pass is required by the direct publication theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedStoreStability

open PreparedStoreProtocol
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe u v
variable {O : Type u} {Key : Type v} [DecidableEq O] [DecidableEq Key] (label : O → Key)

def Preserves (waiting writer : Plan O Key) : Prop :=
  match waiting.operation with
  | .append made => Disjoint made.toFinset writer.made.toFinset
  | .erase keys =>
      (∀ occurrence ∈ writer.taken, label occurrence ∉ keys) ∧
      (∀ occurrence ∈ writer.made, label occurrence ∉ keys)

instance (waiting writer : Plan O Key) : Decidable (Preserves label waiting writer) := by
  unfold Preserves
  cases waiting.operation <;> infer_instance

def after (world : World O) (writer : Plan O Key) (ready : Ready label world writer) : World O :=
  ⟨world.space, updatedRows world writer, updated_unique label world writer ready⟩

theorem selection_unchanged (world : World O) (writer : Plan O Key) (keys : List Key)
    (notTaken : ∀ occurrence ∈ writer.taken, label occurrence ∉ keys)
    (notMade : ∀ occurrence ∈ writer.made, label occurrence ∉ keys) :
    select label keys (updatedRows world writer) = select label keys world.rows := by
  have madeEmpty : select label keys writer.made = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro occurrence member
    simp [notMade occurrence member]
  have oldSame : select label keys (OrderedStore.survivors world.rows writer.taken) =
      select label keys world.rows := by
    simp only [select, OrderedStore.survivors, List.filter_filter]
    apply List.filter_congr
    intro occurrence _
    by_cases selectedKey : label occurrence ∈ keys
    · have absent : occurrence ∉ writer.taken := fun member => notTaken occurrence member selectedKey
      simp [selectedKey, absent]
    · simp [selectedKey]
  calc
    select label keys (updatedRows world writer) =
        select label keys (OrderedStore.survivors world.rows writer.taken) ++
          select label keys writer.made := List.filter_append _ _
    _ = select label keys world.rows := by rw [oldSame, madeEmpty, List.append_nil]

theorem ready_after (world : World O) (waiting writer : Plan O Key)
    (waitingReady : Ready label world waiting) (writerReady : Ready label world writer)
    (preserved : Preserves label waiting writer) :
    Ready label (after label world writer writerReady) waiting := by
  refine ⟨waitingReady.1, ?_⟩
  cases operation : waiting.operation with
  | append made =>
      have initial : waiting.selected = [] ∧ made.Nodup ∧ Disjoint made.toFinset world.rows.toFinset := by
        simpa [operation] using waitingReady.2
      have fresh : Disjoint made.toFinset writer.made.toFinset := by
        simpa [Preserves, operation] using preserved
      change waiting.selected = [] ∧ made.Nodup ∧
        Disjoint made.toFinset (updatedRows world writer).toFinset
      refine ⟨initial.1, initial.2.1, Finset.disjoint_left.mpr ?_⟩
      intro occurrence reserved member
      rcases (updated_membership world writer occurrence).mp (List.mem_toFinset.mp member) with old | new
      · exact Finset.disjoint_left.mp initial.2.2 reserved (List.mem_toFinset.mpr old.1)
      · exact Finset.disjoint_left.mp fresh reserved (List.mem_toFinset.mpr new)
  | erase keys =>
      have initial : waiting.selected = select label keys world.rows := by
        simpa [operation] using waitingReady.2
      have safe : (∀ occurrence ∈ writer.taken, label occurrence ∉ keys) ∧
          (∀ occurrence ∈ writer.made, label occurrence ∉ keys) := by
        simpa [Preserves, operation] using preserved
      simpa [Ready, operation, after, selection_unchanged label world writer keys safe.1 safe.2] using initial

/-- A real intervening publication preserves the pending operation's
readiness from footprint conditions, even though the store has changed. -/
theorem ready_after_publication (state : State O Key) (writer waiting : Plan O Key)
    (pending : state.slot = .pending writer) (waitingReady : Ready label state.world waiting)
    (expected : Option Nat) (receipt : Option (Receipt O Key))
    (committed : (publish label expected state).1 = .committed receipt)
    (preserved : Preserves label waiting writer) :
    Ready label (publish label expected state).2.world waiting := by
  obtain ⟨actual, found, writerReady, ticket, _, _⟩ :=
    successful_publication_exact label expected state receipt committed
  have same : actual = writer := Slot.pending.inj (found.symm.trans pending)
  subst actual
  rw [ticket, publish_under_ready label state writer pending writerReady]
  have ready := ready_after label state.world waiting writer waitingReady writerReady preserved
  by_cases empty : writer.operation.kind = .erase ∧ writer.taken = [] <;>
    simpa [publishReady, after, empty] using ready

/-- Once readiness has been preserved, the checked wrapper and the direct
publication agree without any additional semantic matching obligation. -/
theorem direct_after_change (state : State O Key) (waiting writer : Plan O Key)
    (waitingReady : Ready label state.world waiting) (writerReady : Ready label state.world writer)
    (preserved : Preserves label waiting writer) :
    let resumed : State O Key :=
      { state with world := after label state.world writer writerReady, slot := .pending waiting }
    publish label waiting.ticket resumed = publishReady label resumed waiting
      (ready_after label state.world waiting writer waitingReady writerReady preserved) := by
  exact publish_under_ready label _ waiting rfl _

namespace Controls

def value (occurrence : Nat) : Nat := occurrence % 2
def original : World Nat := ⟨4, [0, 1], by decide⟩
def waiting := build value original (.erase [0]) (some 7)
def unrelated := build value original (.append [3]) none
def interfering := build value original (.append [2]) none
def changed := after value original unrelated (build_ready value original _ none (by decide))

theorem unrelated_addition_keeps_preparation :
    original.rows ≠ changed.rows ∧ Ready value changed waiting ∧ Preserves value waiting unrelated := by
  decide

theorem disjoint_takes_are_not_sufficient :
    Disjoint waiting.taken.toFinset interfering.taken.toFinset ∧
      ¬ Preserves value waiting interfering ∧
      ¬ Ready value (after value original interfering (build_ready value original _ none (by decide))) waiting := by
  decide

def reserved := build value original (.append [2]) none

theorem competing_makes_invalidate_reserved_identity :
    ¬ Preserves value reserved interfering ∧
      ¬ Ready value (after value original interfering (build_ready value original _ none (by decide))) reserved := by
  decide

end Controls

end Mettapedia.Machines.PreparedStoreStability
