import Mettapedia.Machines.PreparedStoreProtocol

/-!
# Prepared publication realizes the existing ordered transform step

The lifecycle protocol's readiness conditions discharge actual occurrence
admission, including the complete region observed by removal. Its publication
has the same ordered result and preserves arbitrary ambient knowledge.
Ticket and recording bookkeeping are not extra store mutations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PublicationProtocol

open Mettapedia.Machines
open MeTTaCalculus.OccurrenceCommits

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type} [DecidableEq O] [DecidableEq (Tm a)]
  (label : O → Tm a)

def request (plan : PreparedStoreProtocol.Plan O (Tm a)) : OrderedStore.Publication (Tm a) O :=
  ⟨⟨plan.taken, [], plan.made⟩,
    match plan.operation with
    | .append _ => []
    | .erase keys => [⟨(fun key => decide (key ∈ keys)), plan.selected.toFinset⟩]⟩

/-- The lifecycle model supplies the actual admission obligations; no target
execution or source/target equality is assumed as a premise. -/
theorem ready_admitted (world : PreparedStoreProtocol.World O)
    (plan : PreparedStoreProtocol.Plan O (Tm a))
    (ready : PreparedStoreProtocol.Ready label world plan)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    (OrderedStore.step X a label).Admits (s := (knowledge, world.rows)) (request (a := a) plan) := by
  have made := PreparedStoreProtocol.ready_made label world plan ready
  refine ⟨⟨world.unique, PreparedStoreProtocol.ready_taken_distinct label world plan ready, made.1⟩,
    ?_, consistent⟩
  refine ⟨?_, by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit], made.2, ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr (PreparedStoreProtocol.ready_taken_present label world plan ready occurrence
      (List.mem_toFinset.mp member))
  · intro query member
    cases operation : plan.operation with
    | append values => simp [request, OrderedStore.Publication.commit, operation] at member
    | erase keys =>
        have same : query = ⟨(fun key => decide (key ∈ keys)), plan.selected.toFinset⟩ := by
          simpa [request, OrderedStore.Publication.commit, operation] using member
        subst query
        have selected : plan.selected = PreparedStoreProtocol.select label keys world.rows := by
          simpa [operation] using ready.2
        change regionOf label world.rows.toFinset _ = plan.selected.toFinset
        rw [selected]
        ext occurrence
        simp [regionOf, PreparedStoreProtocol.select]

theorem result_exact (world : PreparedStoreProtocol.World O)
    (plan : PreparedStoreProtocol.Plan O (Tm a)) (knowledge : EquationStore (Tm a))
    (admitted : (OrderedStore.step X a label).Admits (s := (knowledge, world.rows))
      (request (a := a) plan)) :
    (OrderedStore.step X a label).result (request (a := a) plan) admitted =
      (knowledge, PreparedStoreProtocol.updatedRows world plan) := rfl

/-- Every committed protocol publication is realized by an admitted tcalc
step with the same ordered rows, whether or not a receipt was requested. -/
theorem publication_realized (state : PreparedStoreProtocol.State O (Tm a))
    (expected : Option Nat) (receipt : Option (PreparedStoreProtocol.Receipt O (Tm a)))
    (committed : (PreparedStoreProtocol.publish label expected state).1 = .committed receipt)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    ∃ plan, state.slot = .pending plan ∧
      ∃ admitted : (OrderedStore.step X a label).Admits (s := (knowledge, state.world.rows))
          (request (a := a) plan),
        (OrderedStore.step X a label).result (request (a := a) plan) admitted =
          (knowledge, (PreparedStoreProtocol.publish label expected state).2.world.rows) := by
  obtain ⟨plan, pending, ready, _, _, updated⟩ :=
    PreparedStoreProtocol.successful_publication_exact label expected state receipt committed
  have admitted := ready_admitted X a label state.world plan ready knowledge consistent
  exact ⟨plan, pending, admitted, (result_exact X a label state.world plan knowledge admitted).trans
    (congrArg (Prod.mk knowledge) updated.symm)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.PublicationProtocol
