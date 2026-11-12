import Mettapedia.Machines.ImmediateStorePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PublicationProtocol

/-!
# Immediate store operations realize admitted transform publication

Admission comes from the immediate source operation's checked capacity and
freshness, not from an assumed target execution. The target executes the
existing ordered step and retains arbitrary consistent ambient knowledge.
Only the store publication is represented here; source failure/control events
and native implementation costs have their separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ImmediatePublication

open Mettapedia.Machines
open MeTTaCalculus.OccurrenceCommits

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type} [DecidableEq O] [DecidableEq (Tm a)]
  (label : O → Tm a)

def request (world : PreparedStoreProtocol.World O)
    (operation : PreparedStoreProtocol.Operation O (Tm a)) : OrderedStore.Publication (Tm a) O :=
  PublicationProtocol.request (a := a) (PreparedStoreProtocol.build label world operation none)

theorem admitted (world : PreparedStoreProtocol.World O)
    (operation : PreparedStoreProtocol.Operation O (Tm a))
    (allowed : PreparedStoreProtocol.Admissible world operation)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    (OrderedStore.step X a label).Admits (s := (knowledge, world.rows))
      (request (a := a) label world operation) :=
  PublicationProtocol.ready_admitted X a label world _
    (PreparedStoreProtocol.build_ready label world operation none allowed) knowledge consistent

/-- The independently defined append/filter source agrees with the result of
the actual admitted step, including survivor order and unchanged knowledge. -/
theorem result_exact (world : PreparedStoreProtocol.World O)
    (command : ImmediateStorePublication.Request O (Tm a))
    (capacity : command.effectCapacity = true)
    (allowed : PreparedStoreProtocol.Admissible world command.operation)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    (OrderedStore.step X a label).result (request (a := a) label world command.operation)
        (admitted X a label world command.operation allowed knowledge consistent) =
      (knowledge, (ImmediateStorePublication.immediate label world command).2.rows) := by
  rw [ImmediateStorePublication.immediate_result_rows label world command capacity allowed]
  rw [ImmediateStorePublication.direct_rows_eq_publication label world command.operation none]
  exact PublicationProtocol.result_exact X a label world _ knowledge _

theorem committed_realized (world : PreparedStoreProtocol.World O)
    (command : ImmediateStorePublication.Request O (Tm a))
    (committed : (ImmediateStorePublication.immediate label world command).1 = .committed)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    ∃ permitted : (OrderedStore.step X a label).Admits (s := (knowledge, world.rows))
        (request (a := a) label world command.operation),
      (OrderedStore.step X a label).result (request (a := a) label world command.operation) permitted =
        (knowledge, (ImmediateStorePublication.immediate label world command).2.rows) := by
  obtain ⟨capacity, allowed⟩ :=
    ImmediateStorePublication.committed_requires_capacity_and_admission label world command committed
  exact ⟨admitted X a label world command.operation allowed knowledge consistent,
    result_exact X a label world command capacity allowed knowledge consistent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ImmediatePublication
