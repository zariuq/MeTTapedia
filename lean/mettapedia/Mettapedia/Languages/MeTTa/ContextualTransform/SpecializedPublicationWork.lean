import Mettapedia.Data.List.PublicationSpecializationWork
import Mettapedia.Languages.MeTTa.ContextualTransform.ImmediateRemoval
import Mettapedia.Languages.MeTTa.ContextualTransform.CountedStoreInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ImmediatePublication

/-!
# Measured append and first deletion retain their source interpretation

The list algorithms have independent results and measured work. Here their
outputs meet the existing ordered source contracts and admitted tcalc steps.
The append cost profile studies redundant empty-take contraction; it does not
describe the current native scalar writer. First deletion is a store policy,
not an outer first-answer consumer with possibly answerless effectful firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.SpecializedPublicationWork

open Mettapedia.Data.List
open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open StoreAndDemand

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj) {O : Type} [DecidableEq O] [DecidableEq (Tm a)]
  (label : O → Tm a)

omit [DecidableEq O] [DecidableEq (Tm a)] in
theorem append_matches_source (rows made : List O) :
    ((PublicationSpecializationWork.append rows made).value.map label, made.length) =
      StoreEffects.route (rows.map label) (made.map label) := by
  simp [PublicationSpecializationWork.append_value, StoreEffects.route]

theorem append_committed_realized (world : PreparedStoreProtocol.World O) (made : List O)
    (capacity : Bool)
    (committed : (ImmediateStorePublication.immediate label world ⟨.append made, capacity⟩).1 = .committed)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    ∃ permitted : (OrderedStore.step X a label).Admits (s := (knowledge, world.rows))
        (ImmediatePublication.request (Tm := Tm) (a := a) label world (.append made)),
      (OrderedStore.step X a label).result
          (ImmediatePublication.request (Tm := Tm) (a := a) label world (.append made)) permitted =
        (knowledge, (PublicationSpecializationWork.append world.rows made).value) := by
  obtain ⟨available, allowed⟩ :=
    ImmediateStorePublication.committed_requires_capacity_and_admission label world ⟨.append made, capacity⟩ committed
  obtain ⟨permitted, result⟩ :=
    ImmediatePublication.committed_realized X a label world ⟨.append made, capacity⟩ committed knowledge consistent
  refine ⟨permitted, ?_⟩
  rw [result, ImmediateStorePublication.immediate_result_rows label world ⟨.append made, capacity⟩ available allowed]
  simp [ImmediateStorePublication.directRows, PublicationSpecializationWork.append_value]

omit [DecidableEq O] [DecidableEq (Tm a)] in
theorem first_matches_source (select : Tm a → Bool) (rows : List O) :
    ((PublicationSpecializationWork.first (fun row => select (label row)) rows).value.1.map label) =
      StoreEffects.removeOne select (rows.map label) := by
  rw [PublicationSpecializationWork.first_as_counted, CountedErase.erase_map,
    ImmediateRemoval.one_is_counted_one]

omit [DecidableEq (Tm a)] in
theorem first_realized (select : Tm a → Bool) (rows : List O) (unique : rows.Nodup)
    (knowledge : EquationStore (Tm a)) (consistent : X.Solvable knowledge) :
    ∃ permitted : (OrderedStore.step X a label).Admits (s := (knowledge, rows))
        (CountedStoreInterpretation.request (Tm := Tm) (a := a) label select 1 rows),
      (((OrderedStore.step X a label).result
          (CountedStoreInterpretation.request (Tm := Tm) (a := a) label select 1 rows) permitted).2.map label) =
        (PublicationSpecializationWork.first (fun row => select (label row)) rows).value.1.map label := by
  let permitted := CountedStoreInterpretation.admitted X a label select 1 rows unique knowledge consistent
  refine ⟨permitted, ?_⟩
  rw [CountedStoreInterpretation.up_to_correspondence X a label select 1 rows unique knowledge permitted,
    PublicationSpecializationWork.first_as_counted, CountedErase.erase_map]

end Mettapedia.Languages.MeTTa.ContextualTransform.SpecializedPublicationWork
