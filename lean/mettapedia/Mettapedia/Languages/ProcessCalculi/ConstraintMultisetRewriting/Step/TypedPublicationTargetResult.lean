import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationTargetUpdate

/-!
# Exact endpoints after answer-frame recertification

Publication's actual relabelling commutes with subsequent substitution.
Combined with the exact residual update, recertifying an application at a
compared endpoint reaches that whole endpoint, including its knowledge,
occurrences and every typed row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

namespace TargetChange

variable {source : State rules O} (schema : Schema levels O source.frame) (pick : Pick schema)
  {target observer : Context rules} (answer : target ⟶ schema.helpers.frame)

def madeRows : List (O × Make target) :=
  (pick.val.fresh.zip schema.outputs).map (fun pair => (pair.1, pair.2.raw.reindex answer))

omit [DecidableEq O] in
theorem madeRows_typed (licensed : ∀ code ∈ schema.outputs, code.At answer) :
    ∀ made ∈ madeRows schema pick answer, made.2.WellTyped := by
  intro made member
  obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp member
  exact pair.2.raw_typed answer (licensed pair.2 (List.of_mem_zip inside).2)

omit [DecidableEq O] in
theorem madeRows_precompose (refinement : observer ⟶ target) :
    madeRows schema pick (refinement ≫ answer) =
      (madeRows schema pick answer).map (fun made => (made.1, made.2.reindex refinement)) := by
  unfold madeRows
  rw [List.map_map]
  apply List.map_congr_left
  intro pair member
  exact congrArg (Prod.mk pair.1) (Code.make_reindex_comp pair.2.raw answer refinement).symm

theorem publication_labels (licensed : ∀ code ∈ schema.outputs, code.At answer)
    (refinement : observer ⟶ target) :
    (schema.publish pick (refinement ≫ answer)
      (fun code member => code.at_precompose (licensed code member) refinement)).label =
      fun occurrence => ((schema.publish pick answer licensed).label occurrence).reindex refinement := by
  let oldRows := fun occurrence => ((source.label occurrence).reindex schema.helpers.weaken).reindex answer
  let nextLicense : ∀ code ∈ schema.outputs, code.At (refinement ≫ answer) :=
    fun code member => code.at_precompose (licensed code member) refinement
  have rows : (fun occurrence => ((source.label occurrence).reindex schema.helpers.weaken).reindex (refinement ≫ answer)) =
      (fun occurrence => (oldRows occurrence).reindex refinement) :=
    funext fun occurrence => ContextualDependentEta.reindex_comp _ refinement answer
  have mappedTyped : ∀ made ∈ (madeRows schema pick answer).map (fun made => (made.1, made.2.reindex refinement)),
      made.2.WellTyped := by
    intro made member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact (madeRows_typed schema pick answer licensed original inside).reindex refinement
  change relabel _ (madeRows schema pick (refinement ≫ answer))
      (madeRows_typed schema pick (refinement ≫ answer) nextLicense) =
    fun occurrence => (relabel oldRows (madeRows schema pick answer)
      (madeRows_typed schema pick answer licensed) occurrence).reindex refinement
  exact (NativeTypesOnTheStep.relabel_congr rows (madeRows_precompose schema pick answer refinement)
      (madeRows_typed schema pick (refinement ≫ answer) nextLicense) mappedTyped).trans
    (relabel_move (levels := levels) refinement oldRows (madeRows schema pick answer)
      (madeRows_typed schema pick answer licensed) mappedTyped)

variable {desired : State rules O} (original : Application levels O source)
  (admitted : original.schema.Admits original.pick)
  (comparison : PlainIso levels (original.sourceResult admitted) desired)

theorem result_labels :
    ((application original admitted comparison).sourceResult (source_admitted original admitted comparison)).label =
      fun occurrence => ((original.sourceResult admitted).label occurrence).reindex comparison.frame.hom :=
  publication_labels original.schema original.pick original.answer (original.source_licenses admitted) comparison.frame.hom

theorem source_result :
    (application original admitted comparison).sourceResult (source_admitted original admitted comparison) = desired := by
  cases desired with
  | mk desiredFrame knowledge present label =>
      have labels := result_labels original admitted comparison
      have values := labels.trans (funext comparison.label).symm
      change (⟨desiredFrame, knowledge,
        (source.present \ original.pick.val.taken.toFinset) ∪ original.pick.val.fresh.toFinset,
        ((application original admitted comparison).sourceResult (source_admitted original admitted comparison)).label⟩ :
          State rules O) = ⟨desiredFrame, knowledge, present, label⟩
      exact congrArg₂ (fun occupied rows => (⟨desiredFrame, knowledge, occupied, rows⟩ : State rules O)) comparison.present values

theorem native_result :
    (realizationStep levels O).result (application original admitted comparison)
      (native_admitted original admitted comparison) = desired :=
  (realization_result (application original admitted comparison) (source_admitted original admitted comparison)).trans
    (source_result original admitted comparison)

end TargetChange

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange.source_result
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange.native_result
