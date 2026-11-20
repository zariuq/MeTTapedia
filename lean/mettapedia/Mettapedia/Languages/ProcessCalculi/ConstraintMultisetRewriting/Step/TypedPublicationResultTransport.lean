import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationApplicationTransport

/-!
# Complete publication results under coherent helper transport

Changing the source/helper presentation and composing the solver answer with
the inverse comparison gives the same typed rows and occurrences in the
same solver target frame. Principal realizations preserve the full set of
knowledge models; residual realizations retain the exact residual list.
The result comparison is derived from the publication implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ApplicationTransport

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type}
  {source target : State rules O}
  (application : Application levels O source) (stateIso : PlainIso levels source target)
  (helpers : Helpers target.frame) (comparison : helpers.frame ≅ application.schema.helpers.frame)
  (commuting : comparison.hom ≫ application.schema.helpers.weaken = helpers.weaken ≫ stateIso.frame.hom)

include stateIso commuting

theorem old_rows (occurrence : O) :
    ((target.label occurrence).reindex helpers.weaken).reindex (application.answer ≫ comparison.inv) =
      ((source.label occurrence).reindex application.schema.helpers.weaken).reindex application.answer := by
  have carried := SchemaTransport.row application.schema application.pick stateIso helpers comparison commuting occurrence
  change (target.label occurrence).reindex helpers.weaken =
    ((source.label occurrence).reindex application.schema.helpers.weaken).reindex comparison.hom at carried
  rw [carried, ← ContextualDependentEta.reindex_comp, Category.assoc,
    comparison.inv_hom_id, Category.comp_id]

omit stateIso commuting in
theorem output_row (code : Code application.schema.helpers.frame) :
    (code.reindex comparison.hom).raw.reindex (application.answer ≫ comparison.inv) =
      code.raw.reindex application.answer := by
  rw [Code.reindex_raw, Code.make_reindex_comp, Category.assoc,
    comparison.inv_hom_id, Category.comp_id]

omit stateIso commuting in
theorem made_rows :
    ((application.pick.val.fresh.zip (SchemaTransport.carry application.schema helpers comparison).outputs).map
      fun pair => (pair.1, pair.2.raw.reindex (application.answer ≫ comparison.inv))) =
    ((application.pick.val.fresh.zip application.schema.outputs).map
      fun pair => (pair.1, pair.2.raw.reindex application.answer)) := by
  change ((application.pick.val.fresh.zip (application.schema.outputs.map
    (fun code => code.reindex comparison.hom))).map _) = _
  simp only [List.zip_map_right, List.map_map, Function.comp_def, Prod.map, id_eq]
  apply List.map_congr_left
  intro pair member
  exact congrArg (Prod.mk pair.1) (output_row application helpers comparison pair.2)

variable [DecidableEq O]

theorem labels (admitted : application.schema.Admits application.pick) :
    ((carry application stateIso helpers comparison commuting).sourceResult
      ((source_admits application stateIso helpers comparison commuting).mpr admitted)).label =
      (application.sourceResult admitted).label := by
  change relabel
    (fun occurrence => ((target.label occurrence).reindex helpers.weaken).reindex (application.answer ≫ comparison.inv))
    ((application.pick.val.fresh.zip (SchemaTransport.carry application.schema helpers comparison).outputs).map
      fun pair => (pair.1, pair.2.raw.reindex (application.answer ≫ comparison.inv))) _ =
    relabel
      (fun occurrence => ((source.label occurrence).reindex application.schema.helpers.weaken).reindex application.answer)
      ((application.pick.val.fresh.zip application.schema.outputs).map
        fun pair => (pair.1, pair.2.raw.reindex application.answer)) _
  exact NativeTypesOnTheStep.relabel_congr
    (funext (old_rows application stateIso helpers comparison commuting))
    (made_rows application helpers comparison) _ _

def resultIso (admitted : application.schema.Admits application.pick) :
    PlainIso levels (application.sourceResult admitted)
      ((carry application stateIso helpers comparison commuting).sourceResult
        ((source_admits application stateIso helpers comparison commuting).mpr admitted)) where
  frame := Iso.refl application.target
  knowledge := by
    change (frames levels).Equivalent ((frames levels).applyStore (𝟙 application.target) application.basis.knowledge)
      (SchemaTransport.basis application.schema application.pick stateIso helpers comparison commuting application.basis).knowledge
    have identity : (frames levels).applyStore (𝟙 application.target) application.basis.knowledge =
        application.basis.knowledge := Frames.applyStore_id (X := frames levels) _
    rw [identity]
    exact (SchemaTransport.knowledge_equivalent application.schema application.pick
      stateIso helpers comparison commuting application.basis).symm
  present := by
    change (source.present \ application.pick.val.taken.toFinset) ∪ application.pick.val.fresh.toFinset =
      (target.present \ application.pick.val.taken.toFinset) ∪ application.pick.val.fresh.toFinset
    rw [stateIso.present]
  label := by
    intro occurrence
    change _ = ((application.sourceResult admitted).label occurrence).reindex (𝟙 application.target)
    exact (congrFun (labels application stateIso helpers comparison commuting admitted) occurrence).trans
      (ContextualDependentEta.reindex_id ((application.sourceResult admitted).label occurrence)).symm

theorem result_frame (admitted : application.schema.Admits application.pick) :
    (resultIso application stateIso helpers comparison commuting admitted).frame.hom = 𝟙 application.target := rfl

omit stateIso commuting in
theorem native_labels (admitted : application.schema.Admits application.pick) :
    ((realizationStep levels O).result application ((realization_admits_iff application).mpr admitted)).label =
      (application.sourceResult admitted).label := by
  have same := congrArg
    (fun state : State rules O => (⟨state.frame, state.label⟩ : Σ context : Context rules, O → TotalTerm context))
    (realization_result application admitted)
  exact eq_of_heq (Sigma.mk.inj same).2

def nativeResultIso (admitted : (realizationStep levels O).Admits application) :
    PlainIso levels ((realizationStep levels O).result application admitted)
      ((realizationStep levels O).result (carry application stateIso helpers comparison commuting)
        ((native_admits application stateIso helpers comparison commuting).mpr admitted)) := by
  have sourceAccepted := (realization_admits_iff application).mp admitted
  let derived := resultIso application stateIso helpers comparison commuting sourceAccepted
  refine ⟨Iso.refl application.target, derived.knowledge, ?_, ?_⟩
  · rw [realization_result application sourceAccepted,
      realization_result (carry application stateIso helpers comparison commuting)
        ((source_admits application stateIso helpers comparison commuting).mpr sourceAccepted)]
    exact derived.present
  · intro occurrence
    have firstLabels := native_labels application sourceAccepted
    have secondLabels := native_labels (carry application stateIso helpers comparison commuting)
      ((source_admits application stateIso helpers comparison commuting).mpr sourceAccepted)
    exact (congrFun secondLabels occurrence).trans ((derived.label occurrence).trans
      (congrArg (fun row : TotalTerm application.target => (frames levels).act (𝟙 application.target) row)
        (congrFun firstLabels occurrence).symm))

theorem nativeResultIso_frame (admitted : (realizationStep levels O).Admits application) :
    (nativeResultIso application stateIso helpers comparison commuting admitted).frame.hom =
      𝟙 application.target := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ApplicationTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ApplicationTransport.resultIso
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ApplicationTransport.nativeResultIso
