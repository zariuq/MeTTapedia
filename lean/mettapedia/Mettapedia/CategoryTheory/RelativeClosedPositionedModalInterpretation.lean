import Mettapedia.CategoryTheory.RelativeClosedPositionedModalExpressions
import Mettapedia.CategoryTheory.RelativeClosedRawFunctionReadout
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicNativeMeaning
import Mettapedia.CategoryTheory.PositionedRewritePredicatePower

/-!
# Independent readings of the complete positioned-modal expression

The structural evaluator first reads both supplied function arguments, then
their implication, complete instance quantification and actual focus image.
In a native higher-order doctrine the resulting complete arrow equals the
independently constructed positioned-modal operation. This comparison is
earned from classification and the quantified supplied-input readouts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPositionedModal.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax GeneratedCategory RelativeClosedPredicateLogic

universe k w z p
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base)

theorem pointwiseImplication_read {context : Object (signature (C := C))} {parameter : D} (value : C)
    {first second : RawHom context (RelativeClosedPredicateLogic.power value)}
    {before after : parameter ⟶ RelativeClosedPredicateLogic.Interpretation.targetPower base meaning value}
    (contextRead : RawInterpretation.ObjectReads
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) context parameter)
    (firstRead : RawInterpretation.Reads
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) first before)
    (secondRead : RawInterpretation.Reads
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning) second after) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (pointwiseImplicationRaw value first second)
      (curry (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
        (uncurry before) (uncurry after))) :=
  RawInterpretation.quote _ contextRead rfl (RelativeClosedPredicateLogic.Interpretation.omega_read base meaning)
    (RelativeClosedPredicateLogic.Interpretation.implication_read base meaning
      (RawFunctionInterpretation.read _ contextRead rfl
        (RelativeClosedPredicateLogic.Interpretation.omega_read base meaning) firstRead)
      (RawFunctionInterpretation.read _ contextRead rfl
        (RelativeClosedPredicateLogic.Interpretation.omega_read base meaning) secondRead))

variable {instances assignments assay carrier outgoing : C}

abbrev targetProfiles :=
  RelativeClosedPredicateLogic.Interpretation.targetPower base meaning assay ⊗
    RelativeClosedPredicateLogic.Interpretation.targetPower base meaning outgoing

def conditionOperator (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    targetProfiles base meaning (assay := assay) (outgoing := outgoing) ⟶
      RelativeClosedPredicateLogic.Interpretation.targetPower base meaning instances :=
  curry (InternalPredicateImplication.applyOperation meaning.predicates meaning.implication
    (uncurry (fst _ _ ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map instantiate)))
    (uncurry (snd _ _ ≫ InternalPredicateQuantifier.precomposition meaning.predicates (base.map reduct))))

def modalityOperator (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    targetProfiles base meaning (assay := assay) (outgoing := outgoing) ⟶
      RelativeClosedPredicateLogic.Interpretation.targetPower base meaning carrier :=
  (conditionOperator base meaning instantiate reduct ≫ meaning.universal forget) ≫ meaning.existential focus

theorem condition_read (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (conditionRaw instantiate reduct) (conditionOperator base meaning instantiate reduct) := by
  let values := RelativeClosedPredicateLogic.Interpretation.assignment base meaning
  have firstPower := RelativeClosedPredicateLogic.Interpretation.power_read base meaning assay
  have secondPower := RelativeClosedPredicateLogic.Interpretation.power_read base meaning outgoing
  exact pointwiseImplication_read base meaning instances (values.evaluate_product firstPower secondPower)
    (RawInterpretation.compose values
      (RawInterpretation.first values (left := RelativeClosedPredicateLogic.power assay)
        (right := RelativeClosedPredicateLogic.power outgoing) firstPower secondPower)
      (RelativeClosedPredicateLogic.Interpretation.precomposition_read base meaning instantiate))
    (RawInterpretation.compose values
      (RawInterpretation.second values (left := RelativeClosedPredicateLogic.power assay)
        (right := RelativeClosedPredicateLogic.power outgoing) firstPower secondPower)
      (RelativeClosedPredicateLogic.Interpretation.precomposition_read base meaning reduct))

theorem modality_read (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (modalityRaw forget focus instantiate reduct) (modalityOperator base meaning forget focus instantiate reduct) :=
  RawInterpretation.compose _ (RawInterpretation.compose _ (condition_read base meaning instantiate reduct) rfl) rfl

theorem possibility_read {events programs : C} (source target : events ⟶ programs) :
    RawInterpretation.Reads (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      (possibilityRaw source target)
      (InternalPredicateQuantifier.precomposition meaning.predicates (base.map target) ≫ meaning.existential source) :=
  RawInterpretation.compose _ (RelativeClosedPredicateLogic.Interpretation.precomposition_read base meaning target) rfl

variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

omit [HasFiniteLimits D] in
theorem native_condition_supplied (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    {parameter : D} (inputs : parameter ⟶ targetProfiles base (NativeMeaning.meaning base doctrine)) :
    HigherOrderInternalPredicateObject.family doctrine
        (inputs ≫ conditionOperator base (NativeMeaning.meaning base doctrine) instantiate reduct) =
      PositionedRewritePredicatePower.conditionAt doctrine (base.map instantiate) (base.map reduct) inputs := by
  change HigherOrderInternalPredicateObject.decode doctrine (uncurry (inputs ≫ curry _)) = _
  dsimp only [NativeMeaning.meaning]
  rw [uncurry_natural_left, uncurry_curry,
    InternalPredicateImplication.apply_substitution,
    HigherOrderInternalPredicateImplication.applied_read]
  rw [← uncurry_natural_left, ← uncurry_natural_left]
  change HigherOrderInternalPredicateObject.family doctrine
      (inputs ≫ (fst _ _ ≫ InternalPredicateQuantifier.precomposition
        (HigherOrderInternalPredicateObject.operations doctrine) (base.map instantiate))) ⇨
    HigherOrderInternalPredicateObject.family doctrine
      (inputs ≫ (snd _ _ ≫ InternalPredicateQuantifier.precomposition
        (HigherOrderInternalPredicateObject.operations doctrine) (base.map reduct))) = _
  rw [← Category.assoc, ← Category.assoc,
    HigherOrderInternalPredicateQuantifier.precomposition_supplied,
    HigherOrderInternalPredicateQuantifier.precomposition_supplied]
  rfl

omit [HasFiniteLimits D] in
theorem native_modality_supplied (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    {parameter : D} (inputs : parameter ⟶ targetProfiles base (NativeMeaning.meaning base doctrine)) :
    HigherOrderInternalPredicateObject.family doctrine
        (inputs ≫ modalityOperator base (NativeMeaning.meaning base doctrine) forget focus instantiate reduct) =
      PositionedRewritePredicatePower.modalAt doctrine (base.map forget) (base.map focus)
        (base.map instantiate) (base.map reduct) inputs := by
  change HigherOrderInternalPredicateObject.family doctrine
    (inputs ≫ ((conditionOperator base (NativeMeaning.meaning base doctrine) instantiate reduct ≫
      HigherOrderInternalPredicateQuantifier.forallOperation doctrine (base.map forget)) ≫
      HigherOrderInternalPredicateQuantifier.existsOperation doctrine (base.map focus))) = _
  rw [← Category.assoc, ← Category.assoc,
    HigherOrderInternalPredicateQuantifier.exists_supplied,
    HigherOrderInternalPredicateQuantifier.forall_supplied,
    native_condition_supplied]
  rfl

omit [HasFiniteLimits D] in
theorem native_modality_complete (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    modalityOperator base (NativeMeaning.meaning base doctrine) forget focus instantiate reduct =
      PositionedRewritePredicatePower.operation doctrine (base.map forget) (base.map focus)
        (base.map instantiate) (base.map reduct) :=
  PositionedRewritePredicatePower.operation_unique doctrine (base.map forget) (base.map focus)
    (base.map instantiate) (base.map reduct) _
    (by
      have actual := native_modality_supplied base doctrine forget focus instantiate reduct (𝟙 _)
      change doctrine.reindex
        (uncurry (𝟙 (PositionedRewritePredicatePower.profiles doctrine (base.obj assay) (base.obj outgoing)) ≫
          modalityOperator base (NativeMeaning.meaning base doctrine) forget focus instantiate reduct))
        doctrine.generic.truth = _ at actual
      change doctrine.reindex
        (uncurry (modalityOperator base (NativeMeaning.meaning base doctrine) forget focus instantiate reduct))
        doctrine.generic.truth = PositionedRewritePredicatePower.modalAt doctrine (base.map forget)
          (base.map focus) (base.map instantiate) (base.map reduct)
          (𝟙 (targetProfiles base (NativeMeaning.meaning base doctrine)))
      simpa only [Category.id_comp] using actual)

end Mettapedia.CategoryTheory.RelativeClosedPositionedModal.Interpretation
