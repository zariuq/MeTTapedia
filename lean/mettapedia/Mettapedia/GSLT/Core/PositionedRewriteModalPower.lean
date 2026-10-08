import Mettapedia.CategoryTheory.PositionedRewritePredicatePower
import Mettapedia.GSLT.Core.PositionedRewriteModal

/-!
# Parameterized native rewrite modalities

The selected rewrite's modality is an internal function of independently
supplied rely and postcondition functions. The construction retains the
complete assay and reduct, and binds every rely instance. Evaluation and
parameter substitution are earned from the native higher-order doctrine.
The operational readout uses a supplied complete rule instance separately
from the erased image predicate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteModalPower

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open PositionedRewriteModal PositionedRewritePredicatePower PositionedRewritePredicateLogic

universe u v
variable {theory : Theory.{u,v}} {rule : Rule theory}
variable (frame : Frame rule) (classifier : Subobject.Classifier theory.closed.Obj)

abbrev inputProfiles : theory.closed.Obj :=
  profiles (Frame.doctrine classifier) frame.assay (frame.assay ⨯ theory.program)

def operator : inputProfiles frame classifier ⟶ power (Frame.doctrine classifier) frame.carrier :=
  operation (Frame.doctrine classifier) frame.forget frame.focus frame.instantiate frame.outgoing

variable {parameter : theory.closed.Obj}
variable (inputs : parameter ⟶ inputProfiles frame classifier)

theorem output_reading :
    family (Frame.doctrine classifier) (inputs ≫ operator frame classifier) =
      modalAt (Frame.doctrine classifier) frame.forget frame.focus frame.instantiate frame.outgoing inputs :=
  supplied_evaluation (Frame.doctrine classifier) frame.forget frame.focus
    frame.instantiate frame.outgoing inputs

theorem parameter_substitution {future : theory.closed.Obj} (incoming : future ⟶ parameter) :
    (Frame.doctrine classifier).reindex (frame.carrier ◁ incoming)
        (family (Frame.doctrine classifier) (inputs ≫ operator frame classifier)) =
      family (Frame.doctrine classifier) ((incoming ≫ inputs) ≫ operator frame classifier) := by
  rw [family_substitution, Category.assoc]

theorem guarded_elimination :
    (Frame.doctrine classifier).reindex (frame.hole ▷ parameter)
        (family (Frame.doctrine classifier) (inputs ≫ operator frame classifier)) ⊓
      family (Frame.doctrine classifier) (inputs ≫ fst _ _) ≤
    (Frame.doctrine classifier).existsAlong (frame.instantiate ▷ parameter)
      ((Frame.doctrine classifier).reindex (frame.outgoing ▷ parameter)
        (family (Frame.doctrine classifier) (inputs ≫ snd _ _))) := by
  rw [output_reading]
  exact PositionedRewritePredicateLogic.guarded_elimination (Frame.doctrine classifier).toFirstOrder
    (frame.forget ▷ parameter) (frame.focus ▷ parameter)
    (frame.instantiate ▷ parameter) (frame.hole ▷ parameter)
    (CartesianTensorPullback.tensorRight frame.square parameter) _ _

variable (assignment : parameter ⟶ frame.assignments) (assay : parameter ⟶ frame.assay)
variable (compatible : assignment ≫ frame.focus = assay ≫ frame.hole)

/-- The parameter is retained alongside the supplied complete rule instance. -/
def completeInstance : parameter ⟶ rule.parameters ⊗ parameter :=
  lift (frame.suppliedInstance assignment assay compatible) (𝟙 parameter)

@[reassoc (attr := simp)] theorem completeInstance_assignment :
    completeInstance frame assignment assay compatible ≫ (frame.forget ▷ parameter) =
      lift assignment (𝟙 parameter) := by
  apply hom_ext <;> simp [completeInstance]

@[reassoc (attr := simp)] theorem completeInstance_assay :
    completeInstance frame assignment assay compatible ≫ (frame.instantiate ▷ parameter) =
      lift assay (𝟙 parameter) := by
  apply hom_ext <;> simp [completeInstance]

theorem completeInstance_outgoing :
    completeInstance frame assignment assay compatible ≫ (frame.outgoing ▷ parameter) =
      lift (prod.lift assay (frame.step assignment assay compatible ≫ theory.target)) (𝟙 parameter) := by
  apply hom_ext
  · simp only [completeInstance, Category.assoc, whiskerRight_fst, lift_fst, lift_fst_assoc]
    apply prod.hom_ext
    · simp only [Frame.outgoing, Category.assoc, prod.lift_fst,
        Frame.suppliedInstance_assay]
    · simp only [Frame.outgoing, Category.assoc, prod.lift_snd,
        Frame.step_target]
  · simp [completeInstance]

variable (intro : (Frame.doctrine classifier).reindex (lift assignment (𝟙 parameter))
    (introPredicate (Frame.doctrine classifier).toFirstOrder (frame.forget ▷ parameter)
      (conditionAt (Frame.doctrine classifier) frame.instantiate frame.outgoing inputs)) = ⊤)
variable (rely : (Frame.doctrine classifier).reindex (lift assay (𝟙 parameter))
    (family (Frame.doctrine classifier) (inputs ≫ fst _ _)) = ⊤)

include intro rely in
/-- The postcondition is read on the actual reduct and the original parameter. -/
theorem supplied_reduct : (Frame.doctrine classifier).reindex
    (lift (prod.lift assay (frame.step assignment assay compatible ≫ theory.target)) (𝟙 parameter))
      (family (Frame.doctrine classifier) (inputs ≫ snd _ _)) = ⊤ := by
  have retained := supplied_condition (Frame.doctrine classifier).toFirstOrder
    (frame.forget ▷ parameter) (frame.instantiate ▷ parameter)
    (lift assignment (𝟙 parameter)) (lift assay (𝟙 parameter))
    (completeInstance frame assignment assay compatible)
    (completeInstance_assignment frame assignment assay compatible)
    (completeInstance_assay frame assignment assay compatible)
    (family (Frame.doctrine classifier) (inputs ≫ fst _ _))
    ((Frame.doctrine classifier).reindex (frame.outgoing ▷ parameter)
      (family (Frame.doctrine classifier) (inputs ≫ snd _ _))) intro rely
  have complete : (Frame.doctrine classifier).reindex
      (completeInstance frame assignment assay compatible ≫ (frame.outgoing ▷ parameter))
      (family (Frame.doctrine classifier) (inputs ≫ snd _ _)) = ⊤ :=
    ((Frame.doctrine classifier).reindex_comp _ _ _).trans retained
  exact completeInstance_outgoing frame assignment assay compatible ▸ complete

end Mettapedia.GSLT.Core.PositionedRewriteModalPower
