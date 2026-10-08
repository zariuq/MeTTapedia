import Mettapedia.CategoryTheory.ElementaryToposPartialMaps

/-!
# Universal domain and value of the partial-map classifier

The functional-relation construction classifies complete partial maps:
the actual domain is a classifier pullback, and its supplied value is
recovered. A competing classification with the same domain pullback and
value has the same parameter. No coproduct or Boolean complement is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPartialMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPowerObjects

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {object parameter selected : C}
variable (inclusion : selected ⟶ parameter) [Mono inclusion] (suppliedValue : selected ⟶ object)

theorem suppliedLookupCondition {context : C}
    (defined : context ⟶ definedObject classifier object) (base : context ⟶ parameter)
    (same : base ≫ classifyPartial classifier inclusion suppliedValue = defined ≫ domain classifier object) :
    (defined ≫ pullback.fst _ _) ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← same,
    Category.assoc, classifyPartial_inclusion]

def suppliedLookup {context : C}
    (defined : context ⟶ definedObject classifier object) (base : context ⟶ parameter)
    (same : base ≫ classifyPartial classifier inclusion suppliedValue = defined ≫ domain classifier object) :
    context ⟶ selected :=
  graphMember classifier inclusion suppliedValue (defined ≫ pullback.fst _ _) base
    (suppliedLookupCondition classifier inclusion suppliedValue defined base same)

@[reassoc (attr := simp)] theorem suppliedLookup_inclusion {context : C}
    (defined : context ⟶ definedObject classifier object) (base : context ⟶ parameter)
    (same : base ≫ classifyPartial classifier inclusion suppliedValue = defined ≫ domain classifier object) :
    suppliedLookup classifier inclusion suppliedValue defined base same ≫ inclusion = base :=
  graphMember_inclusion classifier inclusion suppliedValue _ _ _

@[reassoc (attr := simp)] theorem suppliedLookup_value {context : C}
    (defined : context ⟶ definedObject classifier object) (base : context ⟶ parameter)
    (same : base ≫ classifyPartial classifier inclusion suppliedValue = defined ≫ domain classifier object) :
    suppliedLookup classifier inclusion suppliedValue defined base same ≫ suppliedValue =
      defined ≫ value classifier object := by
  simpa only [suppliedLookup, value, Category.assoc] using
    graphMember_value classifier inclusion suppliedValue (defined ≫ pullback.fst _ _) base
      (suppliedLookupCondition classifier inclusion suppliedValue defined base same)

@[reassoc (attr := simp)] theorem suppliedLookup_witness {context : C}
    (defined : context ⟶ definedObject classifier object) (base : context ⟶ parameter)
    (same : base ≫ classifyPartial classifier inclusion suppliedValue = defined ≫ domain classifier object) :
    suppliedLookup classifier inclusion suppliedValue defined base same ≫
      partialWitness classifier inclusion suppliedValue = defined := by
  apply (cancel_mono (domain classifier object)).mp
  rw [Category.assoc, partialWitness_domain, ← Category.assoc,
    suppliedLookup_inclusion, same]

theorem classifyPartial_isPullback :
    IsPullback inclusion (partialWitness classifier inclusion suppliedValue)
      (classifyPartial classifier inclusion suppliedValue) (domain classifier object) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (partialWitness_domain classifier inclusion suppliedValue).symm
    (fun cone => suppliedLookup classifier inclusion suppliedValue cone.snd cone.fst cone.condition)
    ?_ ?_ ?_)
  · intro cone
    exact suppliedLookup_inclusion classifier inclusion suppliedValue _ _ _
  · intro cone
    exact suppliedLookup_witness classifier inclusion suppliedValue _ _ _
  · intro cone candidate first _second
    apply (cancel_mono inclusion).mp
    rw [first, suppliedLookup_inclusion]

omit [HasPullbacks C] [HasEqualizers C] [MonoidalClosed C] in
theorem relation_pullback {A Q Z R M : C} (relation : R ⟶ A ⊗ Q)
    (parameterMap : Z ⟶ Q) (left : M ⟶ R) (right : M ⟶ Z)
    (square : IsPullback left right (relation ≫ snd A Q) parameterMap) :
    IsPullback (lift (left ≫ relation ≫ fst A Q) right) left (A ◁ parameterMap) relation := by
  have commutes : lift (left ≫ relation ≫ fst A Q) right ≫ A ◁ parameterMap = left ≫ relation := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerLeft_fst, lift_fst]
    · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc] using square.w.symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk commutes
    (fun cone => square.lift cone.snd (cone.fst ≫ snd A Z) (by
      have second := congrArg (fun arrow => arrow ≫ snd A Q) cone.condition
      simpa only [Category.assoc, whiskerLeft_snd] using second.symm)) ?_ ?_ ?_)
  · intro cone
    apply CartesianMonoidalCategory.hom_ext
    · have first := congrArg (fun arrow => arrow ≫ fst A Q) cone.condition
      simpa only [Category.assoc, whiskerLeft_fst, comp_lift, lift_fst, square.lift_fst_assoc] using first.symm
    · simp only [comp_lift, lift_snd, square.lift_snd]
  · intro cone
    exact square.lift_fst _ _ _
  · intro cone candidate first second
    apply square.hom_ext
    · exact second.trans (square.lift_fst _ _ _).symm
    · have projection := congrArg (fun arrow => arrow ≫ snd A Z) first
      simpa only [Category.assoc, lift_snd, square.lift_snd] using projection

theorem classifyPartial_unique
    (other : parameter ⟶ partialObject classifier object)
    (otherWitness : selected ⟶ definedObject classifier object)
    (square : IsPullback inclusion otherWitness other (domain classifier object))
    (value_readout : otherWitness ≫ value classifier object = suppliedValue) :
    other = classifyPartial classifier inclusion suppliedValue := by
  have complete := square.flip.paste_horiz
    (IsPullback.of_hasPullback (relationDomain classifier object) (partialInclusion classifier object))
  have relation := relation_pullback (membership classifier object)
    (other ≫ partialInclusion classifier object) (otherWitness ≫ pullback.fst _ _) inclusion complete
  have sameGraph : lift
      ((otherWitness ≫ pullback.fst _ _) ≫ membership classifier object ≫ fst _ _) inclusion =
      partialGraph inclusion suppliedValue := by
    rw [Category.assoc]
    change lift (otherWitness ≫ value classifier object) inclusion = _
    rw [value_readout]
  rw [sameGraph] at relation
  have names := name_unique classifier (partialGraph inclusion suppliedValue)
    (other ≫ partialInclusion classifier object) (otherWitness ≫ pullback.fst _ _) relation
  apply (cancel_mono (partialInclusion classifier object)).mp
  rw [classifyPartial_inclusion]
  exact names

end Mettapedia.CategoryTheory.ElementaryToposPartialMaps
