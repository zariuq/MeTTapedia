import Mettapedia.CategoryTheory.ElementaryToposPredicateQuantification

/-!
# Partial maps classified by functional singleton predicates

An element of the power object is selected exactly when any two of its
members agree. Restricting the membership relation to that selection makes
its domain projection monic. The graph of any supplied partial map has a
unique selected name, and its complete domain and value are recovered.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPartialMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPowerObjects ElementaryToposPredicateQuantification

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C) (object : C)

abbrev relationDomain : membershipObject classifier object ⟶ power classifier object :=
  membership classifier object ≫ snd _ _

abbrev relationValue : membershipObject classifier object ⟶ object :=
  membership classifier object ≫ fst _ _

abbrev relationKernel : C :=
  pullback (relationDomain classifier object) (relationDomain classifier object)

abbrev firstValue : relationKernel classifier object ⟶ object :=
  pullback.fst _ _ ≫ relationValue classifier object

abbrev secondValue : relationKernel classifier object ⟶ object :=
  pullback.snd _ _ ≫ relationValue classifier object

abbrev kernelBase : relationKernel classifier object ⟶ power classifier object :=
  pullback.fst _ _ ≫ relationDomain classifier object

abbrev functionalEquality : C :=
  equalizer (firstValue classifier object) (secondValue classifier object)

abbrev functionalInclusion : functionalEquality classifier object ⟶ relationKernel classifier object :=
  equalizer.ι _ _

abbrev partialObject : C :=
  universalObject classifier (kernelBase classifier object) (functionalInclusion classifier object)

abbrev partialInclusion : partialObject classifier object ⟶ power classifier object :=
  universalInclusion classifier (kernelBase classifier object) (functionalInclusion classifier object)

abbrev definedObject : C :=
  pullback (relationDomain classifier object) (partialInclusion classifier object)

abbrev domain : definedObject classifier object ⟶ partialObject classifier object :=
  pullback.snd _ _

abbrev value : definedObject classifier object ⟶ object :=
  pullback.fst _ _ ≫ relationValue classifier object

theorem selected_members_equal {parameter : C}
    (pair : parameter ⟶ relationKernel classifier object)
    (candidate : parameter ⟶ partialObject classifier object)
    (liesOver : pair ≫ kernelBase classifier object =
      candidate ≫ partialInclusion classifier object) :
    pair ≫ firstValue classifier object = pair ≫ secondValue classifier object := by
  let witness := universalElement classifier (kernelBase classifier object)
    (functionalInclusion classifier object) pair candidate liesOver
  have recovers := universalElement_inclusion classifier (kernelBase classifier object)
    (functionalInclusion classifier object) pair candidate liesOver
  calc
    _ = (witness ≫ functionalInclusion classifier object) ≫ firstValue classifier object := by
      rw [recovers]
    _ = (witness ≫ functionalInclusion classifier object) ≫ secondValue classifier object := by
      rw [Category.assoc, equalizer.condition, ← Category.assoc]
    _ = _ := by rw [recovers]

instance domain_mono : Mono (domain classifier object) where
  right_cancellation first second same := by
    have bases : (first ≫ pullback.fst _ _) ≫ relationDomain classifier object =
        (second ≫ pullback.fst _ _) ≫ relationDomain classifier object := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, same,
        Category.assoc, ← pullback.condition, ← Category.assoc]
    let pair := pullback.lift (first ≫ pullback.fst _ _) (second ≫ pullback.fst _ _) bases
    have over : pair ≫ kernelBase classifier object =
        (first ≫ domain classifier object) ≫ partialInclusion classifier object := by
      simp only [pair, kernelBase, Category.assoc, pullback.lift_fst_assoc]
      rw [pullback.condition]
    have values := selected_members_equal classifier object pair (first ≫ domain classifier object) over
    simp only [pair, firstValue, secondValue, Category.assoc,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] at values
    have members : first ≫ pullback.fst _ _ = second ≫ pullback.fst _ _ := by
      apply (cancel_mono (membership classifier object)).mp
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [relationValue, Category.assoc] using values
      · simpa only [relationDomain, Category.assoc] using bases
    exact pullback.hom_ext members same

variable {object} {parameter selected : C}
variable (inclusion : selected ⟶ parameter) [Mono inclusion] (suppliedValue : selected ⟶ object)

abbrev partialGraph : selected ⟶ object ⊗ parameter := lift suppliedValue inclusion

instance partialGraph_mono : Mono (partialGraph inclusion suppliedValue) := by
  dsimp [partialGraph]
  infer_instance

abbrev graphName : parameter ⟶ power classifier object :=
  name classifier (partialGraph inclusion suppliedValue)

abbrev graphWitness : selected ⟶ membershipObject classifier object :=
  membershipWitness classifier (partialGraph inclusion suppliedValue)

omit [HasEqualizers C] in
@[reassoc (attr := simp)] theorem graphWitness_value :
    graphWitness classifier inclusion suppliedValue ≫ relationValue classifier object = suppliedValue := by
  change membershipWitness classifier (partialGraph inclusion suppliedValue) ≫
    (membership classifier object ≫ fst _ _) = suppliedValue
  rw [← Category.assoc, membershipWitness_membership, Category.assoc, whiskerLeft_fst]
  exact lift_fst _ _

omit [HasEqualizers C] in
@[reassoc (attr := simp)] theorem graphWitness_domain :
    graphWitness classifier inclusion suppliedValue ≫ relationDomain classifier object =
      inclusion ≫ graphName classifier inclusion suppliedValue := by
  change membershipWitness classifier (partialGraph inclusion suppliedValue) ≫
    (membership classifier object ≫ snd _ _) = _
  rw [← Category.assoc, membershipWitness_membership, Category.assoc, whiskerLeft_snd]
  exact lift_snd_assoc _ _ _

omit [HasEqualizers C] in
theorem graphMember_condition {context : C}
    (member : context ⟶ membershipObject classifier object) (base : context ⟶ parameter)
    (liesOver : member ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue) :
    lift (member ≫ relationValue classifier object) base ≫
      object ◁ graphName classifier inclusion suppliedValue =
        member ≫ membership classifier object := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerLeft_fst, lift_fst, relationValue]
  · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc, relationDomain] using liesOver.symm

def graphMember {context : C} (member : context ⟶ membershipObject classifier object)
    (base : context ⟶ parameter)
    (liesOver : member ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue) : context ⟶ selected :=
  (classifies classifier (partialGraph inclusion suppliedValue)).lift
    (lift (member ≫ relationValue classifier object) base) member
    (graphMember_condition classifier inclusion suppliedValue member base liesOver)

omit [HasEqualizers C] in
@[reassoc (attr := simp)] theorem graphMember_inclusion {context : C}
    (member : context ⟶ membershipObject classifier object) (base : context ⟶ parameter)
    (liesOver : member ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue) :
    graphMember classifier inclusion suppliedValue member base liesOver ≫ inclusion = base := by
  have readout := (classifies classifier (partialGraph inclusion suppliedValue)).lift_fst
    (lift (member ≫ relationValue classifier object) base) member
    (graphMember_condition classifier inclusion suppliedValue member base liesOver)
  have coordinate := congrArg (fun arrow => arrow ≫ snd object parameter) readout
  simpa only [graphMember, partialGraph, Category.assoc, lift_snd, lift_snd_assoc] using coordinate

omit [HasEqualizers C] in
@[reassoc (attr := simp)] theorem graphMember_value {context : C}
    (member : context ⟶ membershipObject classifier object) (base : context ⟶ parameter)
    (liesOver : member ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue) :
    graphMember classifier inclusion suppliedValue member base liesOver ≫ suppliedValue =
      member ≫ relationValue classifier object := by
  have readout := (classifies classifier (partialGraph inclusion suppliedValue)).lift_fst
    (lift (member ≫ relationValue classifier object) base) member
    (graphMember_condition classifier inclusion suppliedValue member base liesOver)
  have coordinate := congrArg (fun arrow => arrow ≫ fst object parameter) readout
  simpa only [graphMember, partialGraph, Category.assoc, lift_fst, lift_fst_assoc] using coordinate

omit [HasEqualizers C] in
@[reassoc (attr := simp)] theorem graphMember_witness {context : C}
    (member : context ⟶ membershipObject classifier object) (base : context ⟶ parameter)
    (liesOver : member ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue) :
    graphMember classifier inclusion suppliedValue member base liesOver ≫
      graphWitness classifier inclusion suppliedValue = member :=
  (classifies classifier (partialGraph inclusion suppliedValue)).lift_snd _ _ _

theorem graphName_functional : graphName classifier inclusion suppliedValue ≫
    name classifier (ElementaryToposStableEpimorphisms.graph (kernelBase classifier object)) =
      graphName classifier inclusion suppliedValue ≫ name classifier
        (functionalInclusion classifier object ≫
          ElementaryToposStableEpimorphisms.graph (kernelBase classifier object)) := by
  apply (fibre_factor_iff classifier (kernelBase classifier object)
    (functionalInclusion classifier object) (graphName classifier inclusion suppliedValue)
    (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _)).mpr
  let firstMember := pullback.fst (kernelBase classifier object)
    (graphName classifier inclusion suppliedValue) ≫ pullback.fst _ _
  let secondMember := pullback.fst (kernelBase classifier object)
    (graphName classifier inclusion suppliedValue) ≫ pullback.snd _ _
  let base := pullback.snd (kernelBase classifier object) (graphName classifier inclusion suppliedValue)
  have firstOver : firstMember ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue := by
    dsimp [firstMember, base]
    rw [Category.assoc]
    exact pullback.condition
  have secondOver : secondMember ≫ relationDomain classifier object =
      base ≫ graphName classifier inclusion suppliedValue := by
    dsimp [secondMember, base]
    rw [Category.assoc, ← pullback.condition]
    exact pullback.condition
  let firstPoint := graphMember classifier inclusion suppliedValue firstMember base firstOver
  let secondPoint := graphMember classifier inclusion suppliedValue secondMember base secondOver
  have pointsEqual : firstPoint = secondPoint := by
    apply (cancel_mono inclusion).mp
    rw [graphMember_inclusion, graphMember_inclusion]
  refine ⟨equalizer.lift (pullback.fst _ _) ?_, equalizer.lift_ι _ _⟩
  have sameValues : firstMember ≫ relationValue classifier object =
      secondMember ≫ relationValue classifier object := by
    calc
      _ = firstPoint ≫ suppliedValue := (graphMember_value classifier inclusion suppliedValue _ _ _).symm
      _ = secondPoint ≫ suppliedValue := congrArg (fun arrow => arrow ≫ suppliedValue) pointsEqual
      _ = _ := graphMember_value classifier inclusion suppliedValue _ _ _
  simpa only [firstMember, secondMember, firstValue, secondValue, Category.assoc] using sameValues

def classifyPartial : parameter ⟶ partialObject classifier object :=
  equalizer.lift (graphName classifier inclusion suppliedValue)
    (graphName_functional classifier inclusion suppliedValue)

@[reassoc (attr := simp)] theorem classifyPartial_inclusion :
    classifyPartial classifier inclusion suppliedValue ≫ partialInclusion classifier object =
      graphName classifier inclusion suppliedValue := equalizer.lift_ι _ _

def partialWitness : selected ⟶ definedObject classifier object :=
  pullback.lift (graphWitness classifier inclusion suppliedValue)
    (inclusion ≫ classifyPartial classifier inclusion suppliedValue) (by
      rw [graphWitness_domain, Category.assoc, classifyPartial_inclusion])

@[reassoc (attr := simp)] theorem partialWitness_domain :
    partialWitness classifier inclusion suppliedValue ≫ domain classifier object =
      inclusion ≫ classifyPartial classifier inclusion suppliedValue := pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem partialWitness_value :
    partialWitness classifier inclusion suppliedValue ≫ value classifier object = suppliedValue := by
  simp only [partialWitness, value, pullback.lift_fst_assoc, graphWitness_value]

end Mettapedia.CategoryTheory.ElementaryToposPartialMaps
