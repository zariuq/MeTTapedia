import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetTypes

/-!
# Retained observed continuations and literal set members

Actual observed child classes construct a small displayed continuation
family. Its map into actual set-member codes is natural and onto, with
exactly the unlabelled contextual bisimulation kernel. This map can merge
different declared child results; the continuation family retains them.

The actual child set reading constructs an argument-dependent member body.
Full future native sums, products and W apply to this retained family at
the original bound, and the whole-family classifier decodes them. No child
observation is recovered from an arbitrary literal set value or receipt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetContinuations

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualHypersetModel
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open HostChoiceContextualObservedHypersetTriangle

universe u h v w
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev relation := CoveredFuturePowerClassifier.classifiedPredicate
  (observedClasses source atoms worlds arrows atomCoding) (observedClasses source atoms worlds arrows atomCoding)
  (observedCoalgebra source atoms worlds arrows atomCoding)

def relationFamily {P : D ⥤ Type u}
    (predicate : CoveredFuturePowerClassifier.StablePredicate (CoveredFuturePowerClassifier.product P P)) :
    P.Elements ⥤ Type u where
  obj point := {child : P.obj point.1 // predicate.holds ⟨point.1, (point.2, child)⟩}
  map {first second} step := TypeCat.ofHom fun child =>
    ⟨P.map step.1 child.val, predicate.closed
      (CategoryOfElements.homMk (F := CoveredFuturePowerClassifier.product P P)
        ⟨first.1, (first.2, child.val)⟩ ⟨second.1, (second.2, P.map step.1 child.val)⟩
        step.1 (Prod.ext step.2 rfl)) child.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (P.map_id_apply point.1 child.val)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (P.map_comp_apply first.1 second.1 child.val)

abbrev family := relationFamily (relation source atoms worlds arrows atomCoding)
abbrev At (point : (observedClasses source atoms worlds arrows atomCoding).Elements) : Type u :=
  (family source atoms worlds arrows atomCoding).obj point

theorem actual_member (point : (observedClasses source atoms worlds arrows atomCoding).Elements)
    (child : At source atoms worlds arrows atomCoding point) :
    Member point.1 ((classSetReadout source atoms worlds arrows atomCoding).app point.1 child.val)
      ((classSetReadout source atoms worlds arrows atomCoding).app point.1 point.2) :=
  (setReadout_future (observedCoalgebra source atoms worlds arrows atomCoding) point.1 point.1
    (𝟙 point.1) point.2 _).mpr ⟨child.val, rfl, child.property⟩

noncomputable def valueCode (point : (observedClasses source atoms worlds arrows atomCoding).Elements)
    (child : At source atoms worlds arrows atomCoding point) :
    (memberFamilyUnder (classSetReadout source atoms worlds arrows atomCoding)).obj point :=
  (memberDecoder _).symm
    ⟨(classSetReadout source atoms worlds arrows atomCoding).app point.1 child.val,
      actual_member source atoms worlds arrows atomCoding point child⟩

theorem valueCode_value (point : (observedClasses source atoms worlds arrows atomCoding).Elements)
    (child : At source atoms worlds arrows atomCoding point) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap
      (classSetReadout source atoms worlds arrows atomCoding)).obj point)
      (valueCode source atoms worlds arrows atomCoding point child)).val =
        (classSetReadout source atoms worlds arrows atomCoding).app point.1 child.val :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

noncomputable def toMember : NatTrans (family source atoms worlds arrows atomCoding)
    (memberFamilyUnder (classSetReadout source atoms worlds arrows atomCoding)) where
  app point := TypeCat.ofHom (valueCode source atoms worlds arrows atomCoding point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro child
    apply (memberDecoder _).injective
    apply Subtype.ext
    exact (valueCode_value source atoms worlds arrows atomCoding second
      ((family source atoms worlds arrows atomCoding).map step child)).trans
        (((classSetReadout source atoms worlds arrows atomCoding).naturality step.1 child.val).symm.trans
          ((congrArg (sets.map step.1) (valueCode_value source atoms worlds arrows atomCoding first child).symm).trans
            (memberDecoder_restriction_value ((ContextualSmallFamilyUniverse.elementMap
              (classSetReadout source atoms worlds arrows atomCoding)).map step) _)))

theorem toMember_value (point : (observedClasses source atoms worlds arrows atomCoding).Elements)
    (child : At source atoms worlds arrows atomCoding point) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap
      (classSetReadout source atoms worlds arrows atomCoding)).obj point)
      ((toMember source atoms worlds arrows atomCoding).app point child)).val =
        (classSetReadout source atoms worlds arrows atomCoding).app point.1 child.val :=
  congrArg Subtype.val ((memberDecoder _).apply_symm_apply _)

theorem toMember_onto (point : (observedClasses source atoms worlds arrows atomCoding).Elements) :
    Function.Surjective ((toMember source atoms worlds arrows atomCoding).app point) := by
  intro code
  let decoded := memberDecoder ((ContextualSmallFamilyUniverse.elementMap
    (classSetReadout source atoms worlds arrows atomCoding)).obj point) code
  obtain ⟨child, reads, admitted⟩ :=
    (setReadout_future (observedCoalgebra source atoms worlds arrows atomCoding) point.1 point.1
      (𝟙 point.1) point.2 decoded.val).mp decoded.property
  refine ⟨⟨child, admitted⟩, (memberDecoder _).injective ?_⟩
  apply Subtype.ext
  exact (toMember_value source atoms worlds arrows atomCoding point ⟨child, admitted⟩).trans reads

theorem toMember_kernel (point : (observedClasses source atoms worlds arrows atomCoding).Elements)
    (left right : At source atoms worlds arrows atomCoding point) :
    (toMember source atoms worlds arrows atomCoding).app point left =
        (toMember source atoms worlds arrows atomCoding).app point right ↔
      ContextualCoalgebraBisimulation.Bisimilar (observedCoalgebra source atoms worlds arrows atomCoding)
        point.1 left.val right.val := by
  refine Iff.trans ?_ (setReadout_kernel _ point.1 left.val right.val)
  constructor
  · intro same
    exact (toMember_value source atoms worlds arrows atomCoding point left).symm.trans
      ((congrArg (fun code => (memberDecoder ((ContextualSmallFamilyUniverse.elementMap
        (classSetReadout source atoms worlds arrows atomCoding)).obj point) code).val) same).trans
          (toMember_value source atoms worlds arrows atomCoding point right))
  · intro same
    apply (memberDecoder _).injective
    apply Subtype.ext
    exact (toMember_value source atoms worlds arrows atomCoding point left).trans
      (same.trans (toMember_value source atoms worlds arrows atomCoding point right).symm)

noncomputable def bodyReading : NaturalHom (ContextualSmallFamilyUniverse.total
    (family source atoms worlds arrows atomCoding)) sets where
  app point receipt := (classSetReadout source atoms worlds arrows atomCoding).app point receipt.2.val
  naturality step receipt := (classSetReadout source atoms worlds arrows atomCoding).naturality step receipt.2.val

noncomputable def body : (family source atoms worlds arrows atomCoding).Elements ⥤ Type u :=
  ContextualSmallFamilyComprehension.indexedBody (family source atoms worlds arrows atomCoding)
    (memberFamilyUnder (bodyReading source atoms worlds arrows atomCoding))

noncomputable def sum := ContextualSmallFamilyTypeFormers.sigma
  (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding)
noncomputable def product := ContextualSmallFamilyTypeFormers.pi
  (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding)
noncomputable def trees := ContextualSmallFamilyWTypes.w
  (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding)

noncomputable def nativeHom (consumer : (observedClasses source atoms worlds arrows atomCoding).Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom (WiderPresheafDependentFunctions.over
      (family source atoms worlds arrows atomCoding) consumer) (body source atoms worlds arrows atomCoding) ≃
    WiderPresheafDependentFunctions.Hom consumer (product source atoms worlds arrows atomCoding) :=
  ContextualSmallFamilyNativeAdjunction.smallHomEquiv _ _ consumer

theorem whole_family_classifier : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (family source atoms worlds arrows atomCoding)) =
      family source atoms worlds arrows atomCoding := ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem whole_former_classifiers :
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (sum source atoms worlds arrows atomCoding)) = sum source atoms worlds arrows atomCoding ∧
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (product source atoms worlds arrows atomCoding)) = product source atoms worlds arrows atomCoding ∧
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (trees source atoms worlds arrows atomCoding)) = trees source atoms worlds arrows atomCoding :=
  ⟨ContextualSmallFamilyUniverse.decoded_classifier_eq _, ContextualSmallFamilyUniverse.decoded_classifier_eq _,
    ContextualSmallFamilyUniverse.decoded_classifier_eq _⟩

section Substitution

variable {P : D ⥤ Type v} (change : NaturalHom P (observedClasses source atoms worlds arrows atomCoding))

def familyUnder : P.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.substitutedFamily (family source atoms worlds arrows atomCoding) change

noncomputable def toMemberUnder : NatTrans (familyUnder source atoms worlds arrows atomCoding change)
    (ContextualSmallFamilyUniverse.substitutedFamily
      (memberFamilyUnder (classSetReadout source atoms worlds arrows atomCoding)) change) :=
  ContextualSmallFamilyTypeFormerCoherence.restrictNat (ContextualSmallFamilyUniverse.elementMap change)
    (toMember source atoms worlds arrows atomCoding)

theorem toMemberUnder_onto (point : P.Elements) :
    Function.Surjective ((toMemberUnder source atoms worlds arrows atomCoding change).app point) :=
  toMember_onto source atoms worlds arrows atomCoding ((ContextualSmallFamilyUniverse.elementMap change).obj point)

theorem member_reindex_triangle : memberFamilyUnder (change.comp (classSetReadout source atoms worlds arrows atomCoding)) =
    ContextualSmallFamilyUniverse.substitutedFamily
      (memberFamilyUnder (classSetReadout source atoms worlds arrows atomCoding)) change :=
  HostChoiceContextualHypersetFamilyClosure.member_formation_substitution _ _

noncomputable def bodyReadingUnder : NaturalHom (ContextualSmallFamilyUniverse.total
    (familyUnder source atoms worlds arrows atomCoding change)) sets :=
  (ContextualSmallFamilyComprehension.totalChange (family source atoms worlds arrows atomCoding) change).comp
    (bodyReading source atoms worlds arrows atomCoding)

noncomputable def freshBody : (familyUnder source atoms worlds arrows atomCoding change).Elements ⥤ Type u :=
  ContextualSmallFamilyComprehension.indexedBody (familyUnder source atoms worlds arrows atomCoding change)
    (memberFamilyUnder (bodyReadingUnder source atoms worlds arrows atomCoding change))

theorem freshBody_eq : freshBody source atoms worlds arrows atomCoding change =
    ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (family source atoms worlds arrows atomCoding)
      (body source atoms worlds arrows atomCoding) := by
  have members := HostChoiceContextualHypersetFamilyClosure.member_formation_substitution
    (bodyReading source atoms worlds arrows atomCoding)
    (ContextualSmallFamilyComprehension.totalChange (family source atoms worlds arrows atomCoding) change)
  unfold freshBody
  rw [show memberFamilyUnder (bodyReadingUnder source atoms worlds arrows atomCoding change) =
    ContextualSmallFamilyUniverse.substitutedFamily (memberFamilyUnder (bodyReading source atoms worlds arrows atomCoding))
      (ContextualSmallFamilyComprehension.totalChange (family source atoms worlds arrows atomCoding) change) from members]
  exact ContextualSmallFamilyComprehension.indexedBody_substitution _ _ _

theorem sum_substitution : ContextualSmallFamilyTypeFormers.sigma
    (familyUnder source atoms worlds arrows atomCoding change) (freshBody source atoms worlds arrows atomCoding change) =
      ContextualSmallFamilyUniverse.substitutedFamily (sum source atoms worlds arrows atomCoding) change := by
  rw [freshBody_eq]
  exact ContextualSmallFamilyTypeFormerCoherence.sigma_substitution _ _ _

theorem trees_substitution : ContextualSmallFamilyUniverse.substitutedFamily (trees source atoms worlds arrows atomCoding) change =
    ContextualSmallFamilyWTypes.w (familyUnder source atoms worlds arrows atomCoding change)
      (freshBody source atoms worlds arrows atomCoding change) := by
  rw [freshBody_eq]
  exact ContextualSmallFamilyWSubstitutionCoherence.w_substitution_eq _ _ _

noncomputable def freshProduct : P.Elements ⥤ Type u := ContextualSmallFamilyTypeFormers.pi
  (familyUnder source atoms worlds arrows atomCoding change) (freshBody source atoms worlds arrows atomCoding change)

theorem freshProduct_eq : freshProduct source atoms worlds arrows atomCoding change =
    ContextualSmallFamilyTypeFormers.pi (familyUnder source atoms worlds arrows atomCoding change)
      (ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (family source atoms worlds arrows atomCoding)
        (body source atoms worlds arrows atomCoding)) :=
  congrArg (ContextualSmallFamilyTypeFormers.pi (familyUnder source atoms worlds arrows atomCoding change))
    (freshBody_eq source atoms worlds arrows atomCoding change)

noncomputable def productComparison : NatTrans
    (ContextualSmallFamilyUniverse.substitutedFamily (product source atoms worlds arrows atomCoding) change)
    (freshProduct source atoms worlds arrows atomCoding change) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution change (family source atoms worlds arrows atomCoding)
      (body source atoms worlds arrows atomCoding))
    (HostChoiceContextualHypersetFamilyClosure.familyEqHom (freshProduct_eq source atoms worlds arrows atomCoding change).symm)

noncomputable def productInverse : NatTrans (freshProduct source atoms worlds arrows atomCoding change)
    (ContextualSmallFamilyUniverse.substitutedFamily (product source atoms worlds arrows atomCoding) change) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (HostChoiceContextualHypersetFamilyClosure.familyEqHom (freshProduct_eq source atoms worlds arrows atomCoding change))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change (family source atoms worlds arrows atomCoding)
      (body source atoms worlds arrows atomCoding))

theorem productComparison_left : ContextualSmallFamilyTypeFormers.composeNat
    (productComparison source atoms worlds arrows atomCoding change) (productInverse source atoms worlds arrows atomCoding change) =
      ContextualSmallFamilyTypeFormers.identityNat
        (ContextualSmallFamilyUniverse.substitutedFamily (product source atoms worlds arrows atomCoding) change) :=
  HostChoiceContextualHypersetFamilyClosure.inverseAfterFamilyEquality
    (freshProduct_eq source atoms worlds arrows atomCoding change) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_left change
      (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding))

theorem productComparison_right : ContextualSmallFamilyTypeFormers.composeNat
    (productInverse source atoms worlds arrows atomCoding change) (productComparison source atoms worlds arrows atomCoding change) =
      ContextualSmallFamilyTypeFormers.identityNat (freshProduct source atoms worlds arrows atomCoding change) :=
  HostChoiceContextualHypersetFamilyClosure.equalityAfterInverse
    (freshProduct_eq source atoms worlds arrows atomCoding change) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_right change
      (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding))

noncomputable def productSections :
    (ContextualSmallFamilyUniverse.substitutedFamily (product source atoms worlds arrows atomCoding) change).sections ≃
      (freshProduct source atoms worlds arrows atomCoding change).sections :=
  (ContextualSmallFamilyTypeFormerCoherence.productSectionComparison change
    (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding)).trans
    (ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : P.Elements ⥤ Type u => (family.sections : Type (max u v)))
        (freshProduct_eq source atoms worlds arrows atomCoding change).symm))

theorem piBodyEquality_value {base : D ⥤ Type v} (domain : base.Elements ⥤ Type u)
    {first second : domain.Elements ⥤ Type u} (same : first = second) (point : base.Elements)
    (term : (ContextualSmallFamilyTypeFormers.pi domain first).obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain point).Elements) :
    HEq (((HostChoiceContextualHypersetFamilyClosure.familyEqHom
      (congrArg (ContextualSmallFamilyTypeFormers.pi domain) same)).app point term).val argument)
      (term.val argument) := by
  cases same
  rfl

set_option maxHeartbeats 1000000 in
theorem productComparison_value (point : P.Elements)
    (term : (ContextualSmallFamilyUniverse.substitutedFamily (product source atoms worlds arrows atomCoding) change).obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain
      (familyUnder source atoms worlds arrows atomCoding change) point).Elements) :
    HEq (((productComparison source atoms worlds arrows atomCoding change).app point term).val argument)
      (term.val ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange change
        (family source atoms worlds arrows atomCoding) point).obj argument)) :=
  (piBodyEquality_value (familyUnder source atoms worlds arrows atomCoding change)
    (freshBody_eq source atoms worlds arrows atomCoding change).symm point
    ((ContextualSmallFamilyTypeFormerCoherence.piSubstitution change
      (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding)).app point term) argument).trans
    (ContextualSmallFamilyTypeFormerCoherence.productComparison_value change
      (family source atoms worlds arrows atomCoding) (body source atoms worlds arrows atomCoding) point term argument)

theorem classifier_substitution : ContextualSmallFamilyUniverse.classifier
    (familyUnder source atoms worlds arrows atomCoding change) =
      change.comp (ContextualSmallFamilyUniverse.classifier (family source atoms worlds arrows atomCoding)) :=
  ContextualSmallFamilyUniverse.classifier_parameter_substitution _ _

theorem familyUnder_identity : familyUnder source atoms worlds arrows atomCoding
    (ContextualSmallMapConstructions.identity (observedClasses source atoms worlds arrows atomCoding)) =
      family source atoms worlds arrows atomCoding := ContextualSmallFamilyUniverse.substitutedFamily_id _

theorem familyUnder_composition {R : D ⥤ Type w} (earlier : NaturalHom R P) :
    ContextualSmallFamilyUniverse.substitutedFamily (familyUnder source atoms worlds arrows atomCoding change) earlier =
      familyUnder source atoms worlds arrows atomCoding (earlier.comp change) :=
  ContextualSmallFamilyUniverse.substitutedFamily_comp _ _ _

end Substitution

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetContinuations
