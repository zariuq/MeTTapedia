import Mettapedia.TypeTheory.ContextualCoveredRelationClassifier
import Mettapedia.TypeTheory.HostChoiceContextualSmallMaps

/-!
# Optional full small-relation classification at a fixed bound

Small relations have small actual projection fibres. External host choice
supplies their complete future enumerations; the constructed powerclass
classifier retains every future world, arrow and related argument. Its inverse
recovers the original stable relation, and parameter substitution is natural.

The membership projection and both directions of its literal classification
pullback are actual maps. A present support predicate is not substituted for
the full future classifier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open CoveredFuturePowerFamilies CoveredFuturePowerClassifier

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (B : D ⥤ Type w) (A : D ⥤ Type v)

/-- The projection is the actual natural map from the relation subtype. -/
structure SmallRelation where
  predicate : StablePredicate (product B A)
  small : SmallFibres (ContextualCoveredRelationClassifier.parameterProjection B A predicate)

namespace SmallRelation

theorem ext (first second : SmallRelation B A)
    (same : ∀ point, first.predicate.holds point ↔ second.predicate.holds point) : first = second := by
  cases first with
  | mk first firstSmall =>
    cases second with
    | mk second secondSmall =>
      have predicates := StablePredicate.ext first second same
      cases predicates
      rfl

end SmallRelation

noncomputable def coveredRelation (relation : SmallRelation B A) : CoveredRelation B A :=
  ContextualCoveredRelationClassifier.coveredFromFuture B A relation.predicate
    (HostChoiceContextualSmallMaps.futureData_exists _ relation.small)

def smallRelation (relation : CoveredRelation B A) : SmallRelation B A where
  predicate := relation.predicate
  small := ContextualCoveredRelationClassifier.projection_smallFibres B A relation

theorem small_covered (relation : SmallRelation B A) :
    smallRelation B A (coveredRelation B A relation) = relation := by
  apply SmallRelation.ext
  intro _
  exact Iff.rfl

theorem covered_small (relation : CoveredRelation B A) :
    coveredRelation B A (smallRelation B A relation) = relation := by
  apply CoveredRelation.ext
  intro _
  exact Iff.rfl

noncomputable def relationEquiv : SmallRelation B A ≃ CoveredRelation B A where
  toFun := coveredRelation B A
  invFun := smallRelation B A
  left_inv := small_covered B A
  right_inv := covered_small B A

noncomputable def classifier (relation : SmallRelation B A) : NaturalHom B (family A) :=
  CoveredFuturePowerClassifier.classifier B A (coveredRelation B A relation)

def classifiedRelation (operation : NaturalHom B (family A)) : SmallRelation B A :=
  smallRelation B A (CoveredFuturePowerClassifier.classifiedRelation B A operation)

theorem classified_classifier (relation : SmallRelation B A) :
    classifiedRelation B A (classifier B A relation) = relation := by
  exact (congrArg (smallRelation B A)
    (CoveredFuturePowerClassifier.classified_classifier B A (coveredRelation B A relation))).trans
      (small_covered B A relation)

theorem classifier_classified (operation : NaturalHom B (family A)) :
    classifier B A (classifiedRelation B A operation) = operation := by
  exact (congrArg (CoveredFuturePowerClassifier.classifier B A)
    (covered_small B A (CoveredFuturePowerClassifier.classifiedRelation B A operation))).trans
      (CoveredFuturePowerClassifier.classifier_classified B A operation)

/-- The correspondence covers the pointwise proof-small relation class,
not just relations equipped with an authored enumeration function. -/
noncomputable def classifierEquiv : NaturalHom B (family A) ≃ SmallRelation B A where
  toFun := classifiedRelation B A
  invFun := classifier B A
  left_inv := classifier_classified B A
  right_inv := classified_classifier B A

theorem classifier_future (relation : SmallRelation B A) (point : D)
    (parameter : B.obj point) (argument : Arguments A point) :
    ((classifier B A relation).app point parameter).val.holds argument ↔
      relation.predicate.holds
        ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩ := Iff.rfl

variable {B' : D ⥤ Type z}

noncomputable def parameterSubstitution (change : NaturalHom B' B) (relation : SmallRelation B A) :
    SmallRelation B' A :=
  smallRelation B' A (CoveredFuturePowerClassifier.parameterSubstitution B A change
    (coveredRelation B A relation))

theorem classifier_parameter_substitution (change : NaturalHom B' B) (relation : SmallRelation B A) :
    classifier B' A (parameterSubstitution B A change relation) =
      change.comp (classifier B A relation) := by
  exact (congrArg (CoveredFuturePowerClassifier.classifier B' A)
    (covered_small B' A (CoveredFuturePowerClassifier.parameterSubstitution B A change
      (coveredRelation B A relation)))).trans
        (CoveredFuturePowerClassifier.classifier_parameter_substitution B A change
          (coveredRelation B A relation))

theorem classified_parameter_substitution (change : NaturalHom B' B)
    (operation : NaturalHom B (family A)) :
    classifiedRelation B' A (change.comp operation) =
      parameterSubstitution B A change (classifiedRelation B A operation) := by
  apply SmallRelation.ext
  intro _
  exact Iff.rfl

noncomputable abbrev membershipPullback (relation : SmallRelation B A) :=
  ContextualCoveredRelationClassifier.membershipPullback B A (coveredRelation B A relation)

noncomputable def membershipForward (relation : SmallRelation B A) :
    NaturalHom (ContextualCoveredRelationClassifier.total B A relation.predicate)
      (membershipPullback B A relation) :=
  ContextualCoveredRelationClassifier.membershipForward B A (coveredRelation B A relation)

noncomputable def membershipBackward (relation : SmallRelation B A) :
    NaturalHom (membershipPullback B A relation)
      (ContextualCoveredRelationClassifier.total B A relation.predicate) :=
  ContextualCoveredRelationClassifier.membershipBackward B A (coveredRelation B A relation)

theorem membership_left (relation : SmallRelation B A) (point : D)
    (receipt : (ContextualCoveredRelationClassifier.total B A relation.predicate).obj point) :
    (membershipBackward B A relation).app point ((membershipForward B A relation).app point receipt) = receipt :=
  ContextualCoveredRelationClassifier.membership_left B A (coveredRelation B A relation) point receipt

theorem membership_right (relation : SmallRelation B A) (point : D)
    (receipt : (membershipPullback B A relation).obj point) :
    (membershipForward B A relation).app point ((membershipBackward B A relation).app point receipt) = receipt :=
  ContextualCoveredRelationClassifier.membership_right B A (coveredRelation B A relation) point receipt

noncomputable def membershipSectionEquiv (relation : SmallRelation B A) :
    (ContextualCoveredRelationClassifier.total B A relation.predicate).sections ≃
      (membershipPullback B A relation).sections :=
  ContextualCoveredRelationClassifier.membershipSectionEquiv B A (coveredRelation B A relation)

section MonicRelations

variable {R : D ⥤ Type z} (inclusion : NaturalHom R (product B A))

/-- The stable image of an arbitrary authored relation inclusion. -/
def imagePredicate : StablePredicate (product B A) where
  holds point := ∃ receipt : R.obj point.1, inclusion.app point.1 receipt = point.2
  closed {first second} step available := by
    obtain ⟨receipt, same⟩ := available
    exact ⟨R.map step.1 receipt, (inclusion.naturality step.1 receipt).symm.trans
      ((congrArg ((product B A).map step.1) same).trans step.2)⟩

def imageMap : NaturalHom R (ContextualCoveredRelationClassifier.total B A (imagePredicate B A inclusion)) where
  app point receipt := ⟨inclusion.app point receipt, ⟨receipt, rfl⟩⟩
  naturality step receipt := Subtype.ext (inclusion.naturality step receipt)

theorem imageMap_surjective (point : D) : Function.Surjective ((imageMap B A inclusion).app point) := by
  intro receipt
  obtain ⟨original, same⟩ := receipt.property
  exact ⟨original, Subtype.ext same⟩

theorem imageMap_injective (injective : ∀ point, Function.Injective (inclusion.app point))
    (point : D) : Function.Injective ((imageMap B A inclusion).app point) := by
  intro first second same
  exact injective point (congrArg Subtype.val same)

theorem imageMap_projection : (imageMap B A inclusion).comp
    (ContextualCoveredRelationClassifier.parameterProjection B A (imagePredicate B A inclusion)) =
      inclusion.comp (firstProjection B A) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def imageSmallRelation (small : SmallFibres (inclusion.comp (firstProjection B A))) : SmallRelation B A where
  predicate := imagePredicate B A inclusion
  small := smallFibres_covered_quotient (inclusion.comp (firstProjection B A))
    (imageMap B A inclusion)
    (ContextualCoveredRelationClassifier.parameterProjection B A (imagePredicate B A inclusion))
    (imageMap_projection B A inclusion) (imageMap_surjective B A inclusion) small

/-- This inverse is explicitly priced by host choice. Its input is an
arbitrary monic relation, rather than a supplied inverse decoder. -/
noncomputable def imageEquiv (injective : ∀ point, Function.Injective (inclusion.app point))
    (point : D) : R.obj point ≃
      (ContextualCoveredRelationClassifier.total B A (imagePredicate B A inclusion)).obj point :=
  Equiv.ofBijective ((imageMap B A inclusion).app point)
    ⟨imageMap_injective B A inclusion injective point, imageMap_surjective B A inclusion point⟩

noncomputable def imageInverse (injective : ∀ point, Function.Injective (inclusion.app point)) :
    NaturalHom (ContextualCoveredRelationClassifier.total B A (imagePredicate B A inclusion)) R where
  app point := (imageEquiv B A inclusion injective point).symm
  naturality {first second} step receipt := by
    apply imageMap_injective B A inclusion injective second
    exact ((imageMap B A inclusion).naturality step
      ((imageEquiv B A inclusion injective first).symm receipt)).symm.trans
        ((congrArg ((ContextualCoveredRelationClassifier.total B A
          (imagePredicate B A inclusion)).map step)
            ((imageEquiv B A inclusion injective first).apply_symm_apply receipt)).trans
              ((imageEquiv B A inclusion injective second).apply_symm_apply _).symm)

noncomputable def monicMembershipForward
    (small : SmallFibres (inclusion.comp (firstProjection B A))) :
    NaturalHom R (membershipPullback B A (imageSmallRelation B A inclusion small)) :=
  (imageMap B A inclusion).comp (membershipForward B A (imageSmallRelation B A inclusion small))

noncomputable def monicMembershipBackward
    (injective : ∀ point, Function.Injective (inclusion.app point))
    (small : SmallFibres (inclusion.comp (firstProjection B A))) :
    NaturalHom (membershipPullback B A (imageSmallRelation B A inclusion small)) R :=
  (membershipBackward B A (imageSmallRelation B A inclusion small)).comp
    (imageInverse B A inclusion injective)

theorem monic_membership_left (injective : ∀ point, Function.Injective (inclusion.app point))
    (small : SmallFibres (inclusion.comp (firstProjection B A)))
    (point : D) (receipt : R.obj point) :
    (monicMembershipBackward B A inclusion injective small).app point
      ((monicMembershipForward B A inclusion small).app point receipt) = receipt := by
  exact (congrArg ((imageEquiv B A inclusion injective point).symm)
    (membership_left B A (imageSmallRelation B A inclusion small) point
      ((imageMap B A inclusion).app point receipt))).trans
        ((imageEquiv B A inclusion injective point).symm_apply_apply receipt)

theorem monic_membership_right (injective : ∀ point, Function.Injective (inclusion.app point))
    (small : SmallFibres (inclusion.comp (firstProjection B A)))
    (point : D) (receipt : (membershipPullback B A (imageSmallRelation B A inclusion small)).obj point) :
    (monicMembershipForward B A inclusion small).app point
      ((monicMembershipBackward B A inclusion injective small).app point receipt) = receipt := by
  exact (congrArg ((membershipForward B A (imageSmallRelation B A inclusion small)).app point)
    ((imageEquiv B A inclusion injective point).apply_symm_apply _)).trans
      (membership_right B A (imageSmallRelation B A inclusion small) point receipt)

noncomputable def monicMembershipSectionEquiv
    (injective : ∀ point, Function.Injective (inclusion.app point))
    (small : SmallFibres (inclusion.comp (firstProjection B A))) :
    R.sections ≃ (membershipPullback B A (imageSmallRelation B A inclusion small)).sections where
  toFun := (monicMembershipForward B A inclusion small).mapSection
  invFun := (monicMembershipBackward B A inclusion injective small).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact monic_membership_left B A inclusion injective small point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact monic_membership_right B A inclusion injective small point (term.val point)

end MonicRelations

end Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier
