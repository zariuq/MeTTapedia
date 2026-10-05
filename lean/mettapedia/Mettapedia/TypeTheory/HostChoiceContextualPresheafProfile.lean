import Mettapedia.TypeTheory.HostChoiceContextualPresheafAmbient

/-!
# A proved optional fixed-successor presheaf profile

The only parameters of this checking profile are a small site and its
category structure. The ambient objects have successor-bound values; the
small-map receipt types stay at the original bound. Each clause below is
certified by a constructed map, quotient, classifier, adjunction or covering
diagram. No closure, representability or Collection provider is supplied.

External host choice reconstructs coherent decoders for proof-small fibres
and populates the unrestricted Collection generators. Proposition-valued
subobjects and the full future power construction retain the full host
propositional powerset strength. The profile is a comparison model; it does
not select a native foundation or assert an internal choice law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualPresheafProfile

open CategoryTheory CategoryTheory.Limits ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps
open ContextualPresheafExactness HostChoiceContextualSmallMapModel
open HostChoiceContextualPresheafAmbient
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

universe u
variable (D : Type u) [Category.{u} D]

/-- These are certificates about the fixed canonical constructions, not
existence fields required from a caller. -/
structure VerifiedProfile : Prop where
  finiteLimits : HasFiniteLimits (D ⥤ Type (u + 1))
  finiteColimits : HasFiniteColimits (D ⥤ Type (u + 1))
  extensive : FinitaryExtensive (D ⥤ Type (u + 1))
  regular : Regular (D ⥤ Type (u + 1))
  subobjectClassifier : HasSubobjectClassifier (D ⥤ Type (u + 1))
  smallIdentity : (smallMaps (D := D)).ContainsIdentities
  smallComposition : (smallMaps (D := D)).IsStableUnderComposition
  smallPullback : (smallMaps (D := D)).IsStableUnderBaseChange
  smallDiagonal : ∀ A : D ⥤ Type (u + 1), SmallFibres (diagonal A)
  smallCoveredQuotient : ∀ {X A B : D ⥤ Type (u + 1)}
    (cover : NaturalHom X A) (remaining : NaturalHom A B),
    Cover cover → SmallFibres (cover.comp remaining) → SmallFibres remaining
  smallCopairing : ∀ {X Y A : D ⥤ Type (u + 1)}
    (first : NaturalHom X A) (second : NaturalHom Y A),
    SmallFibres first → SmallFibres second → SmallFibres (copairing first second)
  effectiveRelation : ∀ {A R : D ⥤ Type (u + 1)} (presentation : MonicEquivalence (A := A) R),
    @IsKernelPair (D ⥤ Type (u + 1)) _ _ _ _
      (StableEquivalence.projection A presentation.relation).toNatTrans
      presentation.left.toNatTrans presentation.right.toNatTrans
  effectiveRelationUniversal : ∀ {A R B : D ⥤ Type (u + 1)}
    (presentation : MonicEquivalence (A := A) R) (operation : NaturalHom A B),
    presentation.left.comp operation = presentation.right.comp operation →
      ∃! factor : NaturalHom (StableEquivalence.quotient A presentation.relation) B,
        (StableEquivalence.projection A presentation.relation).comp factor = operation
  monicRepresentation : ∀ {A R : D ⥤ Type (u + 1)} (inclusion : NaturalHom R A),
    (∀ point, Function.Injective (inclusion.app point)) →
      ∃ forward : NaturalHom R (subobject (monicPredicate inclusion)),
      ∃ backward : NaturalHom (subobject (monicPredicate inclusion)) R,
        forward.comp backward = ContextualSmallMapConstructions.identity R ∧
        backward.comp forward = ContextualSmallMapConstructions.identity (subobject (monicPredicate inclusion)) ∧
        forward.comp (subobjectInclusion (monicPredicate inclusion)) = inclusion
  predicateSubobjectOrder : ∀ {A : D ⥤ Type (u + 1)} (first second : StablePredicate A),
    Included first second ↔ ∃ factor : NaturalHom (subobject first) (subobject second),
      factor.comp (subobjectInclusion second) = subobjectInclusion first
  existsLeftAdjoint : ∀ {A B : D ⥤ Type (u + 1)} (operation : NaturalHom A B)
    (first : StablePredicate A) (second : StablePredicate B),
    Included (existsImage operation first) second ↔ Included first (inverseImage operation second)
  forallRightAdjoint : ∀ {A B : D ⥤ Type (u + 1)} (operation : NaturalHom A B)
    (first : StablePredicate B) (second : StablePredicate A),
    Included (inverseImage operation first) second ↔ Included first (forallImage operation second)
  frobenius : ∀ {A B : D ⥤ Type (u + 1)} (operation : NaturalHom A B)
    (first : StablePredicate A) (second : StablePredicate B),
    existsImage operation (conjunction first (inverseImage operation second)) =
      conjunction (existsImage operation first) second
  relationClassification : ∀ B A : D ⥤ Type (u + 1),
    Nonempty (NaturalHom B (Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies.family A) ≃
      HostChoiceContextualSmallMapClassifier.SmallRelation B A)
  universalSmall : SmallFibres (ContextualSmallFamilyUniverse.universalProjection (D := D))
  representation : ∀ {X A : D ⥤ Type (u + 1)} (operation : NaturalHom X A)
    (small : SmallFibres operation),
    @IsPullback (D ⥤ Type (u + 1)) _ X ContextualSmallFamilyUniverse.universalTotal A
      ContextualSmallFamilyUniverse.universeFamily
      (HostChoiceContextualSmallMapRepresentation.classified operation small).toNatTrans
      operation.toNatTrans ContextualSmallFamilyUniverse.universalProjection.toNatTrans
      (HostChoiceContextualSmallMapRepresentation.classifier operation small).toNatTrans
  representationCoverSquare : ∀ {X A : D ⥤ Type (u + 1)} (operation : NaturalHom X A),
    @IsPullback (D ⥤ Type (u + 1)) _ X X A A
      (ContextualSmallMapConstructions.identity X).toNatTrans operation.toNatTrans
      operation.toNatTrans (ContextualSmallMapConstructions.identity A).toNatTrans
  representationCover : ∀ A : D ⥤ Type (u + 1),
    Cover (ContextualSmallMapConstructions.identity A)
  naturalNumbersSmall : SmallFibres (naturalNumbersProjection (D := D))
  indexedRecursion : ∀ {P Y : D ⥤ Type (u + 1)}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y),
    ∃! operation : NaturalHom (product P naturalNumbers) Y,
      (parameterZero P).comp operation = initial ∧
        (parameterSuccessor P).comp operation = (iterationPair operation).comp step
  collection : ∀ {X A Y : D ⥤ Type (u + 1)}
    (operation : NaturalHom X A) (cover : NaturalHom Y X),
    SmallFibres operation → Cover cover →
      Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover)

/-- The fixed profile is constructed from the site alone. -/
theorem verifiedProfile : VerifiedProfile D where
  finiteLimits := ordinary_finiteLimits
  finiteColimits := ordinary_finiteColimits
  extensive := ordinary_extensive
  regular := ordinary_regular
  subobjectClassifier := ordinary_subobjectClassifier
  smallIdentity := smallMaps_identity
  smallComposition := smallMaps_composition
  smallPullback := smallMaps_pullback
  smallDiagonal := small_diagonal
  smallCoveredQuotient := small_covered_quotient
  smallCopairing := small_copairing
  effectiveRelation := monicEquivalence_isKernelPair
  effectiveRelationUniversal := fun presentation operation equalizes =>
    presentation.quotient_universal operation equalizes
  monicRepresentation := fun inclusion injective =>
    ⟨monicForward inclusion, monicBackward inclusion injective,
      monic_left inclusion injective, monic_right inclusion injective, monic_parameter inclusion⟩
  predicateSubobjectOrder := predicate_order_iff
  existsLeftAdjoint := exists_inverse_adjunction
  forallRightAdjoint := inverse_forall_adjunction
  frobenius := exists_frobenius
  relationClassification := fun B A => ⟨HostChoiceContextualSmallMapClassifier.classifierEquiv B A⟩
  universalSmall := ContextualSmallFamilyUniverse.universalProjection_smallFibres
  representation := classification_isPullback
  representationCoverSquare := representation_identity_square
  representationCover := fun _ _ value => ⟨value, rfl⟩
  naturalNumbersSmall := naturalNumbers_small
  indexedRecursion := indexed_naturalNumber_universal
  collection := HostChoiceContextualCollection.collection_in_successor_category

end Mettapedia.TypeTheory.HostChoiceContextualPresheafProfile
