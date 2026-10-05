import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassification
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes

/-!
# Constructed classification of interpreted contextual material maps

An interpreted family supplies an actual small decoded term type and its
material dictionary at every point. A typed subset of that term type
therefore enumerates each fibre of any authored natural material map,
including maps into wider parameter functors. Evaluating this construction
at every actual future produces the whole future receipt data.

The bounded material receipt decoder constructs a coherent small family,
and the identity-future universe classifies it with genuine inverse
pullback comparisons. The future-data cover also becomes unconditional for
this interpreted class. Its factory is natural under parameter substitution
and retains the full authored member restrictions.

The construction applies to the actual dictionaries built by the generated
Pi, Sigma, identity and W operations. It does not select original-bound
dictionaries for arbitrary bare carrier functions into the hyperset
quotient, and it does not establish Collection for arbitrary wider covers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassification

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open CoveredFuturePowerFunctor

universe u v w z
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)

/-- Forgetting the dictionaries retains their actual material carriers and
the member restrictions constructed by decoding and re-encoding. -/
def dictionaryBare : BareContextualFamilies.Family.{u, u} context where
  carrier point := (domain.model point).carrier
  restrict := domain.memberRestriction
  restrict_id point member := domain.members.map_id_apply point member
  restrict_comp first second member := domain.members.map_comp_apply first second member

def encode : NaturalHom domain.family (dictionaryBare domain).source where
  app point := (domain.model point).decode.symm
  naturality arrow term := domain.memberRestriction_encode arrow term

def decode : NaturalHom (dictionaryBare domain).source domain.family where
  app point := (domain.model point).decode
  naturality arrow member := (domain.memberRestriction_decode arrow member).symm

theorem decode_encode : (encode domain).comp (decode domain) = identityHom domain.family := by
  apply NaturalHom.ext
  intro point term
  exact (domain.model point).decode.apply_symm_apply term

theorem encode_decode : (decode domain).comp (encode domain) =
    identityHom (dictionaryBare domain).source := by
  apply NaturalHom.ext
  intro point member
  exact (domain.model point).decode.symm_apply_apply member

theorem encode_value (point : context.base.Elements) (term : domain.family.obj point) :
    ((encode domain).app point term).val = (domain.model point).value term := rfl

theorem decode_value (point : context.base.Elements)
    (member : (dictionaryBare domain).source.obj point) :
    (domain.model point).value ((decode domain).app point member) = member.val :=
  (domain.model point).value_decode member

def memberSectionEquiv : domain.family.sections ≃ (dictionaryBare domain).source.sections where
  toFun := (encode domain).mapSection
  invFun := (decode domain).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (domain.model point).decode.apply_symm_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (domain.model point).decode.symm_apply_apply (term.val point)

variable {B : context.base.Elements ⥤ Type v}
variable (operation : NaturalHom (dictionaryBare domain).source B)

/-- The receipts are literal decoded terms satisfying the map's fibre
equation. Their universe is the original material graph bound. -/
def fibreEnumeration (point : context.base.Elements) (parameter : B.obj point) :
    Enumeration.{u, u + 1} (Fibre operation point parameter) where
  Carrier := {term : domain.family.obj point // operation.app point ((encode domain).app point term) = parameter}
  value term := ⟨(encode domain).app point term.val, term.property⟩
  covered member := by
    refine ⟨⟨(decode domain).app point member.val, ?_⟩, ?_⟩
    · exact (congrArg (operation.app point) ((domain.model point).decode.symm_apply_apply member.val)).trans
        member.property
    · exact Subtype.ext ((domain.model point).decode.symm_apply_apply member.val)

theorem fibreEnumeration_value (point : context.base.Elements) (parameter : B.obj point)
    (receipt : (fibreEnumeration domain operation point parameter).Carrier) :
    ((fibreEnumeration domain operation point parameter).value receipt).val.val =
      (domain.model point).value receipt.val := rfl

/-- Every actual future is used, including its retained arrow and the
transported parameter. No family is extracted from pointwise nonemptiness. -/
def futureEnumerations (point : context.base.Elements) (parameter : B.obj point) :
    ContextualEnumerationCovers.FutureEnumerations operation point parameter :=
  fun future => fibreEnumeration domain operation future.1 (B.map future.2 parameter)

theorem future_covered (point : context.base.Elements) (parameter : B.obj point) :
    Nonempty (ContextualEnumerationCovers.FutureEnumerations operation point parameter) :=
  ⟨futureEnumerations domain operation point parameter⟩

theorem smallFibres : SmallFibres operation :=
  fun point parameter => ⟨fibreEnumeration domain operation point parameter⟩

/-! ## Arbitrary wider parameter substitution -/

variable {F : context.base.Elements ⥤ Type w} (change : NaturalHom F B)

def substitutedEnumeration (point : context.base.Elements) (parameter : F.obj point) :
    Enumeration.{u, u + 1} (Fibre operation point (change.app point parameter)) :=
  fibreEnumeration domain operation point (change.app point parameter)

def smallFamily : F.Elements ⥤ Type u :=
  ContextualMaterialSmallMapClassification.smallFamily (dictionaryBare domain) operation change
    (substitutedEnumeration domain operation change)

def classifier : NaturalHom F ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (smallFamily domain operation change)

theorem decoded_classifier : ContextualSmallFamilyUniverse.decodedFamily
    (classifier domain operation change) = smallFamily domain operation change :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq (smallFamily domain operation change)

def representedForward : NaturalHom (ContextualSmallFamilyUniverse.total (smallFamily domain operation change))
    (pullback operation change) :=
  ContextualMaterialSmallMapClassification.representedForward (dictionaryBare domain) operation change
    (substitutedEnumeration domain operation change)

def representedBackward : NaturalHom (pullback operation change)
    (ContextualSmallFamilyUniverse.total (smallFamily domain operation change)) :=
  ContextualMaterialSmallMapClassification.representedBackward (dictionaryBare domain) operation change
    (substitutedEnumeration domain operation change)

theorem representedForward_inverse :
    (representedForward domain operation change).comp (representedBackward domain operation change) =
      identityHom (ContextualSmallFamilyUniverse.total (smallFamily domain operation change)) :=
  ContextualMaterialSmallMapClassification.represented_backward_forward_hom (dictionaryBare domain)
    operation change (substitutedEnumeration domain operation change)

theorem representedBackward_inverse :
    (representedBackward domain operation change).comp (representedForward domain operation change) =
      identityHom (pullback operation change) :=
  ContextualMaterialSmallMapClassification.represented_forward_backward_hom (dictionaryBare domain)
    operation change (substitutedEnumeration domain operation change)

def representedSectionEquiv : (ContextualSmallFamilyUniverse.total (smallFamily domain operation change)).sections ≃
    (pullback operation change).sections :=
  ContextualMaterialSmallMapClassification.representedSectionEquiv (dictionaryBare domain) operation change
    (substitutedEnumeration domain operation change)

theorem represented_pullback_universal {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R (dictionaryBare domain).source) (right : NaturalHom R F)
    (square : left.comp operation = right.comp change) :
    ∃! lift : NaturalHom R (ContextualSmallFamilyUniverse.total (smallFamily domain operation change)),
      lift.comp (ContextualMaterialSmallMapClassification.representedSource (dictionaryBare domain)
        operation change (substitutedEnumeration domain operation change)) = left ∧
      lift.comp (ContextualSmallFamilyUniverse.projection (smallFamily domain operation change)) = right :=
  ContextualMaterialSmallMapClassification.represented_pullback_universal (dictionaryBare domain)
    operation change (substitutedEnumeration domain operation change) left right square

section ParameterSubstitution

variable {G : context.base.Elements ⥤ Type z} (earlier : NaturalHom G F)

theorem smallFamily_parameter_substitution :
    smallFamily domain operation (earlier.comp change) =
      ContextualSmallFamilyUniverse.substitutedFamily (smallFamily domain operation change) earlier :=
  ContextualMaterialSmallMapClassification.smallFamily_parameter_substitution (dictionaryBare domain)
    operation change (substitutedEnumeration domain operation change) earlier

theorem classifier_parameter_substitution :
    classifier domain operation (earlier.comp change) = earlier.comp (classifier domain operation change) := by
  unfold classifier
  rw [smallFamily_parameter_substitution]
  exact ContextualSmallFamilyUniverse.classifier_parameter_substitution
    (smallFamily domain operation change) earlier

end ParameterSubstitution

/-- The literal parameter pullback receives its own actual whole-future
small receipt factory, retaining the original argument and parameter. -/
def pullbackFutureEnumerations (point : context.base.Elements) (parameter : F.obj point) :
    ContextualEnumerationCovers.FutureEnumerations (pullbackSecond operation change) point parameter :=
  fun future => pullbackFibreEnumeration operation change future.1 (F.map future.2 parameter)
    (fibreEnumeration domain operation future.1 (change.app future.1 (F.map future.2 parameter)))

theorem pullback_future_covered (point : context.base.Elements) (parameter : F.obj point) :
    Nonempty (ContextualEnumerationCovers.FutureEnumerations (pullbackSecond operation change) point parameter) :=
  ⟨pullbackFutureEnumerations domain operation change point parameter⟩

/-- Substitution changes only the fibre equation on the same decoded
term. Both directions retain that term and its complete material value. -/
def futureReceiptEquiv (point : context.base.Elements) (parameter : F.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point) :
    ((futureEnumerations domain operation point (change.app point parameter)) future).Carrier ≃
      ((pullbackFutureEnumerations domain operation change point parameter) future).Carrier where
  toFun term := ⟨term.val, term.property.trans (change.naturality future.2 parameter)⟩
  invFun term := ⟨term.val, term.property.trans (change.naturality future.2 parameter).symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem futureReceiptEquiv_value (point : context.base.Elements) (parameter : F.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point)
    (receipt : ((futureEnumerations domain operation point (change.app point parameter)) future).Carrier) :
    (((pullbackFutureEnumerations domain operation change point parameter) future).value
      (futureReceiptEquiv domain operation change point parameter future receipt)).val.val.1.val =
        (((futureEnumerations domain operation point (change.app point parameter)) future).value receipt).val.val := rfl

theorem futureReceiptEquiv_parameter (point : context.base.Elements) (parameter : F.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point)
    (receipt : ((futureEnumerations domain operation point (change.app point parameter)) future).Carrier) :
    (((pullbackFutureEnumerations domain operation change point parameter) future).value
      (futureReceiptEquiv domain operation change point parameter future receipt)).val.val.2 =
        F.map future.2 parameter := rfl

def fibrePowerClassifier : NaturalHom B (CoveredFuturePowerFamilies.family (dictionaryBare domain).source) :=
  ContextualEnumerationCovers.fibreClassifier operation (future_covered domain operation)

def pulledFibrePowerClassifier : NaturalHom F
    (CoveredFuturePowerFamilies.family (pullback operation change)) :=
  ContextualEnumerationCovers.fibreClassifier (pullbackSecond operation change)
    (pullback_future_covered domain operation change)

/-- The entire future relation, rather than only its current support,
commutes with parameter substitution under the actual argument projection. -/
theorem fibrePower_parameter_substitution :
    (pulledFibrePowerClassifier domain operation change).comp
      (CoveredFuturePowerFunctor.imageHom (pullbackFirst operation change)) =
        change.comp (fibrePowerClassifier domain operation) := by
  apply NaturalHom.ext
  intro point parameter
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, argument⟩
  change (∃ receipt : (pullback operation change).obj future.1,
    receipt.val.1 = argument ∧ receipt.val.2 = F.map future.2 parameter) ↔
      operation.app future.1 argument = B.map future.2 (change.app point parameter)
  constructor
  · rintro ⟨receipt, sameArgument, sameParameter⟩
    exact (congrArg (operation.app future.1) sameArgument).symm.trans
      (receipt.property.trans ((congrArg (change.app future.1) sameParameter).trans
        (change.naturality future.2 parameter).symm))
  · intro belongs
    exact ⟨⟨(argument, F.map future.2 parameter),
      belongs.trans (change.naturality future.2 parameter)⟩, rfl, rfl⟩

/-! ## Classification of the original map without a parameter cover -/

def mapSmallFamily : B.Elements ⥤ Type u :=
  smallFamily domain operation (identityHom B)

def mapClassifier : NaturalHom B ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (mapSmallFamily domain operation)

theorem smallFamily_as_substitution : smallFamily domain operation change =
    ContextualSmallFamilyUniverse.substitutedFamily (mapSmallFamily domain operation) change :=
  smallFamily_parameter_substitution domain operation (identityHom B) change

theorem classifier_as_substitution : classifier domain operation change =
    change.comp (mapClassifier domain operation) :=
  classifier_parameter_substitution domain operation (identityHom B) change

theorem classifier_substitution_comp {G : context.base.Elements ⥤ Type z} (earlier : NaturalHom G F) :
    classifier domain operation (earlier.comp change) =
      earlier.comp (change.comp (mapClassifier domain operation)) := by
  rw [classifier_parameter_substitution, classifier_as_substitution]

abbrev mapTotal := ContextualSmallFamilyUniverse.total (mapSmallFamily domain operation)

def mapForward : NaturalHom (mapTotal domain operation) (dictionaryBare domain).source :=
  (representedForward domain operation (identityHom B)).comp (pullbackFirst operation (identityHom B))

def mapBackward : NaturalHom (dictionaryBare domain).source (mapTotal domain operation) :=
  (pullbackPair operation (identityHom B) (identityHom (dictionaryBare domain).source) operation rfl).comp
    (representedBackward domain operation (identityHom B))

theorem mapForward_inverse : (mapForward domain operation).comp (mapBackward domain operation) =
    identityHom (mapTotal domain operation) := by
  apply NaturalHom.ext
  intro point receipt
  let pair := (representedForward domain operation (identityHom B)).app point receipt
  have back : (⟨(pair.val.1, operation.app point pair.val.1), rfl⟩ :
      (pullback operation (identityHom B)).obj point) = pair :=
    Subtype.ext (Prod.ext rfl pair.property)
  change (representedBackward domain operation (identityHom B)).app point
    ⟨(pair.val.1, operation.app point pair.val.1), rfl⟩ = receipt
  rw [back]
  exact ContextualMaterialSmallMapClassification.represented_backward_forward
    (dictionaryBare domain) operation (identityHom B)
    (substitutedEnumeration domain operation (identityHom B)) point receipt

theorem mapBackward_inverse : (mapBackward domain operation).comp (mapForward domain operation) =
    identityHom (dictionaryBare domain).source := by
  apply NaturalHom.ext
  intro point member
  exact congrArg (fun pair : (pullback operation (identityHom B)).obj point => pair.val.1)
    (ContextualMaterialSmallMapClassification.represented_forward_backward
      (dictionaryBare domain) operation (identityHom B)
      (substitutedEnumeration domain operation (identityHom B)) point ⟨(member, operation.app point member), rfl⟩)

theorem mapForward_parameter : (mapForward domain operation).comp operation =
    ContextualSmallFamilyUniverse.projection (mapSmallFamily domain operation) := by
  apply NaturalHom.ext
  intro point receipt
  exact ((representedForward domain operation (identityHom B)).app point receipt).property

theorem mapBackward_parameter : (mapBackward domain operation).comp
    (ContextualSmallFamilyUniverse.projection (mapSmallFamily domain operation)) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

def mapSectionEquiv : (mapTotal domain operation).sections ≃ (dictionaryBare domain).source.sections where
  toFun := (mapForward domain operation).mapSection
  invFun := (mapBackward domain operation).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun map : NaturalHom (mapTotal domain operation) (mapTotal domain operation) =>
      map.app point (term.val point)) (mapForward_inverse domain operation)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact congrArg (fun map : NaturalHom (dictionaryBare domain).source (dictionaryBare domain).source =>
      map.app point (term.val point)) (mapBackward_inverse domain operation)

/-- Whole typed continuations are recovered after small-code
classification, not merely their current support or material carrier. -/
def termClassificationEquiv : (mapTotal domain operation).sections ≃ domain.family.sections :=
  (mapSectionEquiv domain operation).trans (memberSectionEquiv domain).symm

theorem termClassificationEquiv_value (sectionTerm : (mapTotal domain operation).sections)
    (point : context.base.Elements) :
    (domain.model point).value ((termClassificationEquiv domain operation sectionTerm).val point) =
      ((mapForward domain operation).app point (sectionTerm.val point)).val :=
  (domain.model point).value_decode _

def mapUniversal : NaturalHom (dictionaryBare domain).source ContextualSmallFamilyUniverse.universalTotal :=
  (mapBackward domain operation).comp (ContextualSmallFamilyUniverse.classified (mapSmallFamily domain operation))

theorem mapUniversal_square : (mapUniversal domain operation).comp ContextualSmallFamilyUniverse.universalProjection =
    operation.comp (mapClassifier domain operation) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def mapUniversalForward : NaturalHom (dictionaryBare domain).source
    (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) :=
  (mapBackward domain operation).comp
    (ContextualSmallFamilyUniverse.classificationForward (mapSmallFamily domain operation))

def mapUniversalBackward : NaturalHom
    (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation))
    (dictionaryBare domain).source :=
  (ContextualSmallFamilyUniverse.classificationBackward (mapSmallFamily domain operation)).comp
    (mapForward domain operation)

theorem mapUniversalForward_inverse : (mapUniversalForward domain operation).comp
    (mapUniversalBackward domain operation) = identityHom (dictionaryBare domain).source := by
  apply NaturalHom.ext
  intro point member
  have same := ContextualSmallFamilyUniverse.classification_left (mapSmallFamily domain operation) point
    ((mapBackward domain operation).app point member)
  exact (congrArg ((mapForward domain operation).app point) same).trans
    (congrArg (fun map : NaturalHom (dictionaryBare domain).source (dictionaryBare domain).source =>
      map.app point member) (mapBackward_inverse domain operation))

theorem mapUniversalBackward_inverse : (mapUniversalBackward domain operation).comp
    (mapUniversalForward domain operation) =
      identityHom (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) := by
  apply NaturalHom.ext
  intro point pair
  have same := congrArg (fun map : NaturalHom (mapTotal domain operation) (mapTotal domain operation) =>
      map.app point ((ContextualSmallFamilyUniverse.classificationBackward
        (mapSmallFamily domain operation)).app point pair)) (mapForward_inverse domain operation)
  exact (congrArg ((ContextualSmallFamilyUniverse.classificationForward (mapSmallFamily domain operation)).app point) same).trans
    (ContextualSmallFamilyUniverse.classification_right (mapSmallFamily domain operation) point pair)

theorem mapUniversalForward_source : (mapUniversalForward domain operation).comp
    (pullbackFirst ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) =
      mapUniversal domain operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem mapUniversalForward_parameter : (mapUniversalForward domain operation).comp
    (pullbackSecond ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

def mapUniversalLift {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal) (right : NaturalHom R B)
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection = right.comp (mapClassifier domain operation)) :
    NaturalHom R (dictionaryBare domain).source :=
  (pullbackPair ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)
    left right square).comp (mapUniversalBackward domain operation)

theorem mapUniversalLift_source {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal) (right : NaturalHom R B)
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection = right.comp (mapClassifier domain operation)) :
    (mapUniversalLift domain operation left right square).comp (mapUniversal domain operation) = left := by
  apply NaturalHom.ext
  intro point value
  exact congrArg (fun pair : (pullback ContextualSmallFamilyUniverse.universalProjection
      (mapClassifier domain operation)).obj point => pair.val.1)
    (congrArg (fun map : NaturalHom
        (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation))
        (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) =>
      map.app point ((pullbackPair ContextualSmallFamilyUniverse.universalProjection
        (mapClassifier domain operation) left right square).app point value))
      (mapUniversalBackward_inverse domain operation))

theorem mapUniversalLift_parameter {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal) (right : NaturalHom R B)
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection = right.comp (mapClassifier domain operation)) :
    (mapUniversalLift domain operation left right square).comp operation = right := by
  apply NaturalHom.ext
  intro point value
  exact congrArg (fun pair : (pullback ContextualSmallFamilyUniverse.universalProjection
      (mapClassifier domain operation)).obj point => pair.val.2)
    (congrArg (fun map : NaturalHom
        (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation))
        (pullback ContextualSmallFamilyUniverse.universalProjection (mapClassifier domain operation)) =>
      map.app point ((pullbackPair ContextualSmallFamilyUniverse.universalProjection
        (mapClassifier domain operation) left right square).app point value))
      (mapUniversalBackward_inverse domain operation))

theorem mapUniversalLift_unique {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal) (right : NaturalHom R B)
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection = right.comp (mapClassifier domain operation))
    (candidate : NaturalHom R (dictionaryBare domain).source)
    (leftLaw : candidate.comp (mapUniversal domain operation) = left) (rightLaw : candidate.comp operation = right) :
    candidate = mapUniversalLift domain operation left right square := by
  apply NaturalHom.ext
  intro point value
  have pairSame : (mapUniversalForward domain operation).app point (candidate.app point value) =
      (mapUniversalForward domain operation).app point ((mapUniversalLift domain operation left right square).app point value) := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal =>
        map.app point value) leftLaw).trans
        (congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal =>
          map.app point value) (mapUniversalLift_source domain operation left right square)).symm
    · exact (congrArg (fun map : NaturalHom R B => map.app point value) rightLaw).trans
        (congrArg (fun map : NaturalHom R B => map.app point value)
          (mapUniversalLift_parameter domain operation left right square)).symm
  have inverse (member : (dictionaryBare domain).source.obj point) :
      (mapUniversalBackward domain operation).app point ((mapUniversalForward domain operation).app point member) = member :=
    congrArg (fun map : NaturalHom (dictionaryBare domain).source (dictionaryBare domain).source =>
      map.app point member) (mapUniversalForward_inverse domain operation)
  exact (inverse (candidate.app point value)).symm.trans
    ((congrArg ((mapUniversalBackward domain operation).app point) pairSame).trans (inverse _))

/-- The original material map is a literal pullback of the constructed
universal map, with an actual unique lift for every wider source. -/
theorem map_pullback_universal {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal) (right : NaturalHom R B)
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection = right.comp (mapClassifier domain operation)) :
    ∃! lift : NaturalHom R (dictionaryBare domain).source,
      lift.comp (mapUniversal domain operation) = left ∧ lift.comp operation = right :=
  ⟨mapUniversalLift domain operation left right square,
    ⟨mapUniversalLift_source domain operation left right square, mapUniversalLift_parameter domain operation left right square⟩,
    fun candidate laws => mapUniversalLift_unique domain operation left right square candidate laws.1 laws.2⟩

section ContextSubstitution

variable {other : LabelledContext C} (baseChange : NatTrans other.base context.base)

theorem dictionaryBare_reindex : dictionaryBare (domain.reindex baseChange) =
    (dictionaryBare domain).reindex baseChange := rfl

def reindexedOperation : NaturalHom (dictionaryBare (domain.reindex baseChange)).source
    (ContextualImageFactorization.restrict (PowerClassPresheafProducts.elementMap baseChange) B) where
  app point := operation.app ((PowerClassPresheafProducts.elementMap baseChange).obj point)
  naturality arrow member := operation.naturality ((PowerClassPresheafProducts.elementMap baseChange).map arrow) member

theorem reindexedEnumeration (point : other.base.Elements)
    (parameter : B.obj ((PowerClassPresheafProducts.elementMap baseChange).obj point)) :
    fibreEnumeration (domain.reindex baseChange) (reindexedOperation domain operation baseChange) point parameter =
      fibreEnumeration domain operation ((PowerClassPresheafProducts.elementMap baseChange).obj point) parameter := rfl

end ContextSubstitution

/-! ## The concrete two-pullback future-cover classification -/

theorem future_parameters_cover (point : context.base.Elements) :
    Function.Surjective ((ContextualMaterialSmallMapClassification.futureChange
      (dictionaryBare domain) operation).app point) :=
  ContextualMaterialSmallMapClassification.future_parameters_cover (dictionaryBare domain) operation
    (future_covered domain operation) point

theorem future_top_cover (point : context.base.Elements) :
    Function.Surjective ((ContextualMaterialSmallMapClassification.futureTop
      (dictionaryBare domain) operation).app point) :=
  ContextualMaterialSmallMapClassification.future_top_cover (dictionaryBare domain) operation
    (future_covered domain operation) point

theorem two_pullbacks :
    ((ContextualMaterialSmallMapClassification.futureForward (dictionaryBare domain) operation).comp
      (ContextualMaterialSmallMapClassification.futureBackward (dictionaryBare domain) operation) =
        identityHom (ContextualMaterialSmallMapClassification.futureRepresented (dictionaryBare domain) operation)) ∧
    ((ContextualMaterialSmallMapClassification.futureBackward (dictionaryBare domain) operation).comp
      (ContextualMaterialSmallMapClassification.futureForward (dictionaryBare domain) operation) =
        identityHom (pullback operation (ContextualMaterialSmallMapClassification.futureChange
          (dictionaryBare domain) operation))) ∧
    ((ContextualMaterialSmallMapClassification.universalForward (dictionaryBare domain) operation).comp
      (ContextualMaterialSmallMapClassification.universalBackward (dictionaryBare domain) operation) =
        identityHom (ContextualMaterialSmallMapClassification.futureRepresented (dictionaryBare domain) operation)) ∧
    ((ContextualMaterialSmallMapClassification.universalBackward (dictionaryBare domain) operation).comp
      (ContextualMaterialSmallMapClassification.universalForward (dictionaryBare domain) operation) =
        identityHom (ContextualMaterialSmallMapClassification.universalPullback (dictionaryBare domain) operation)) :=
  ContextualMaterialSmallMapClassification.two_pullbacks (dictionaryBare domain) operation

namespace ClosedCodes

variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (code : ContextualClosedUniverseCodes.Code seeds seedModel arrows context)
variable {parameters : context.base.Elements ⥤ Type v}
variable (authored : NaturalHom
  (dictionaryBare (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows code)).source parameters)

/-- Constructor-closed codes supply their already constructed complete
dictionary. No derivation is extracted from an inhabitation proposition. -/
def futureFactory (point : context.base.Elements) (parameter : parameters.obj point) :
    ContextualEnumerationCovers.FutureEnumerations authored point parameter :=
  futureEnumerations (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows code) authored point parameter

theorem futureFactory_covered (point : context.base.Elements) (parameter : parameters.obj point) :
    Nonempty (ContextualEnumerationCovers.FutureEnumerations authored point parameter) :=
  ⟨futureFactory seeds seedModel arrows code authored point parameter⟩

def mapCode : NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  mapClassifier (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows code) authored

theorem mapCode_decoded : ContextualSmallFamilyUniverse.decodedFamily
    (mapCode seeds seedModel arrows code authored) =
      mapSmallFamily (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows code) authored :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

end ClosedCodes

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassification
