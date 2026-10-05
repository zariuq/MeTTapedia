import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialEnumerationDecoders
import Mettapedia.TypeTheory.MaterialSets.Hypersets.BareContextualFamilies
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

/-!
# Constructed coherent small models of covered material fibres

Actual material carriers and authored member restrictions determine the
source functor. Uniform receipt enumerations construct small saturated
predicate codes for its typed fibres. Their bounded material decoder and
the original member restrictions construct every small-fibre action.

The total small family has explicit inverse natural maps with the literal
parameter pullback. In particular, the existing future-data parameter
cover constructs all enumeration data needed by this model. Pointwise
existence of separate enumerations does not select those data. The small
codes use full proposition-valued subsets of their receipt carriers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassification

open CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualGeneratedUniverse

open CoveredFuturePowerFunctor

universe u v w z
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : BareContextualFamilies.Family.{u, u} context)
variable {B : context.base.Elements ⥤ Type v} {F : context.base.Elements ⥤ Type w}
variable (operation : NaturalHom domain.source B) (change : NaturalHom F B)
variable (enumerations : ∀ point parameter,
  Enumeration.{u, u + 1} (Fibre operation point (change.app point parameter)))

abbrev SmallAt (point : F.Elements) : Type u :=
  MaterialEnumerationDecoders.FibreCode (operation.app point.1) (change.app point.1 point.2) (enumerations point.1 point.2)

def fibreDecoder (point : F.Elements) : SmallAt domain operation change enumerations point ≃
    Fibre operation point.1 (change.app point.1 point.2) :=
  MaterialEnumerationDecoders.fibreCodeEquiv (operation.app point.1) (change.app point.1 point.2) (enumerations point.1 point.2)

def fibreRestriction {first second : F.Elements} (step : first ⟶ second)
    (receipt : Fibre operation first.1 (change.app first.1 first.2)) :
    Fibre operation second.1 (change.app second.1 second.2) :=
  ⟨domain.source.map step.1 receipt.val, by
    rw [← operation.naturality step.1 receipt.val, receipt.property,
      change.naturality step.1 first.2, step.2]⟩

def smallMap {first second : F.Elements} (step : first ⟶ second) :
    SmallAt domain operation change enumerations first → SmallAt domain operation change enumerations second :=
  fun code => (fibreDecoder domain operation change enumerations second).symm
    (fibreRestriction domain operation change step
      (fibreDecoder domain operation change enumerations first code))

theorem smallMap_decode {first second : F.Elements} (step : first ⟶ second)
    (code : SmallAt domain operation change enumerations first) :
    fibreDecoder domain operation change enumerations second
      (smallMap domain operation change enumerations step code) =
    fibreRestriction domain operation change step
      (fibreDecoder domain operation change enumerations first code) :=
  (fibreDecoder domain operation change enumerations second).apply_symm_apply _

theorem smallMap_encode {first second : F.Elements} (step : first ⟶ second)
    (receipt : Fibre operation first.1 (change.app first.1 first.2)) :
    smallMap domain operation change enumerations step
      ((fibreDecoder domain operation change enumerations first).symm receipt) =
    (fibreDecoder domain operation change enumerations second).symm
      (fibreRestriction domain operation change step receipt) := by
  unfold smallMap
  rw [Equiv.apply_symm_apply]

theorem smallMap_id (point : F.Elements) (code : SmallAt domain operation change enumerations point) :
    smallMap domain operation change enumerations (𝟙 point) code = code := by
  apply (fibreDecoder domain operation change enumerations point).injective
  rw [smallMap_decode]
  apply Subtype.ext
  exact domain.source.map_id_apply point.1 _

theorem smallMap_comp {first middle last : F.Elements} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (code : SmallAt domain operation change enumerations first) :
    smallMap domain operation change enumerations (earlier ≫ later) code =
      smallMap domain operation change enumerations later
        (smallMap domain operation change enumerations earlier code) := by
  apply (fibreDecoder domain operation change enumerations last).injective
  rw [smallMap_decode, smallMap_decode, smallMap_decode]
  apply Subtype.ext
  exact domain.source.map_comp_apply earlier.1 later.1 _

/-- Each code fibre and each contextual action is constructed from the
material decoder and the authored restriction, including varying fibres. -/
def smallFamily : F.Elements ⥤ Type u where
  obj := SmallAt domain operation change enumerations
  map step := TypeCat.ofHom (smallMap domain operation change enumerations step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact smallMap_id domain operation change enumerations point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact smallMap_comp domain operation change enumerations earlier later

theorem decode_restriction {first second : F.Elements} (step : first ⟶ second)
    (code : (smallFamily domain operation change enumerations).obj first) :
    (fibreDecoder domain operation change enumerations second
      ((smallFamily domain operation change enumerations).map step code)).val =
      domain.source.map step.1 (fibreDecoder domain operation change enumerations first code).val :=
  congrArg Subtype.val (smallMap_decode domain operation change enumerations step code)

abbrev representedTotal := ContextualSmallFamilyUniverse.total (smallFamily domain operation change enumerations)

def representedForward : NaturalHom (representedTotal domain operation change enumerations)
    (pullback operation change) where
  app point receipt :=
    let decoded := fibreDecoder domain operation change enumerations ⟨point, receipt.1⟩ receipt.2
    ⟨(decoded.val, receipt.1), decoded.property⟩
  naturality {first second} step receipt := by
    apply Subtype.ext
    apply Prod.ext
    · exact (decode_restriction domain operation change enumerations
        (CategoryOfElements.homMk (F := F) ⟨first, receipt.1⟩
          ⟨second, F.map step receipt.1⟩ step rfl) receipt.2).symm
    · rfl

def representedBackward : NaturalHom (pullback operation change)
    (representedTotal domain operation change enumerations) where
  app point pair := ⟨pair.val.2,
    (fibreDecoder domain operation change enumerations ⟨point, pair.val.2⟩).symm
      ⟨pair.val.1, pair.property⟩⟩
  naturality {first second} step pair := by
    change (⟨F.map step pair.val.2,
      smallMap domain operation change enumerations
        (CategoryOfElements.homMk (F := F) ⟨first, pair.val.2⟩
          ⟨second, F.map step pair.val.2⟩ step rfl)
        ((fibreDecoder domain operation change enumerations ⟨first, pair.val.2⟩).symm
          ⟨pair.val.1, pair.property⟩)⟩ :
      (representedTotal domain operation change enumerations).obj second) = _
    apply congrArg (fun code =>
      (⟨F.map step pair.val.2, code⟩ : (representedTotal domain operation change enumerations).obj second))
    exact smallMap_encode domain operation change enumerations
      (CategoryOfElements.homMk (F := F) ⟨first, pair.val.2⟩
        ⟨second, F.map step pair.val.2⟩ step rfl) ⟨pair.val.1, pair.property⟩

theorem represented_forward_backward (point : context.base.Elements) (pair : (pullback operation change).obj point) :
    (representedForward domain operation change enumerations).app point
      ((representedBackward domain operation change enumerations).app point pair) = pair := by
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val
    ((fibreDecoder domain operation change enumerations ⟨point, pair.val.2⟩).apply_symm_apply
      ⟨pair.val.1, pair.property⟩)) rfl

theorem represented_backward_forward (point : context.base.Elements)
    (receipt : (representedTotal domain operation change enumerations).obj point) :
    (representedBackward domain operation change enumerations).app point
      ((representedForward domain operation change enumerations).app point receipt) = receipt := by
  change (⟨receipt.1, (fibreDecoder domain operation change enumerations ⟨point, receipt.1⟩).symm
    (fibreDecoder domain operation change enumerations ⟨point, receipt.1⟩ receipt.2)⟩ :
    (representedTotal domain operation change enumerations).obj point) = receipt
  exact congrArg (fun code =>
    (⟨receipt.1, code⟩ : (representedTotal domain operation change enumerations).obj point))
    ((fibreDecoder domain operation change enumerations ⟨point, receipt.1⟩).symm_apply_apply receipt.2)

theorem represented_forward_backward_hom :
    (representedBackward domain operation change enumerations).comp
      (representedForward domain operation change enumerations) = identityHom (pullback operation change) := by
  apply NaturalHom.ext
  exact represented_forward_backward domain operation change enumerations

theorem represented_backward_forward_hom :
    (representedForward domain operation change enumerations).comp
      (representedBackward domain operation change enumerations) =
        identityHom (representedTotal domain operation change enumerations) := by
  apply NaturalHom.ext
  exact represented_backward_forward domain operation change enumerations

theorem represented_projection :
    (representedForward domain operation change enumerations).comp (pullbackSecond operation change) =
      ContextualSmallFamilyUniverse.projection (smallFamily domain operation change enumerations) := rfl

def representedEquiv (point : context.base.Elements) :
    (representedTotal domain operation change enumerations).obj point ≃ (pullback operation change).obj point where
  toFun := (representedForward domain operation change enumerations).app point
  invFun := (representedBackward domain operation change enumerations).app point
  left_inv := represented_backward_forward domain operation change enumerations point
  right_inv := represented_forward_backward domain operation change enumerations point

def representedSectionEquiv : (representedTotal domain operation change enumerations).sections ≃
    (pullback operation change).sections where
  toFun := (representedForward domain operation change enumerations).mapSection
  invFun := (representedBackward domain operation change enumerations).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact represented_backward_forward domain operation change enumerations point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact represented_forward_backward domain operation change enumerations point (term.val point)

def representedSource : NaturalHom (representedTotal domain operation change enumerations) domain.source :=
  (representedForward domain operation change enumerations).comp (pullbackFirst operation change)

def representedLift {R : context.base.Elements ⥤ Type z} (left : NaturalHom R domain.source)
    (right : NaturalHom R F) (square : left.comp operation = right.comp change) :
    NaturalHom R (representedTotal domain operation change enumerations) :=
  (pullbackPair operation change left right square).comp
    (representedBackward domain operation change enumerations)

theorem representedLift_source {R : context.base.Elements ⥤ Type z} (left : NaturalHom R domain.source)
    (right : NaturalHom R F) (square : left.comp operation = right.comp change) :
    (representedLift domain operation change enumerations left right square).comp
      (representedSource domain operation change enumerations) = left := by
  apply NaturalHom.ext
  intro point value
  exact congrArg (fun pair : (pullback operation change).obj point => pair.val.1)
    (represented_forward_backward domain operation change enumerations point
      ((pullbackPair operation change left right square).app point value))

theorem representedLift_parameter {R : context.base.Elements ⥤ Type z} (left : NaturalHom R domain.source)
    (right : NaturalHom R F) (square : left.comp operation = right.comp change) :
    (representedLift domain operation change enumerations left right square).comp
      (ContextualSmallFamilyUniverse.projection (smallFamily domain operation change enumerations)) = right := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem representedLift_unique {R : context.base.Elements ⥤ Type z} (left : NaturalHom R domain.source)
    (right : NaturalHom R F) (square : left.comp operation = right.comp change)
    (candidate : NaturalHom R (representedTotal domain operation change enumerations))
    (leftLaw : candidate.comp (representedSource domain operation change enumerations) = left)
    (rightLaw : candidate.comp
      (ContextualSmallFamilyUniverse.projection (smallFamily domain operation change enumerations)) = right) :
    candidate = representedLift domain operation change enumerations left right square := by
  apply NaturalHom.ext
  intro point value
  apply (representedEquiv domain operation change enumerations point).injective
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun map : NaturalHom R domain.source => map.app point value) leftLaw).trans
      (congrArg (fun map : NaturalHom R domain.source => map.app point value)
        (representedLift_source domain operation change enumerations left right square)).symm
  · exact (congrArg (fun map : NaturalHom R F => map.app point value) rightLaw).trans
      (congrArg (fun map : NaturalHom R F => map.app point value)
        (representedLift_parameter domain operation change enumerations left right square)).symm

/-- The first square has the universal property for every wider source
functor. Its lifting function is constructed, not selected from existence. -/
theorem represented_pullback_universal {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R domain.source) (right : NaturalHom R F)
    (square : left.comp operation = right.comp change) :
    ∃! lift : NaturalHom R (representedTotal domain operation change enumerations),
      lift.comp (representedSource domain operation change enumerations) = left ∧
      lift.comp (ContextualSmallFamilyUniverse.projection (smallFamily domain operation change enumerations)) = right :=
  ⟨representedLift domain operation change enumerations left right square,
    ⟨representedLift_source domain operation change enumerations left right square,
      representedLift_parameter domain operation change enumerations left right square⟩,
    fun candidate laws => representedLift_unique domain operation change enumerations left right square candidate
      laws.1 laws.2⟩

section ParameterSubstitution

variable {G : context.base.Elements ⥤ Type z} (earlier : NaturalHom G F)

def substitutedEnumerations (point : context.base.Elements) (parameter : G.obj point) :
    Enumeration.{u, u + 1} (Fibre operation point ((earlier.comp change).app point parameter)) :=
  enumerations point (earlier.app point parameter)

/-- The new small codes retain the same complete receipt predicates and
bounded material rows as actual reindexing of the old small family. -/
theorem smallFamily_parameter_substitution :
    smallFamily domain operation (earlier.comp change)
      (substitutedEnumerations domain operation change enumerations earlier) =
    ContextualSmallFamilyUniverse.substitutedFamily
      (smallFamily domain operation change enumerations) earlier := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem material_classifier_parameter_substitution :
    ContextualSmallFamilyUniverse.classifier
      (smallFamily domain operation (earlier.comp change)
        (substitutedEnumerations domain operation change enumerations earlier)) =
      earlier.comp (ContextualSmallFamilyUniverse.classifier
        (smallFamily domain operation change enumerations)) := by
  rw [smallFamily_parameter_substitution]
  exact ContextualSmallFamilyUniverse.classifier_parameter_substitution
    (smallFamily domain operation change enumerations) earlier

end ParameterSubstitution

/-! ## The actual future-data parameter cover supplies every enumeration -/

abbrev futureParameters := ContextualEnumerationCovers.futureFamily operation
abbrev futureChange := ContextualEnumerationCovers.futureProjection operation

def futureEnumerations (point : context.base.Elements) (parameter : (futureParameters domain operation).obj point) :
    Enumeration.{u, u + 1} (Fibre operation point ((futureChange domain operation).app point parameter)) :=
  ContextualEnumerationCovers.currentEnumeration operation point parameter

def futureSmallFamily : (futureParameters domain operation).Elements ⥤ Type u :=
  smallFamily domain operation (futureChange domain operation) (futureEnumerations domain operation)

abbrev futureRepresented := ContextualSmallFamilyUniverse.total (futureSmallFamily domain operation)

def futureClassifier : NaturalHom (futureParameters domain operation) ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (futureSmallFamily domain operation)

theorem future_decode_classifier :
    ContextualSmallFamilyUniverse.decodedFamily (futureClassifier domain operation) = futureSmallFamily domain operation :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq (futureSmallFamily domain operation)

def futureForward : NaturalHom (futureRepresented domain operation)
    (pullback operation (futureChange domain operation)) :=
  representedForward domain operation (futureChange domain operation) (futureEnumerations domain operation)

def futureBackward : NaturalHom (pullback operation (futureChange domain operation))
    (futureRepresented domain operation) :=
  representedBackward domain operation (futureChange domain operation) (futureEnumerations domain operation)

theorem futureForward_inverse : (futureForward domain operation).comp (futureBackward domain operation) =
    identityHom (futureRepresented domain operation) :=
  represented_backward_forward_hom domain operation (futureChange domain operation) (futureEnumerations domain operation)

theorem futureBackward_inverse : (futureBackward domain operation).comp (futureForward domain operation) =
    identityHom (pullback operation (futureChange domain operation)) :=
  represented_forward_backward_hom domain operation (futureChange domain operation) (futureEnumerations domain operation)

theorem future_parameters_cover
    (covered : ∀ point parameter, Nonempty (ContextualEnumerationCovers.FutureEnumerations operation point parameter))
    (point : context.base.Elements) : Function.Surjective ((futureChange domain operation).app point) :=
  ContextualEnumerationCovers.futureProjection_surjective operation covered point

def futureTop : NaturalHom (futureRepresented domain operation) domain.source :=
  (futureForward domain operation).comp (pullbackFirst operation (futureChange domain operation))

theorem future_square : (futureTop domain operation).comp operation =
    (ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation)).comp (futureChange domain operation) := by
  apply NaturalHom.ext
  intro point receipt
  exact (futureForward domain operation).app point receipt |>.property

theorem future_top_cover
    (covered : ∀ point parameter, Nonempty (ContextualEnumerationCovers.FutureEnumerations operation point parameter))
    (point : context.base.Elements) : Function.Surjective ((futureTop domain operation).app point) := by
  intro argument
  obtain ⟨pair, same⟩ := ContextualEnumerationCovers.futureTop_surjective operation covered point argument
  refine ⟨(futureBackward domain operation).app point pair, ?_⟩
  have inverse := represented_forward_backward domain operation (futureChange domain operation)
    (futureEnumerations domain operation) point pair
  exact (congrArg (fun pair => pair.val.1) inverse).trans same

/-! ## The second actual pullback is the constructed universal small family -/

abbrev universalPullback := pullback ContextualSmallFamilyUniverse.universalProjection
  (futureClassifier domain operation)

def universalForward : NaturalHom (futureRepresented domain operation) (universalPullback domain operation) :=
  ContextualSmallFamilyUniverse.classificationForward (futureSmallFamily domain operation)

def universalBackward : NaturalHom (universalPullback domain operation) (futureRepresented domain operation) :=
  ContextualSmallFamilyUniverse.classificationBackward (futureSmallFamily domain operation)

theorem universalForward_inverse :
    (universalForward domain operation).comp (universalBackward domain operation) =
      identityHom (futureRepresented domain operation) := by
  apply NaturalHom.ext
  exact ContextualSmallFamilyUniverse.classification_left (futureSmallFamily domain operation)

theorem universalBackward_inverse :
    (universalBackward domain operation).comp (universalForward domain operation) =
      identityHom (universalPullback domain operation) := by
  apply NaturalHom.ext
  exact ContextualSmallFamilyUniverse.classification_right (futureSmallFamily domain operation)

def universalTop : NaturalHom (futureRepresented domain operation) ContextualSmallFamilyUniverse.universalTotal :=
  ContextualSmallFamilyUniverse.classified (futureSmallFamily domain operation)

theorem universal_square :
    (universalTop domain operation).comp ContextualSmallFamilyUniverse.universalProjection =
      (ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation)).comp
        (futureClassifier domain operation) :=
  ContextualSmallFamilyUniverse.classified_parameter_square (futureSmallFamily domain operation)

theorem universalForward_projection :
    (universalForward domain operation).comp
      (pullbackSecond ContextualSmallFamilyUniverse.universalProjection (futureClassifier domain operation)) =
      ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation) :=
  ContextualSmallFamilyUniverse.classificationForward_parameter (futureSmallFamily domain operation)

def universalSectionEquiv : (futureRepresented domain operation).sections ≃
    (universalPullback domain operation).sections :=
  ContextualSmallFamilyUniverse.classificationSectionEquiv (futureSmallFamily domain operation)

def universalLift {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (right : NaturalHom R (futureParameters domain operation))
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection =
      right.comp (futureClassifier domain operation)) : NaturalHom R (futureRepresented domain operation) :=
  (pullbackPair ContextualSmallFamilyUniverse.universalProjection (futureClassifier domain operation)
    left right square).comp (universalBackward domain operation)

theorem universalLift_source {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (right : NaturalHom R (futureParameters domain operation))
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection =
      right.comp (futureClassifier domain operation)) :
    (universalLift domain operation left right square).comp (universalTop domain operation) = left := by
  apply NaturalHom.ext
  intro point value
  exact congrArg (fun pair : (universalPullback domain operation).obj point => pair.val.1)
    (ContextualSmallFamilyUniverse.classification_right (futureSmallFamily domain operation) point
      ((pullbackPair ContextualSmallFamilyUniverse.universalProjection (futureClassifier domain operation)
        left right square).app point value))

theorem universalLift_parameter {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (right : NaturalHom R (futureParameters domain operation))
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection =
      right.comp (futureClassifier domain operation)) :
    (universalLift domain operation left right square).comp
      (ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation)) = right := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem universalLift_unique {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (right : NaturalHom R (futureParameters domain operation))
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection =
      right.comp (futureClassifier domain operation))
    (candidate : NaturalHom R (futureRepresented domain operation))
    (leftLaw : candidate.comp (universalTop domain operation) = left)
    (rightLaw : candidate.comp (ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation)) = right) :
    candidate = universalLift domain operation left right square := by
  apply NaturalHom.ext
  intro point value
  apply (ContextualSmallFamilyUniverse.classificationEquiv (futureSmallFamily domain operation) point).injective
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal => map.app point value)
      leftLaw).trans
      (congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal => map.app point value)
        (universalLift_source domain operation left right square)).symm
  · exact (congrArg (fun map : NaturalHom R (futureParameters domain operation) => map.app point value)
      rightLaw).trans
      (congrArg (fun map : NaturalHom R (futureParameters domain operation) => map.app point value)
        (universalLift_parameter domain operation left right square)).symm

/-- The second square has the actual universal property with the same
middle small family and the constructed universal identity decoder. -/
theorem universal_pullback_universal {R : context.base.Elements ⥤ Type z}
    (left : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (right : NaturalHom R (futureParameters domain operation))
    (square : left.comp ContextualSmallFamilyUniverse.universalProjection =
      right.comp (futureClassifier domain operation)) :
    ∃! lift : NaturalHom R (futureRepresented domain operation),
      lift.comp (universalTop domain operation) = left ∧
      lift.comp (ContextualSmallFamilyUniverse.projection (futureSmallFamily domain operation)) = right :=
  ⟨universalLift domain operation left right square,
    ⟨universalLift_source domain operation left right square, universalLift_parameter domain operation left right square⟩,
    fun candidate laws => universalLift_unique domain operation left right square candidate laws.1 laws.2⟩

/-- Both literal pullbacks in the representability diagram have actual
inverse natural comparisons. The parameter cover is proved independently
from the precise covered-future hypothesis. This does not extend that
hypothesis to every pointwise-small material map. -/
theorem two_pullbacks :
    ((futureForward domain operation).comp (futureBackward domain operation) =
      identityHom (futureRepresented domain operation)) ∧
    ((futureBackward domain operation).comp (futureForward domain operation) =
      identityHom (pullback operation (futureChange domain operation))) ∧
    ((universalForward domain operation).comp (universalBackward domain operation) =
      identityHom (futureRepresented domain operation)) ∧
    ((universalBackward domain operation).comp (universalForward domain operation) =
      identityHom (universalPullback domain operation)) :=
  ⟨futureForward_inverse domain operation, futureBackward_inverse domain operation,
    universalForward_inverse domain operation, universalBackward_inverse domain operation⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSmallMapClassification
