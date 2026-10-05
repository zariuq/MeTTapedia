import Mettapedia.TypeTheory.ContextualImageFactorization
import Mettapedia.TypeTheory.ContextualEnumerationCovers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

/-!
# Actual covered-relation objects and membership pullbacks

A stable relation constructs its literal subtype functor, parameter and
argument projections. The covered-power classifier identifies this total
relation object with the actual pullback of universal membership, through
constructed natural inverse maps. Arbitrary parameter substitution similarly
constructs the literal relation pullback and preserves its two coordinates.

Parameter and argument families may live in independent larger universes.
The cover condition concerns the complete future of each retained parameter;
it does not classify every map with merely pointwise existential small fibres
or establish a universal small-map representation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCoveredRelationClassifier

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open CoveredFuturePowerClassifier
open CoveredFuturePowerFamilies (family Power current)

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (B : D ⥤ Type w) (A : D ⥤ Type v)

def total (predicate : StablePredicate (product B A)) : D ⥤ Type (max w v) where
  obj point := {pair : B.obj point × A.obj point // predicate.holds ⟨point, pair⟩}
  map {first second} step := TypeCat.ofHom fun pair =>
    ⟨(B.map step pair.val.1, A.map step pair.val.2),
      predicate.closed (CategoryOfElements.homMk (F := product B A)
        ⟨first, pair.val⟩ ⟨second, (B.map step pair.val.1, A.map step pair.val.2)⟩ step rfl) pair.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Subtype.ext (Prod.ext (B.map_id_apply point pair.val.1) (A.map_id_apply point pair.val.2))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Subtype.ext (Prod.ext (B.map_comp_apply first second pair.val.1)
      (A.map_comp_apply first second pair.val.2))

def parameterProjection (predicate : StablePredicate (product B A)) : NaturalHom (total B A predicate) B where
  app _ pair := pair.val.1
  naturality _ _ := rfl

def argumentProjection (predicate : StablePredicate (product B A)) : NaturalHom (total B A predicate) A where
  app _ pair := pair.val.2
  naturality _ _ := rfl

def relationInclusion (predicate : StablePredicate (product B A)) :
    NaturalHom (total B A predicate) (product B A) where
  app _ := Subtype.val
  naturality _ _ := rfl

theorem relationInclusion_injective (predicate : StablePredicate (product B A)) (point : D) :
    Function.Injective ((relationInclusion B A predicate).app point) :=
  fun _ _ same => Subtype.ext same

/-- The actual parameter fibre is exactly the typed relation row, with
both directions constructed from its retained parameter equality. -/
def parameterFibreEquiv (predicate : StablePredicate (product B A)) (point : D) (parameter : B.obj point) :
    Fibre (parameterProjection B A predicate) point parameter ≃
      {argument : A.obj point // predicate.holds ⟨point, (parameter, argument)⟩} where
  toFun receipt := ⟨receipt.val.val.2, by
    have truth := receipt.val.property
    change predicate.holds ⟨point, (receipt.val.val.1, receipt.val.val.2)⟩ at truth
    have parameterEq : receipt.val.val.1 = parameter := receipt.property
    simpa only [parameterEq] using truth⟩
  invFun argument := ⟨⟨(parameter, argument.val), argument.property⟩, rfl⟩
  left_inv receipt := Subtype.ext (Subtype.ext (Prod.ext receipt.property.symm rfl))
  right_inv _ := Subtype.ext rfl

/-- Every relation receipt constructs an actual member of the corresponding
parameter fibre. The complete future index is retained in its carrier. -/
def relationFutureEnumerations (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point)
    (enumeration : RelationEnumeration B A predicate point parameter) :
    ContextualEnumerationCovers.FutureEnumerations (parameterProjection B A predicate) point parameter :=
  fun future => {
    Carrier := enumeration.Carrier future
    value code := ⟨⟨(B.map future.2 parameter, enumeration.value future code),
      (enumeration.covered future _).mpr ⟨code, rfl⟩⟩, rfl⟩
    covered receipt := by
      have truth := receipt.val.property
      have parameterEq : receipt.val.val.1 = B.map future.2 parameter := receipt.property
      change predicate.holds ⟨future.1, (receipt.val.val.1, receipt.val.val.2)⟩ at truth
      have related : predicate.holds ⟨future.1, (B.map future.2 parameter, receipt.val.val.2)⟩ := by
        simpa only [parameterEq] using truth
      obtain ⟨code, same⟩ := (enumeration.covered future receipt.val.val.2).mp related
      exact ⟨code, Subtype.ext (Subtype.ext (Prod.ext parameterEq.symm same))⟩ }

/-- Typed fibre enumerations supply precisely the related argument
enumerations. Parameter equalities are used to recover each actual row. -/
def futureRelationEnumeration (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point)
    (enumerations : ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A predicate) point parameter) :
    RelationEnumeration B A predicate point parameter where
  Carrier future := (enumerations future).Carrier
  value future code := ((enumerations future).value code).val.val.2
  covered future argument := by
    constructor
    · intro related
      let receipt : Fibre (parameterProjection B A predicate) future.1 (B.map future.2 parameter) :=
        ⟨⟨(B.map future.2 parameter, argument), related⟩, rfl⟩
      obtain ⟨code, same⟩ := (enumerations future).covered receipt
      exact ⟨code, congrArg (fun entry : Fibre (parameterProjection B A predicate) future.1
        (B.map future.2 parameter) => entry.val.val.2) same⟩
    · rintro ⟨code, same⟩
      have truth := ((enumerations future).value code).val.property
      have parameterEq : ((enumerations future).value code).val.val.1 = B.map future.2 parameter :=
        ((enumerations future).value code).property
      change predicate.holds ⟨future.1,
        (((enumerations future).value code).val.val.1, ((enumerations future).value code).val.val.2)⟩ at truth
      simpa only [parameterEq, same] using truth

theorem relationFutureEnumerations_argument (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point)
    (enumeration : RelationEnumeration B A predicate point parameter)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (code : enumeration.Carrier future) :
    (((relationFutureEnumerations B A predicate point parameter enumeration future).value code).val).val.2 =
      enumeration.value future code := rfl

theorem futureRelationEnumeration_argument (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point)
    (enumerations : ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A predicate) point parameter)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (code : (enumerations future).Carrier) :
    (futureRelationEnumeration B A predicate point parameter enumerations).value future code =
      ((enumerations future).value code).val.val.2 := rfl

theorem relation_cover_iff_future_fibres (predicate : StablePredicate (product B A)) :
    (∀ point parameter, Nonempty (RelationEnumeration B A predicate point parameter)) ↔
      ∀ point parameter, Nonempty (ContextualEnumerationCovers.FutureEnumerations
        (parameterProjection B A predicate) point parameter) :=
  ⟨fun covered point parameter => by
    obtain ⟨enumeration⟩ := covered point parameter
    exact ⟨relationFutureEnumerations B A predicate point parameter enumeration⟩,
    fun covered point parameter => by
      obtain ⟨enumerations⟩ := covered point parameter
      exact ⟨futureRelationEnumeration B A predicate point parameter enumerations⟩⟩

def coveredFromFuture (predicate : StablePredicate (product B A))
    (covered : ∀ point parameter, Nonempty (ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A predicate) point parameter)) : CoveredRelation B A where
  predicate := predicate
  covered := (relation_cover_iff_future_fibres B A predicate).mpr covered

theorem projection_futureCovered (relation : CoveredRelation B A) :
    ∀ point parameter, Nonempty (ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A relation.predicate) point parameter) :=
  (relation_cover_iff_future_fibres B A relation.predicate).mp relation.covered

def presentFibreEnumeration (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point)
    (enumeration : RelationEnumeration B A predicate point parameter) :
    Enumeration.{u, max w v} (Fibre (parameterProjection B A predicate) point parameter) :=
  (relationFutureEnumerations B A predicate point parameter enumeration ⟨point, 𝟙 point⟩).transport {
    toFun receipt := ⟨receipt.val, receipt.property.trans (B.map_id_apply point parameter)⟩
    invFun receipt := ⟨receipt.val, receipt.property.trans (B.map_id_apply point parameter).symm⟩
    left_inv _ := Subtype.ext rfl
    right_inv _ := Subtype.ext rfl }

theorem projection_smallFibres (relation : CoveredRelation B A) :
    SmallFibres (parameterProjection B A relation.predicate) := by
  intro point parameter
  obtain ⟨enumeration⟩ := relation.covered point parameter
  exact ⟨presentFibreEnumeration B A relation.predicate point parameter enumeration⟩

def membershipTotal : D ⥤ Type (max u v) :=
  total (family A) A (membershipRelation A).predicate

def membershipProjection : NaturalHom (membershipTotal A) (family A) :=
  parameterProjection (family A) A (membershipRelation A).predicate

def membershipArgument : NaturalHom (membershipTotal A) A :=
  argumentProjection (family A) A (membershipRelation A).predicate

def membershipFutureEnumerations (point : D) (predicate : Power A point)
    (enumeration : CoveredFuturePowerFamilies.Enumeration predicate.val) :
    ContextualEnumerationCovers.FutureEnumerations (membershipProjection A) point predicate :=
  relationFutureEnumerations (family A) A (membershipRelation A).predicate point predicate
    (classifiedEnumeration (family A) A (identityHom (family A)) point predicate enumeration)

theorem membershipFutureEnumerations_argument (point : D) (predicate : Power A point)
    (enumeration : CoveredFuturePowerFamilies.Enumeration predicate.val)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (code : enumeration.Carrier future) :
    (((membershipFutureEnumerations A point predicate enumeration future).value code).val).val.2 =
      enumeration.value future code := rfl

theorem membershipProjection_futureCovered :
    ∀ point predicate, Nonempty (ContextualEnumerationCovers.FutureEnumerations
      (membershipProjection A) point predicate) :=
  projection_futureCovered (family A) A (membershipRelation A)

theorem membershipProjection_smallFibres : SmallFibres (membershipProjection A) :=
  projection_smallFibres (family A) A (membershipRelation A)

theorem classifier_current (relation : CoveredRelation B A)
    (point : D) (parameter : B.obj point) (argument : A.obj point) :
    (membershipRelation A).predicate.holds ⟨point, ((classifier B A relation).app point parameter, argument)⟩ ↔
      relation.predicate.holds ⟨point, (parameter, argument)⟩ := by
  change relation.predicate.holds ⟨point, (B.map (𝟙 point) parameter, argument)⟩ ↔ _
  rw [B.map_id_apply]

def classifiedMap (relation : CoveredRelation B A) :
    NaturalHom (total B A relation.predicate) (membershipTotal A) where
  app point receipt := ⟨((classifier B A relation).app point receipt.val.1, receipt.val.2),
    (classifier_current B A relation point receipt.val.1 receipt.val.2).mpr receipt.property⟩
  naturality step receipt := Subtype.ext (Prod.ext
    ((classifier B A relation).naturality step receipt.val.1) rfl)

theorem classified_parameter_square (relation : CoveredRelation B A) :
    (classifiedMap B A relation).comp (membershipProjection A) =
      (parameterProjection B A relation.predicate).comp (classifier B A relation) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem classified_argument_square (relation : CoveredRelation B A) :
    (classifiedMap B A relation).comp (membershipArgument A) =
      argumentProjection B A relation.predicate := by
  apply NaturalHom.ext
  intro _ _
  rfl

/-- Classifying actual projection fibres and then reading their argument
coordinate recovers the same full future classifier, not merely its current
support. Both directions use literal typed relation receipts. -/
theorem projection_classifier_image (relation : CoveredRelation B A) :
    (ContextualEnumerationCovers.fibreClassifier (parameterProjection B A relation.predicate)
      (projection_futureCovered B A relation)).comp
        (CoveredFuturePowerFunctor.imageHom (argumentProjection B A relation.predicate)) =
          classifier B A relation := by
  apply NaturalHom.ext
  intro point parameter
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro argument
  constructor
  · rintro ⟨receipt, same, parameterEq⟩
    have truth := receipt.property
    change receipt.val.1 = B.map argument.1.2 parameter at parameterEq
    change receipt.val.2 = argument.2 at same
    change relation.predicate.holds ⟨argument.1.1, (receipt.val.1, receipt.val.2)⟩ at truth
    change relation.predicate.holds ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩
    simpa only [parameterEq, same] using truth
  · intro related
    exact ⟨⟨(B.map argument.1.2 parameter, argument.2), related⟩, rfl, rfl⟩

abbrev membershipPullback (relation : CoveredRelation B A) :=
  pullback (membershipProjection A) (classifier B A relation)

def membershipForward (relation : CoveredRelation B A) :
    NaturalHom (total B A relation.predicate) (membershipPullback B A relation) :=
  pullbackPair (membershipProjection A) (classifier B A relation)
    (classifiedMap B A relation) (parameterProjection B A relation.predicate)
      (classified_parameter_square B A relation)

def membershipBackward (relation : CoveredRelation B A) :
    NaturalHom (membershipPullback B A relation) (total B A relation.predicate) where
  app point pair := ⟨(pair.val.2, pair.val.1.val.2), by
    apply (classifier_current B A relation point pair.val.2 pair.val.1.val.2).mp
    have truth := pair.val.1.property
    change (membershipRelation A).predicate.holds ⟨point, (pair.val.1.val.1, pair.val.1.val.2)⟩ at truth
    have parameterEq : pair.val.1.val.1 = (classifier B A relation).app point pair.val.2 := pair.property
    simpa only [parameterEq] using truth⟩
  naturality _ _ := Subtype.ext rfl

theorem membership_left (relation : CoveredRelation B A) (point : D)
    (receipt : (total B A relation.predicate).obj point) :
    (membershipBackward B A relation).app point ((membershipForward B A relation).app point receipt) = receipt :=
  Subtype.ext rfl

theorem membership_right (relation : CoveredRelation B A) (point : D)
    (receipt : (membershipPullback B A relation).obj point) :
    (membershipForward B A relation).app point ((membershipBackward B A relation).app point receipt) = receipt :=
  Subtype.ext (Prod.ext (Subtype.ext (Prod.ext receipt.property.symm rfl)) rfl)

def membershipEquiv (relation : CoveredRelation B A) (point : D) :
    (total B A relation.predicate).obj point ≃ (membershipPullback B A relation).obj point where
  toFun := (membershipForward B A relation).app point
  invFun := (membershipBackward B A relation).app point
  left_inv := membership_left B A relation point
  right_inv := membership_right B A relation point

def membershipSectionEquiv (relation : CoveredRelation B A) :
    (total B A relation.predicate).sections ≃ (membershipPullback B A relation).sections where
  toFun := (membershipForward B A relation).mapSection
  invFun := (membershipBackward B A relation).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact membership_left B A relation point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact membership_right B A relation point (term.val point)

theorem membershipForward_parameter (relation : CoveredRelation B A) :
    (membershipForward B A relation).comp
      (pullbackSecond (membershipProjection A) (classifier B A relation)) =
        parameterProjection B A relation.predicate :=
  pullbackPair_second (membershipProjection A) (classifier B A relation)
    (classifiedMap B A relation) (parameterProjection B A relation.predicate) _

theorem membershipForward_argument (relation : CoveredRelation B A) :
    (membershipForward B A relation).comp
      ((pullbackFirst (membershipProjection A) (classifier B A relation)).comp (membershipArgument A)) =
        argumentProjection B A relation.predicate := by
  apply NaturalHom.ext
  intro _ _
  rfl

section ParameterSubstitution

variable {B' : D ⥤ Type z} (change : NaturalHom B' B) (relation : CoveredRelation B A)

def substitutionFutureEnumerations (point : D) (parameter : B'.obj point)
    (enumerations : ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A relation.predicate) point (change.app point parameter)) :
    ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B' A (parameterSubstitution B A change relation).predicate) point parameter :=
  relationFutureEnumerations B' A (parameterSubstitution B A change relation).predicate point parameter
    (substituteEnumeration B A change
      (futureRelationEnumeration B A relation.predicate point (change.app point parameter) enumerations))

theorem substitutionFutureEnumerations_argument (point : D) (parameter : B'.obj point)
    (enumerations : ContextualEnumerationCovers.FutureEnumerations
      (parameterProjection B A relation.predicate) point (change.app point parameter))
    (future : PowerClassPresheafBaseChange.Future.Objects point) (code : (enumerations future).Carrier) :
    (((substitutionFutureEnumerations B A change relation point parameter enumerations future).value code).val).val.2 =
      ((enumerations future).value code).val.val.2 := rfl

def parameterTotalMap :
    NaturalHom (total B' A (parameterSubstitution B A change relation).predicate) (total B A relation.predicate) where
  app _ receipt := ⟨(change.app _ receipt.val.1, receipt.val.2), receipt.property⟩
  naturality step receipt := Subtype.ext (Prod.ext (change.naturality step receipt.val.1) rfl)

theorem parameterTotal_square :
    (parameterTotalMap B A change relation).comp (parameterProjection B A relation.predicate) =
      (parameterProjection B' A (parameterSubstitution B A change relation).predicate).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

def substitutionForward :
    NaturalHom (total B' A (parameterSubstitution B A change relation).predicate)
      (pullback (parameterProjection B A relation.predicate) change) :=
  pullbackPair (parameterProjection B A relation.predicate) change (parameterTotalMap B A change relation)
    (parameterProjection B' A (parameterSubstitution B A change relation).predicate)
      (parameterTotal_square B A change relation)

def substitutionBackward :
    NaturalHom (pullback (parameterProjection B A relation.predicate) change)
      (total B' A (parameterSubstitution B A change relation).predicate) where
  app point receipt := ⟨(receipt.val.2, receipt.val.1.val.2), by
    change relation.predicate.holds ⟨point, (change.app point receipt.val.2, receipt.val.1.val.2)⟩
    have truth := receipt.val.1.property
    change relation.predicate.holds ⟨point, (receipt.val.1.val.1, receipt.val.1.val.2)⟩ at truth
    have parameterEq : receipt.val.1.val.1 = change.app point receipt.val.2 := receipt.property
    simpa only [parameterEq] using truth⟩
  naturality _ _ := Subtype.ext rfl

theorem substitution_left (point : D)
    (receipt : (total B' A (parameterSubstitution B A change relation).predicate).obj point) :
    (substitutionBackward B A change relation).app point
      ((substitutionForward B A change relation).app point receipt) = receipt := Subtype.ext rfl

theorem substitution_right (point : D)
    (receipt : (pullback (parameterProjection B A relation.predicate) change).obj point) :
    (substitutionForward B A change relation).app point
      ((substitutionBackward B A change relation).app point receipt) = receipt :=
  Subtype.ext (Prod.ext (Subtype.ext (Prod.ext receipt.property.symm rfl)) rfl)

def substitutionEquiv (point : D) :
    (total B' A (parameterSubstitution B A change relation).predicate).obj point ≃
      (pullback (parameterProjection B A relation.predicate) change).obj point where
  toFun := (substitutionForward B A change relation).app point
  invFun := (substitutionBackward B A change relation).app point
  left_inv := substitution_left B A change relation point
  right_inv := substitution_right B A change relation point

def substitutionSectionEquiv :
    (total B' A (parameterSubstitution B A change relation).predicate).sections ≃
      (pullback (parameterProjection B A relation.predicate) change).sections where
  toFun := (substitutionForward B A change relation).mapSection
  invFun := (substitutionBackward B A change relation).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact substitution_left B A change relation point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact substitution_right B A change relation point (term.val point)

theorem substitution_membership_square :
    (parameterTotalMap B A change relation).comp (classifiedMap B A relation) =
      classifiedMap B' A (parameterSubstitution B A change relation) := by
  apply NaturalHom.ext
  intro point receipt
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun operation : NaturalHom B' (family A) => operation.app point receipt.val.1)
      (classifier_parameter_substitution B A change relation)).symm
  · rfl

end ParameterSubstitution

end Mettapedia.TypeTheory.ContextualCoveredRelationClassifier
