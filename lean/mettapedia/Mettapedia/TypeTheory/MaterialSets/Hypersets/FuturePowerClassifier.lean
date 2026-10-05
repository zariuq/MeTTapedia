import Mettapedia.TypeTheory.ContextualWitnessCover
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies

/-!
# The parameterized classifier of small contextual subsets

For arbitrary small type-valued functors `A` and `B`, natural maps from `B`
to the full future power family of `A` correspond to stable predicates on
the actual product `B × A`. The inverse interpretation transports the
parameter along the complete future arrow before testing the predicate.
Both inverse laws and substitution of arbitrary natural parameter maps are
proved from the actual functor and naturality laws.

For interpreted material families, the same correspondence reads membership
through the constructed contextual power dictionary. No material context,
arrow, parameter, or future argument is selected from mere existence.
All objects, arrows, and functor fibres here are in one small universe.
This does not construct a small powerclass of arbitrary large objects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifier

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open FuturePowerFamilies
open ContextualGeneratedUniverse

universe u

variable {D : Type u} [Category.{u} D]

def product (B A : D ⥤ Type u) : D ⥤ Type u where
  obj point := B.obj point × A.obj point
  map step := TypeCat.ofHom (fun pair => (B.map step pair.1, A.map step pair.2))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Prod.ext (B.map_id_apply point pair.1) (A.map_id_apply point pair.2)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact Prod.ext (B.map_comp_apply first second pair.1) (A.map_comp_apply first second pair.2)

variable (B A : D ⥤ Type u)

def firstProjection : NaturalHom (product B A) B where
  app _ pair := pair.1
  naturality _ _ := rfl

def secondProjection : NaturalHom (product B A) A where
  app _ pair := pair.2
  naturality _ _ := rfl

def pair {F : D ⥤ Type u} (first : NaturalHom F B) (second : NaturalHom F A) :
    NaturalHom F (product B A) where
  app point value := (first.app point value, second.app point value)
  naturality step value := Prod.ext (first.naturality step value) (second.naturality step value)

theorem pair_first {F : D ⥤ Type u} (first : NaturalHom F B) (second : NaturalHom F A) :
    (pair B A first second).comp (firstProjection B A) = first := by
  apply NaturalHom.ext
  intro point value
  rfl

theorem pair_second {F : D ⥤ Type u} (first : NaturalHom F B) (second : NaturalHom F A) :
    (pair B A first second).comp (secondProjection B A) = second := by
  apply NaturalHom.ext
  intro point value
  rfl

theorem pair_projections {F : D ⥤ Type u} (operation : NaturalHom F (product B A)) :
    pair B A (operation.comp (firstProjection B A)) (operation.comp (secondProjection B A)) = operation := by
  apply NaturalHom.ext
  intro point value
  rfl

/-- The independently constructed componentwise functor is a product for
all natural maps from arbitrary small parameter objects. -/
def productHomEquiv (F : D ⥤ Type u) :
    NaturalHom F (product B A) ≃ (NaturalHom F B × NaturalHom F A) where
  toFun operation := (operation.comp (firstProjection B A), operation.comp (secondProjection B A))
  invFun maps := pair B A maps.1 maps.2
  left_inv := pair_projections B A
  right_inv maps := Prod.ext (pair_first B A maps.1 maps.2) (pair_second B A maps.1 maps.2)

/-- Evaluate the natural power-family map at the present argument. Its
stability follows by moving that argument into the full future and then
using naturality of the parameterized map. -/
def classifiedPredicate (operation : NaturalHom B (family A)) : StablePredicate (product B A) where
  holds point := (operation.app point.1 point.2.1).holds (current A point.1 point.2.2)
  closed {first second} step available := by
    have parameterEq : B.map step.1 first.2.1 = second.2.1 := congrArg Prod.fst step.2
    have argumentEq : A.map step.1 first.2.2 = second.2.2 := congrArg Prod.snd step.2
    let future : Arguments A first.1 := ⟨⟨second.1, step.1⟩, second.2.2⟩
    have movement : current A first.1 first.2.2 ⟶ future :=
      ⟨⟨step.1, Category.id_comp _⟩, argumentEq⟩
    have later := (operation.app first.1 first.2.1).closed movement available
    have same := operation.naturality step.1 first.2.1
    have truth := congrArg (fun predicate : Predicate A second.1 =>
      predicate.holds (current A second.1 second.2.2)) same
    change (operation.app first.1 first.2.1).holds
      ⟨⟨second.1, step.1 ≫ 𝟙 second.1⟩, second.2.2⟩ =
        (operation.app second.1 (B.map step.1 first.2.1)).holds (current A second.1 second.2.2) at truth
    rw [Category.comp_id, parameterEq] at truth
    exact truth ▸ later

/-- The classifier tests the original predicate at every later object,
transporting its parameter along the actual future arrow. -/
def classifier (predicate : StablePredicate (product B A)) : NaturalHom B (family A) where
  app point parameter := {
    holds argument := predicate.holds ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩
    closed {first second} step available := by
      have parameterEq : B.map step.1.1 (B.map first.1.2 parameter) = B.map second.1.2 parameter := by
        have triangle := congrArg (fun arrow => B.map arrow parameter) step.1.2
        exact (B.map_comp_apply first.1.2 step.1.1 parameter).symm.trans triangle
      let movement := CategoryOfElements.homMk (F := product B A)
        ⟨first.1.1, (B.map first.1.2 parameter, first.2)⟩
        ⟨second.1.1, (B.map second.1.2 parameter, second.2)⟩ step.1.1 (Prod.ext parameterEq step.2)
      exact predicate.closed movement available }
  naturality {first second} step parameter := by
    apply Predicate.ext
    intro argument
    change predicate.holds ⟨argument.1.1, (B.map (step ≫ argument.1.2) parameter, argument.2)⟩ ↔
      predicate.holds ⟨argument.1.1, (B.map argument.1.2 (B.map step parameter), argument.2)⟩
    rw [B.map_comp_apply]

theorem classified_classifier (predicate : StablePredicate (product B A)) :
    classifiedPredicate B A (classifier B A predicate) = predicate := by
  apply StablePredicate.ext
  rintro ⟨point, parameter, argument⟩
  change predicate.holds ⟨point, (B.map (𝟙 point) parameter, argument)⟩ ↔
    predicate.holds ⟨point, (parameter, argument)⟩
  rw [B.map_id_apply]

theorem classifier_classified (operation : NaturalHom B (family A)) :
    classifier B A (classifiedPredicate B A operation) = operation := by
  apply NaturalHom.ext
  intro point parameter
  apply Predicate.ext
  intro argument
  have same := operation.naturality argument.1.2 parameter
  have truth := congrArg (fun predicate : Predicate A argument.1.1 =>
    predicate.holds (current A argument.1.1 argument.2)) same
  change (operation.app point parameter).holds
    ⟨⟨argument.1.1, argument.1.2 ≫ 𝟙 argument.1.1⟩, argument.2⟩ =
      (operation.app argument.1.1 (B.map argument.1.2 parameter)).holds
        (current A argument.1.1 argument.2) at truth
  rw [Category.comp_id] at truth
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact (iff_of_eq truth).symm

def classifierEquiv : NaturalHom B (family A) ≃ StablePredicate (product B A) where
  toFun := classifiedPredicate B A
  invFun := classifier B A
  left_inv := classifier_classified B A
  right_inv := classified_classifier B A

theorem classifier_future (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point) (argument : Arguments A point) :
    ((classifier B A predicate).app point parameter).holds argument ↔
      predicate.holds ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩ := Iff.rfl

theorem classified_future (operation : NaturalHom B (family A))
    (point : D) (parameter : B.obj point) (argument : Arguments A point) :
    (operation.app point parameter).holds argument ↔
      (classifiedPredicate B A operation).holds
        ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩ := by
  have same := congrArg (fun map : NaturalHom B (family A) => map.app point parameter)
    (classifier_classified B A operation)
  rw [← same]
  exact Iff.rfl

def parameterIdentity : NaturalHom B B where
  app _ parameter := parameter
  naturality _ _ := rfl

variable {B' B'' : D ⥤ Type u}

def productParameter (operation : NaturalHom B' B) : NaturalHom (product B' A) (product B A) where
  app point pair := (operation.app point pair.1, pair.2)
  naturality step pair := Prod.ext (operation.naturality step pair.1) rfl

/-- Pullback of stable predicates along an actual natural map. -/
def pullbackStable {first second : D ⥤ Type u} (operation : NaturalHom first second)
    (predicate : StablePredicate second) : StablePredicate first where
  holds point := predicate.holds ⟨point.1, operation.app point.1 point.2⟩
  closed {first second} step available :=
    predicate.closed ⟨step.1, (operation.naturality step.1 first.2).trans
      (congrArg (operation.app second.1) step.2)⟩ available

def parameterSubstitution (operation : NaturalHom B' B) (predicate : StablePredicate (product B A)) :
    StablePredicate (product B' A) := pullbackStable (productParameter B A operation) predicate

theorem classified_parameter_substitution (operation : NaturalHom B (family A))
    (substitution : NaturalHom B' B) :
    classifiedPredicate B' A (substitution.comp operation) =
      parameterSubstitution B A substitution (classifiedPredicate B A operation) := by
  apply StablePredicate.ext
  intro point
  exact Iff.rfl

theorem classifier_parameter_substitution (substitution : NaturalHom B' B)
    (predicate : StablePredicate (product B A)) :
    classifier B' A (parameterSubstitution B A substitution predicate) =
      substitution.comp (classifier B A predicate) := by
  apply NaturalHom.ext
  intro point parameter
  apply Predicate.ext
  intro argument
  change predicate.holds
      ⟨argument.1.1, (substitution.app argument.1.1 (B'.map argument.1.2 parameter), argument.2)⟩ ↔
    predicate.holds ⟨argument.1.1, (B.map argument.1.2 (substitution.app point parameter), argument.2)⟩
  rw [substitution.naturality]

theorem parameterSubstitution_identity (predicate : StablePredicate (product B A)) :
    parameterSubstitution B A (parameterIdentity B) predicate = predicate := by
  apply StablePredicate.ext
  intro point
  rcases point with ⟨_, _, _⟩
  exact Iff.rfl

theorem parameterSubstitution_comp (first : NaturalHom B'' B') (second : NaturalHom B' B)
    (predicate : StablePredicate (product B A)) :
    parameterSubstitution B' A first (parameterSubstitution B A second predicate) =
      parameterSubstitution B A (first.comp second) predicate := by
  apply StablePredicate.ext
  intro point
  exact Iff.rfl

theorem productParameter_identity : productParameter B A (parameterIdentity B) = parameterIdentity (product B A) := by
  apply NaturalHom.ext
  rintro point ⟨parameter, argument⟩
  rfl

theorem productParameter_comp (first : NaturalHom B'' B') (second : NaturalHom B' B) :
    (productParameter B' A first).comp (productParameter B A second) =
      productParameter B A (first.comp second) := by
  apply NaturalHom.ext
  intro point pair
  rfl

variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

/-- The parameterized classifier's full future interpretation is literal
membership in the constructed material power-family value. -/
theorem material_classifier_future (parameters : context.base.Elements ⥤ Type u)
    (predicate : StablePredicate (product parameters domain.family))
    (point : context.base.Elements) (parameter : parameters.obj point)
    (argument : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading argument ∈
        ((ContextualPowerFamilies.power domain arrows).model point).value
          ((classifier parameters domain.family predicate).app point parameter) ↔
      predicate.holds ⟨argument.1.1, (parameters.map argument.1.2 parameter, argument.2)⟩ :=
  (ContextualPowerFamilies.power_truth domain arrows point _ argument).trans Iff.rfl

/-- A material parameter is decoded by its existing dictionary; the complete
future arrow transports that decoded term before predicate evaluation. -/
theorem material_member_parameter_future (parameters : MaterialFamily context)
    (predicate : StablePredicate (product parameters.family domain.family))
    (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (parameters.model point).carrier})
    (argument : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading argument ∈
        ((ContextualPowerFamilies.power domain arrows).model point).value
          ((classifier parameters.family domain.family predicate).app point ((parameters.model point).decode member)) ↔
      predicate.holds ⟨argument.1.1,
        (parameters.family.map argument.1.2 ((parameters.model point).decode member), argument.2)⟩ :=
  material_classifier_future domain arrows parameters.family predicate point _ argument

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerClassifier
