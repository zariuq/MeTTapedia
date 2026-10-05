import Mettapedia.TypeTheory.ContextualWitnessCover
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies

/-!
# Parameterized classification of small-covered future relations

Argument and parameter fibres can live in different, arbitrarily larger
universes. A relation is an actual stable predicate on their componentwise
product. Its cover condition admits a small receipt carrier at every future
index, uniformly in that future index for each retained parameter. Receipt
values enumerate precisely the related arguments after parameter transport.

Natural maps into the constructed covered power family correspond to these
relations. Both whole inverse laws, arbitrary natural parameter substitution,
and the ambient membership interpretation are constructed. Existence of
enumerations is used only to prove existence of transported enumerations;
no enumeration, representative, or inverse is selected from that proof.

On small argument families every stable relation has an independently
constructed truth-subtype cover, even when its parameters are larger.
For larger arguments the cover condition remains explicit. These results
do not assert collection, arbitrary inverse-image closure, or a universal
small-map package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open CoveredFuturePowerFamilies
open PowerClassPresheafBaseChange

universe u v w t s
variable {D : Type u} [Category.{u} D]

def product (B : D ⥤ Type w) (A : D ⥤ Type v) : D ⥤ Type (max w v) where
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

structure StablePredicate (F : D ⥤ Type v) where
  holds : F.Elements → Prop
  closed : ∀ {first second} (_step : first ⟶ second), holds first → holds second

namespace StablePredicate

theorem ext {F : D ⥤ Type v} (first second : StablePredicate F)
    (same : ∀ point, first.holds point ↔ second.holds point) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun point => propext (same point)
      cases predicates
      rfl

end StablePredicate

variable (B : D ⥤ Type w) (A : D ⥤ Type v)

def firstProjection : NaturalHom (product B A) B where
  app _ pair := pair.1
  naturality _ _ := rfl

def secondProjection : NaturalHom (product B A) A where
  app _ pair := pair.2
  naturality _ _ := rfl

def pair {F : D ⥤ Type t} (first : NaturalHom F B) (second : NaturalHom F A) :
    NaturalHom F (product B A) where
  app point value := (first.app point value, second.app point value)
  naturality step value := Prod.ext (first.naturality step value) (second.naturality step value)

def productHomEquiv (F : D ⥤ Type t) :
    NaturalHom F (product B A) ≃ (NaturalHom F B × NaturalHom F A) where
  toFun operation := (operation.comp (firstProjection B A), operation.comp (secondProjection B A))
  invFun maps := pair B A maps.1 maps.2
  left_inv operation := by
    apply NaturalHom.ext
    intro point value
    rfl
  right_inv maps := by
    apply Prod.ext
    · apply NaturalHom.ext
      intro point value
      rfl
    · apply NaturalHom.ext
      intro point value
      rfl

/-- The cover specifies actual small receipts for all future related
arguments of one retained parameter. Multiplicity is not discarded from
the authored enumeration data. -/
structure RelationEnumeration (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point) where
  Carrier : Future.Objects point → Type u
  value : (future : Future.Objects point) → Carrier future → A.obj future.1
  covered : ∀ future argument,
    predicate.holds ⟨future.1, (B.map future.2 parameter, argument)⟩ ↔
      ∃ code, value future code = argument

structure CoveredRelation where
  predicate : StablePredicate (product B A)
  covered : ∀ point parameter, Nonempty (RelationEnumeration B A predicate point parameter)

namespace CoveredRelation

theorem ext (first second : CoveredRelation B A)
    (same : ∀ point, first.predicate.holds point ↔ second.predicate.holds point) : first = second := by
  cases first with
  | mk first firstCover =>
    cases second with
    | mk second secondCover =>
      have predicates := StablePredicate.ext first second same
      cases predicates
      rfl

end CoveredRelation

def relationPredicate (predicate : StablePredicate (product B A))
    (point : D) (parameter : B.obj point) : Predicate A point where
  holds argument := predicate.holds ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩
  closed {first second} step available := by
    have parameterEq : B.map step.1.1 (B.map first.1.2 parameter) = B.map second.1.2 parameter := by
      have triangle := congrArg (fun arrow => B.map arrow parameter) step.1.2
      exact (B.map_comp_apply first.1.2 step.1.1 parameter).symm.trans triangle
    let movement := CategoryOfElements.homMk (F := product B A)
      ⟨first.1.1, (B.map first.1.2 parameter, first.2)⟩
      ⟨second.1.1, (B.map second.1.2 parameter, second.2)⟩ step.1.1 (Prod.ext parameterEq step.2)
    exact predicate.closed movement available

def RelationEnumeration.toEnumeration {predicate : StablePredicate (product B A)}
    {point : D} {parameter : B.obj point}
    (enumeration : RelationEnumeration B A predicate point parameter) :
    Enumeration (relationPredicate B A predicate point parameter) where
  Carrier := enumeration.Carrier
  value := enumeration.value
  covered := enumeration.covered

def classifier (relation : CoveredRelation B A) : NaturalHom B (family A) where
  app point parameter := ⟨relationPredicate B A relation.predicate point parameter, by
    obtain ⟨enumeration⟩ := relation.covered point parameter
    exact ⟨enumeration.toEnumeration B A⟩⟩
  naturality {first second} step parameter := by
    apply Subtype.ext
    apply Predicate.ext
    intro argument
    change relation.predicate.holds ⟨argument.1.1, (B.map (step ≫ argument.1.2) parameter, argument.2)⟩ ↔
      relation.predicate.holds ⟨argument.1.1, (B.map argument.1.2 (B.map step parameter), argument.2)⟩
    rw [B.map_comp_apply]

def classifiedPredicate (operation : NaturalHom B (family A)) : StablePredicate (product B A) where
  holds point := (operation.app point.1 point.2.1).val.holds (current A point.1 point.2.2)
  closed {first second} step available := by
    have parameterEq : B.map step.1 first.2.1 = second.2.1 := congrArg Prod.fst step.2
    have argumentEq : A.map step.1 first.2.2 = second.2.2 := congrArg Prod.snd step.2
    let future : Arguments A first.1 := ⟨⟨second.1, step.1⟩, second.2.2⟩
    have movement : current A first.1 first.2.2 ⟶ future :=
      ⟨⟨step.1, Category.id_comp _⟩, argumentEq⟩
    have later := (operation.app first.1 first.2.1).val.closed movement available
    have same := operation.naturality step.1 first.2.1
    have truth := congrArg (fun power : Power A second.1 =>
      power.val.holds (current A second.1 second.2.2)) same
    change (operation.app first.1 first.2.1).val.holds
      ⟨⟨second.1, step.1 ≫ 𝟙 second.1⟩, second.2.2⟩ =
        (operation.app second.1 (B.map step.1 first.2.1)).val.holds (current A second.1 second.2.2) at truth
    rw [Category.comp_id, parameterEq] at truth
    exact truth ▸ later

theorem classified_future (operation : NaturalHom B (family A))
    (point : D) (parameter : B.obj point) (argument : Arguments A point) :
    (operation.app point parameter).val.holds argument ↔
      (classifiedPredicate B A operation).holds
        ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩ := by
  have same := operation.naturality argument.1.2 parameter
  have truth := congrArg (fun power : Power A argument.1.1 =>
    power.val.holds (current A argument.1.1 argument.2)) same
  change (operation.app point parameter).val.holds
    ⟨⟨argument.1.1, argument.1.2 ≫ 𝟙 argument.1.1⟩, argument.2⟩ =
      (operation.app argument.1.1 (B.map argument.1.2 parameter)).val.holds
        (current A argument.1.1 argument.2) at truth
  rw [Category.comp_id] at truth
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact iff_of_eq truth

def classifiedEnumeration (operation : NaturalHom B (family A))
    (point : D) (parameter : B.obj point)
    (enumeration : Enumeration (operation.app point parameter).val) :
    RelationEnumeration B A (classifiedPredicate B A operation) point parameter where
  Carrier := enumeration.Carrier
  value := enumeration.value
  covered future argument :=
    (classified_future B A operation point parameter ⟨future, argument⟩).symm.trans
      (enumeration.covered future argument)

def classifiedRelation (operation : NaturalHom B (family A)) : CoveredRelation B A where
  predicate := classifiedPredicate B A operation
  covered point parameter := by
    obtain ⟨enumeration⟩ := (operation.app point parameter).property
    exact ⟨classifiedEnumeration B A operation point parameter enumeration⟩

theorem classified_classifier (relation : CoveredRelation B A) :
    classifiedRelation B A (classifier B A relation) = relation := by
  apply CoveredRelation.ext
  rintro ⟨point, parameter, argument⟩
  change relation.predicate.holds ⟨point, (B.map (𝟙 point) parameter, argument)⟩ ↔
    relation.predicate.holds ⟨point, (parameter, argument)⟩
  rw [B.map_id_apply]

theorem classifier_classified (operation : NaturalHom B (family A)) :
    classifier B A (classifiedRelation B A operation) = operation := by
  apply NaturalHom.ext
  intro point parameter
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  exact (classified_future B A operation point parameter argument).symm

def classifierEquiv : NaturalHom B (family A) ≃ CoveredRelation B A where
  toFun := classifiedRelation B A
  invFun := classifier B A
  left_inv := classifier_classified B A
  right_inv := classified_classifier B A

theorem classifier_future (relation : CoveredRelation B A)
    (point : D) (parameter : B.obj point) (argument : Arguments A point) :
    ((classifier B A relation).app point parameter).val.holds argument ↔
      relation.predicate.holds ⟨argument.1.1, (B.map argument.1.2 parameter, argument.2)⟩ := Iff.rfl

def identityHom (F : D ⥤ Type v) : NaturalHom F F where
  app _ := id
  naturality _ _ := rfl

variable {B' : D ⥤ Type t} {B'' : D ⥤ Type s}

def productParameter (operation : NaturalHom B' B) : NaturalHom (product B' A) (product B A) where
  app point pair := (operation.app point pair.1, pair.2)
  naturality step pair := Prod.ext (operation.naturality step pair.1) rfl

def pullbackStable {first : D ⥤ Type v} {second : D ⥤ Type w}
    (operation : NaturalHom first second) (predicate : StablePredicate second) : StablePredicate first where
  holds point := predicate.holds ⟨point.1, operation.app point.1 point.2⟩
  closed {first second} step available :=
    predicate.closed ⟨step.1, (operation.naturality step.1 first.2).trans
      (congrArg (operation.app second.1) step.2)⟩ available

def substitutedPredicate (operation : NaturalHom B' B) (predicate : StablePredicate (product B A)) :
    StablePredicate (product B' A) := pullbackStable (productParameter B A operation) predicate

def substituteEnumeration (operation : NaturalHom B' B)
    {predicate : StablePredicate (product B A)} {point : D} {parameter : B'.obj point}
    (enumeration : RelationEnumeration B A predicate point (operation.app point parameter)) :
    RelationEnumeration B' A (substitutedPredicate B A operation predicate) point parameter where
  Carrier := enumeration.Carrier
  value := enumeration.value
  covered future argument := by
    change predicate.holds ⟨future.1, (operation.app future.1 (B'.map future.2 parameter), argument)⟩ ↔ _
    rw [← operation.naturality]
    exact enumeration.covered future argument

def parameterSubstitution (operation : NaturalHom B' B) (relation : CoveredRelation B A) :
    CoveredRelation B' A where
  predicate := substitutedPredicate B A operation relation.predicate
  covered point parameter := by
    obtain ⟨enumeration⟩ := relation.covered point (operation.app point parameter)
    exact ⟨substituteEnumeration B A operation enumeration⟩

theorem classifier_parameter_substitution (substitution : NaturalHom B' B)
    (relation : CoveredRelation B A) :
    classifier B' A (parameterSubstitution B A substitution relation) =
      substitution.comp (classifier B A relation) := by
  apply NaturalHom.ext
  intro point parameter
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  change relation.predicate.holds
      ⟨argument.1.1, (substitution.app argument.1.1 (B'.map argument.1.2 parameter), argument.2)⟩ ↔
    relation.predicate.holds ⟨argument.1.1, (B.map argument.1.2 (substitution.app point parameter), argument.2)⟩
  rw [substitution.naturality]

theorem classified_parameter_substitution (operation : NaturalHom B (family A))
    (substitution : NaturalHom B' B) :
    classifiedRelation B' A (substitution.comp operation) =
      parameterSubstitution B A substitution (classifiedRelation B A operation) := by
  apply CoveredRelation.ext
  intro point
  exact Iff.rfl

theorem parameterSubstitution_identity (relation : CoveredRelation B A) :
    parameterSubstitution B A (identityHom B) relation = relation := by
  apply CoveredRelation.ext
  intro point
  exact Iff.rfl

theorem parameterSubstitution_comp (first : NaturalHom B'' B') (second : NaturalHom B' B)
    (relation : CoveredRelation B A) :
    parameterSubstitution B' A first (parameterSubstitution B A second relation) =
      parameterSubstitution B A (first.comp second) relation := by
  apply CoveredRelation.ext
  intro point
  exact Iff.rfl

/-- An authored enumeration transports along a future arrow by retaining
its receipts at the complete composite future index. -/
def restrictEnumeration {predicate : StablePredicate (product B A)}
    {first second : D} (step : first ⟶ second) {parameter : B.obj first}
    (enumeration : RelationEnumeration B A predicate first parameter) :
    RelationEnumeration B A predicate second (B.map step parameter) where
  Carrier future := enumeration.Carrier ⟨future.1, step ≫ future.2⟩
  value future := enumeration.value ⟨future.1, step ≫ future.2⟩
  covered future argument := by
    have comparison := enumeration.covered ⟨future.1, step ≫ future.2⟩ argument
    rw [B.map_comp_apply] at comparison
    exact comparison

theorem restrictEnumeration_value {predicate : StablePredicate (product B A)}
    {first second : D} (step : first ⟶ second) {parameter : B.obj first}
    (enumeration : RelationEnumeration B A predicate first parameter)
    (future : Future.Objects second)
    (code : (restrictEnumeration B A step enumeration).Carrier future) :
    (restrictEnumeration B A step enumeration).value future code =
      enumeration.value ⟨future.1, step ≫ future.2⟩ code := rfl

/-- All admitted power elements are parameters of the actual ambient
membership relation. Its cover proof is inherited through the proved
parameterized classification, not through an assumed membership axiom. -/
def membershipRelation : CoveredRelation (family A) A :=
  classifiedRelation (family A) A (identityHom (family A))

theorem membership_current (point : D) (parameter : Power A point) (argument : A.obj point) :
    (membershipRelation A).predicate.holds ⟨point, (parameter, argument)⟩ ↔
      parameter.val.holds (current A point argument) := Iff.rfl

theorem membership_future (point : D) (parameter : Power A point) (argument : Arguments A point) :
    (membershipRelation A).predicate.holds
        ⟨argument.1.1, (restrictPower A argument.1.2 parameter, argument.2)⟩ ↔
      parameter.val.holds argument := by
  exact (classified_future (family A) A (identityHom (family A)) point parameter argument).symm

theorem membership_classifier : classifier (family A) A (membershipRelation A) = identityHom (family A) :=
  classifier_classified (family A) A (identityHom (family A))

theorem universal_membership (operation : NaturalHom B (family A)) :
    parameterSubstitution (family A) A operation (membershipRelation A) = classifiedRelation B A operation := by
  apply CoveredRelation.ext
  intro point
  exact Iff.rfl

def forget (relation : CoveredRelation B A) : StablePredicate (product B A) := relation.predicate

theorem forget_injective : Function.Injective (forget B A) := by
  intro first second same
  apply CoveredRelation.ext
  intro point
  exact iff_of_eq (congrArg (fun predicate : StablePredicate (product B A) => predicate.holds point) same)

/-- A covered relation which holds on every present argument supplies a
small surjection onto the whole argument fibre. This is a necessary
strength condition; no inverse of that surjection is constructed. -/
theorem small_surjection_of_full_relation (relation : CoveredRelation B A)
    (point : D) (parameter : B.obj point)
    (full : ∀ argument : A.obj point, relation.predicate.holds ⟨point, (parameter, argument)⟩) :
    ∃ Carrier : Type u, ∃ value : Carrier → A.obj point, Function.Surjective value := by
  obtain ⟨enumeration⟩ := relation.covered point parameter
  refine ⟨enumeration.Carrier ⟨point, 𝟙 point⟩, enumeration.value ⟨point, 𝟙 point⟩, ?_⟩
  intro argument
  have truth := full argument
  have comparison := enumeration.covered ⟨point, 𝟙 point⟩ argument
  rw [B.map_id_apply] at comparison
  exact comparison.mp truth

section SmallArguments

variable (parameters : D ⥤ Type w) (arguments : D ⥤ Type u)

def smallRelationEnumeration (predicate : StablePredicate (product parameters arguments))
    (point : D) (parameter : parameters.obj point) :
    RelationEnumeration parameters arguments predicate point parameter where
  Carrier future := {argument : arguments.obj future.1 //
    predicate.holds ⟨future.1, (parameters.map future.2 parameter, argument)⟩}
  value _ code := code.val
  covered _ _ := ⟨fun truth => ⟨⟨_, truth⟩, rfl⟩, fun ⟨code, same⟩ => same ▸ code.property⟩

def smallRelation (predicate : StablePredicate (product parameters arguments)) :
    CoveredRelation parameters arguments where
  predicate := predicate
  covered point parameter := ⟨smallRelationEnumeration parameters arguments predicate point parameter⟩

def smallForgetEquiv : CoveredRelation parameters arguments ≃ StablePredicate (product parameters arguments) where
  toFun := forget parameters arguments
  invFun := smallRelation parameters arguments
  left_inv relation := by
    apply CoveredRelation.ext
    intro point
    exact Iff.rfl
  right_inv _ := rfl

/-- Larger parameter fibres introduce no additional cover obligation when
the actual argument fibres are small. -/
def smallClassifierEquiv :
    NaturalHom parameters (family arguments) ≃ StablePredicate (product parameters arguments) :=
  (classifierEquiv parameters arguments).trans (smallForgetEquiv parameters arguments)

end SmallArguments

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
