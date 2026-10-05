import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange

/-!
# Power families retaining all future arguments

A power-family element is a proposition-valued subset of all future
arguments that is closed under their actual restriction morphisms. Its
restriction precomposes the retained future arrow. Compatible sections of
this family classify stable subsets of the original displayed family.

The objects and arrows of the context category, and every argument fibre,
inhabit one small universe. This construction uses full proposition-valued
predicate types. It does not classify arbitrary large small subobjects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies

open CategoryTheory
open PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D]

abbrev Arguments (A : D ⥤ Type u) (point : D) := (Future.domain A point).Elements

structure Predicate (A : D ⥤ Type u) (point : D) where
  holds : Arguments A point → Prop
  closed : ∀ {first second} (_step : first ⟶ second), holds first → holds second

namespace Predicate

variable {A : D ⥤ Type u} {point : D}

theorem ext (first second : Predicate A point)
    (same : ∀ argument, first.holds argument ↔ second.holds argument) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun argument => propext (same argument)
      cases predicates
      rfl

end Predicate

/-- Precomposition retains the later target, the complete composite arrow,
and the actual argument. -/
def futurePrecompose (A : D ⥤ Type u) {first second : D} (step : first ⟶ second) :
    Arguments A second ⥤ Arguments A first where
  obj argument := ⟨⟨argument.1.1, step ≫ argument.1.2⟩, argument.2⟩
  map move := ⟨⟨move.1.1, by rw [Category.assoc, move.1.2]⟩, move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def restrict (A : D ⥤ Type u) {first second : D} (step : first ⟶ second)
    (predicate : Predicate A first) : Predicate A second where
  holds argument := predicate.holds ((futurePrecompose A step).obj argument)
  closed move available := predicate.closed ((futurePrecompose A step).map move) available

theorem restrict_holds (A : D ⥤ Type u) {first second : D} (step : first ⟶ second)
    (predicate : Predicate A first) (argument : Arguments A second) :
    (restrict A step predicate).holds argument ↔
      predicate.holds ⟨⟨argument.1.1, step ≫ argument.1.2⟩, argument.2⟩ := Iff.rfl

theorem restrict_identity (A : D ⥤ Type u) (point : D) (predicate : Predicate A point) :
    restrict A (𝟙 point) predicate = predicate := by
  apply Predicate.ext
  intro argument
  change predicate.holds ⟨⟨argument.1.1, 𝟙 point ≫ argument.1.2⟩, argument.2⟩ ↔ _
  rw [Category.id_comp]
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact Iff.rfl

theorem restrict_comp (A : D ⥤ Type u) {first middle last : D}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (predicate : Predicate A first) :
    restrict A (earlier ≫ later) predicate = restrict A later (restrict A earlier predicate) := by
  apply Predicate.ext
  intro argument
  change predicate.holds ⟨⟨argument.1.1, (earlier ≫ later) ≫ argument.1.2⟩, argument.2⟩ ↔
    predicate.holds ⟨⟨argument.1.1, earlier ≫ (later ≫ argument.1.2)⟩, argument.2⟩
  rw [Category.assoc]

def family (A : D ⥤ Type u) : D ⥤ Type u where
  obj point := Predicate A point
  map step := TypeCat.ofHom (restrict A step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact restrict_identity A point
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    exact restrict_comp A first second

def current (A : D ⥤ Type u) (point : D) (argument : A.obj point) : Arguments A point :=
  ⟨⟨point, 𝟙 point⟩, argument⟩

structure StablePredicate (A : D ⥤ Type u) where
  holds : A.Elements → Prop
  closed : ∀ {first second} (_step : first ⟶ second), holds first → holds second

namespace StablePredicate

variable {A : D ⥤ Type u}

theorem ext (first second : StablePredicate A)
    (same : ∀ argument, first.holds argument ↔ second.holds argument) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun argument => propext (same argument)
      cases predicates
      rfl

end StablePredicate

def classify (A : D ⥤ Type u) (predicate : StablePredicate A) : (family A).sections :=
  ⟨fun point => {
    holds argument := predicate.holds ⟨argument.1.1, argument.2⟩
    closed move available := predicate.closed ((Future.argument A point).map move) available }, by
    intro first second step
    apply Predicate.ext
    intro argument
    exact Iff.rfl⟩

/-- Current truth is read from the whole natural power-family section. -/
def classifiedPredicate (A : D ⥤ Type u) (term : (family A).sections) : StablePredicate A where
  holds argument := (term.val argument.1).holds (current A argument.1 argument.2)
  closed {first second} step available := by
    let future : Arguments A first.1 := ⟨⟨second.1, step.1⟩, second.2⟩
    have movement : current A first.1 first.2 ⟶ future :=
      ⟨⟨step.1, Category.id_comp _⟩, step.2⟩
    have later := (term.val first.1).closed movement available
    have same := term.property step.1
    have truth := congrArg (fun predicate : Predicate A second.1 =>
      predicate.holds (current A second.1 second.2)) same
    change (term.val first.1).holds
      ⟨⟨second.1, step.1 ≫ 𝟙 second.1⟩, second.2⟩ =
        (term.val second.1).holds (current A second.1 second.2) at truth
    rw [Category.comp_id] at truth
    exact truth ▸ later

theorem classified_classify (A : D ⥤ Type u) (predicate : StablePredicate A) :
    classifiedPredicate A (classify A predicate) = predicate := by
  apply StablePredicate.ext
  intro argument
  exact Iff.rfl

theorem classify_classified (A : D ⥤ Type u) (term : (family A).sections) :
    classify A (classifiedPredicate A term) = term := by
  apply Subtype.ext
  funext point
  apply Predicate.ext
  intro argument
  have same := term.property argument.1.2
  have truth := congrArg (fun predicate : Predicate A argument.1.1 =>
    predicate.holds (current A argument.1.1 argument.2)) same
  change (term.val point).holds
    ⟨⟨argument.1.1, argument.1.2 ≫ 𝟙 argument.1.1⟩, argument.2⟩ =
      (term.val argument.1.1).holds (current A argument.1.1 argument.2) at truth
  rw [Category.comp_id] at truth
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact (iff_of_eq truth).symm

/-- Stable displayed subsets and compatible contextual power sections have
constructed inverse interpretations. -/
def classifierEquiv (A : D ⥤ Type u) : StablePredicate A ≃ (family A).sections where
  toFun := classify A
  invFun := classifiedPredicate A
  left_inv := classified_classify A
  right_inv := classify_classified A

theorem classify_future (A : D ⥤ Type u) (predicate : StablePredicate A)
    (point : D) (argument : Arguments A point) :
    ((classifierEquiv A predicate).val point).holds argument ↔
      predicate.holds ⟨argument.1.1, argument.2⟩ := Iff.rfl

theorem classified_future (A : D ⥤ Type u) (term : (family A).sections)
    (point : D) (argument : Arguments A point) :
    (term.val point).holds argument ↔
      (classifiedPredicate A term).holds ⟨argument.1.1, argument.2⟩ := by
  have same := congrArg (fun termValue : (family A).sections => termValue.val point)
    (classify_classified A term)
  rw [← same]
  exact Iff.rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies
