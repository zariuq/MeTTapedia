import Mettapedia.TypeTheory.ContextualImageFactorization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

/-!
# Constructed contextual equivalence quotients and Heyting quantifiers

Every restriction-stable family of equivalence relations has its actual
pointwise quotient, quotient projection and effective kernel. Quotient
elimination constructs every compatible natural factor and proves uniqueness.

Stable predicates admit inverse image, existential image and universal
image. Universal image quantifies over all future worlds and actual arrows,
so it remains stable under restriction. The two order adjunctions and literal
pullback comparisons are proved on these actual constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPresheafExactness

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (A : D ⥤ Type v)

structure StableEquivalence where
  relation : ∀ point, Setoid (A.obj point)
  restricted : ∀ {first second} (step : first ⟶ second) {left right : A.obj first},
    (relation first).r left right → (relation second).r (A.map step left) (A.map step right)

namespace StableEquivalence

variable (relation : StableEquivalence A)

def quotient : D ⥤ Type v where
  obj point := Quotient (relation.relation point)
  map step := TypeCat.ofHom
    (Quotient.map (A.map step) (fun {_ _} same => relation.restricted step same))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk _) (A.map_id_apply point argument)
  map_comp {first _middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk (relation.relation last)) (A.map_comp_apply earlier later argument)

def projection : NaturalHom A (quotient A relation) where
  app point := Quotient.mk (relation.relation point)
  naturality _ _ := rfl

theorem projection_surjective (point : D) : Function.Surjective ((projection A relation).app point) := by
  intro value
  exact Quotient.inductionOn value fun argument => ⟨argument, rfl⟩

theorem effective_kernel (point : D) (first second : A.obj point) :
    (projection A relation).app point first = (projection A relation).app point second ↔
      (relation.relation point).r first second := ⟨Quotient.exact, Quotient.sound⟩

def respects {B : D ⥤ Type w} (operation : NaturalHom A B) : Prop :=
  ∀ point {first second}, (relation.relation point).r first second →
    operation.app point first = operation.app point second

def descend {B : D ⥤ Type w} (operation : NaturalHom A B)
    (compatible : respects A relation operation) : NaturalHom (quotient A relation) B where
  app point := Quotient.lift (operation.app point) (fun _ _ same => compatible point same)
  naturality step value := Quotient.inductionOn value fun argument => operation.naturality step argument

theorem descend_projection {B : D ⥤ Type w} (operation : NaturalHom A B)
    (compatible : respects A relation operation) :
    (projection A relation).comp (descend A relation operation compatible) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem descend_unique {B : D ⥤ Type w} (operation : NaturalHom A B)
    (compatible : respects A relation operation) (other : NaturalHom (quotient A relation) B)
    (factorization : (projection A relation).comp other = operation) :
    other = descend A relation operation compatible := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A B => map.app point argument) factorization

theorem quotient_universal {B : D ⥤ Type w} (operation : NaturalHom A B)
    (compatible : respects A relation operation) :
    ∃! factor : NaturalHom (quotient A relation) B,
      (projection A relation).comp factor = operation :=
  ⟨descend A relation operation compatible, descend_projection A relation operation compatible,
    fun other factors => descend_unique A relation operation compatible other factors⟩

def relationObject : D ⥤ Type v where
  obj point := {pair : A.obj point × A.obj point // (relation.relation point).r pair.1 pair.2}
  map step := TypeCat.ofHom fun receipt =>
    ⟨(A.map step receipt.val.1, A.map step receipt.val.2), relation.restricted step receipt.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Subtype.ext (Prod.ext (A.map_id_apply point receipt.val.1) (A.map_id_apply point receipt.val.2))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Subtype.ext (Prod.ext (A.map_comp_apply earlier later receipt.val.1)
      (A.map_comp_apply earlier later receipt.val.2))

def first : NaturalHom (relationObject A relation) A where
  app _ receipt := receipt.val.1
  naturality _ _ := rfl

def second : NaturalHom (relationObject A relation) A where
  app _ receipt := receipt.val.2
  naturality _ _ := rfl

def relationToKernel : NaturalHom (relationObject A relation)
    (ContextualKernelQuotients.kernelPair (projection A relation)) where
  app point receipt := ⟨receipt.val, (effective_kernel A relation point receipt.val.1 receipt.val.2).mpr
    receipt.property⟩
  naturality _ _ := Subtype.ext rfl

def kernelToRelation : NaturalHom (ContextualKernelQuotients.kernelPair (projection A relation))
    (relationObject A relation) where
  app point receipt := ⟨receipt.val, (effective_kernel A relation point receipt.val.1 receipt.val.2).mp
    receipt.property⟩
  naturality _ _ := Subtype.ext rfl

theorem relation_kernel_left (point : D) (receipt : (relationObject A relation).obj point) :
    (kernelToRelation A relation).app point ((relationToKernel A relation).app point receipt) = receipt :=
  Subtype.ext rfl

theorem relation_kernel_right (point : D)
    (receipt : (ContextualKernelQuotients.kernelPair (projection A relation)).obj point) :
    (relationToKernel A relation).app point ((kernelToRelation A relation).app point receipt) = receipt :=
  Subtype.ext rfl

def relationKernelEquiv (point : D) : (relationObject A relation).obj point ≃
    (ContextualKernelQuotients.kernelPair (projection A relation)).obj point where
  toFun := (relationToKernel A relation).app point
  invFun := (kernelToRelation A relation).app point
  left_inv := relation_kernel_left A relation point
  right_inv := relation_kernel_right A relation point

theorem relationToKernel_first : (relationToKernel A relation).comp
    (ContextualKernelQuotients.kernelFirst (projection A relation)) = first A relation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem relationToKernel_second : (relationToKernel A relation).comp
    (ContextualKernelQuotients.kernelSecond (projection A relation)) = second A relation := by
  apply NaturalHom.ext
  intro _ _
  rfl

end StableEquivalence

/-- A monic relation presentation and the actual equivalence laws of its
image. The record does not contain a quotient or a quotient inverse. -/
structure MonicEquivalence {A : D ⥤ Type v} (R : D ⥤ Type w) where
  inclusion : NaturalHom R (product A A)
  injective : ∀ point, Function.Injective (inclusion.app point)
  laws : ∀ point, Equivalence (fun first second : A.obj point =>
    ∃ receipt, inclusion.app point receipt = (first, second))

namespace MonicEquivalence

variable {A : D ⥤ Type v} {R : D ⥤ Type w} (presentation : MonicEquivalence (A := A) R)

def relation : StableEquivalence A where
  relation point :=
    { r := fun first second => ∃ receipt, presentation.inclusion.app point receipt = (first, second)
      iseqv := presentation.laws point }
  restricted {first second} step {_ _} available := by
    obtain ⟨receipt, same⟩ := available
    exact ⟨R.map step receipt, (presentation.inclusion.naturality step receipt).symm.trans
      (congrArg ((product A A).map step) same)⟩

def left : NaturalHom R A := presentation.inclusion.comp (firstProjection A A)

def right : NaturalHom R A := presentation.inclusion.comp (secondProjection A A)

theorem image_effective (point : D) (first second : A.obj point) :
    (StableEquivalence.projection A presentation.relation).app point first =
      (StableEquivalence.projection A presentation.relation).app point second ↔
        ∃ receipt, presentation.inclusion.app point receipt = (first, second) :=
  StableEquivalence.effective_kernel A presentation.relation point first second

theorem equalizes : presentation.left.comp (StableEquivalence.projection A presentation.relation) =
    presentation.right.comp (StableEquivalence.projection A presentation.relation) := by
  apply NaturalHom.ext
  intro point receipt
  exact (presentation.image_effective point _ _).mpr ⟨receipt, Prod.ext rfl rfl⟩

theorem compatible_iff {B : D ⥤ Type z} (operation : NaturalHom A B) :
    StableEquivalence.respects A presentation.relation operation ↔
      presentation.left.comp operation = presentation.right.comp operation := by
  constructor
  · intro compatible
    apply NaturalHom.ext
    intro point receipt
    exact compatible point ⟨receipt, Prod.ext rfl rfl⟩
  · intro equalizes point first second available
    obtain ⟨receipt, same⟩ := available
    have law := congrArg (fun map : NaturalHom R B => map.app point receipt) equalizes
    exact (congrArg (operation.app point) (congrArg Prod.fst same)).symm.trans
      (law.trans (congrArg (operation.app point) (congrArg Prod.snd same)))

/-- Quotient elimination, rather than selection of a relation receipt,
constructs every natural coequalizing map. -/
theorem quotient_universal {B : D ⥤ Type z} (operation : NaturalHom A B)
    (equalizes : presentation.left.comp operation = presentation.right.comp operation) :
    ∃! factor : NaturalHom (StableEquivalence.quotient A presentation.relation) B,
      (StableEquivalence.projection A presentation.relation).comp factor = operation :=
  StableEquivalence.quotient_universal A presentation.relation operation
    ((presentation.compatible_iff operation).mpr equalizes)

end MonicEquivalence

def Included {A : D ⥤ Type v} (first second : StablePredicate A) : Prop :=
  ∀ point, first.holds point → second.holds point

instance stablePredicateOrder {A : D ⥤ Type v} : PartialOrder (StablePredicate A) where
  le := Included
  le_refl _ := fun _ available => available
  le_trans _ _ _ first second := fun point available => second point (first point available)
  le_antisymm first second forward backward :=
    StablePredicate.ext first second (fun point => ⟨forward point, backward point⟩)

def conjunction {A : D ⥤ Type v} (first second : StablePredicate A) : StablePredicate A where
  holds point := first.holds point ∧ second.holds point
  closed step available := ⟨first.closed step available.1, second.closed step available.2⟩

def inverseImage {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)
    (predicate : StablePredicate B) : StablePredicate A where
  holds point := predicate.holds ⟨point.1, operation.app point.1 point.2⟩
  closed {first second} step available := predicate.closed
    (CategoryOfElements.homMk (F := B) _ _ step.1
      ((operation.naturality step.1 first.2).trans (congrArg (operation.app second.1) step.2))) available

def existsImage {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)
    (predicate : StablePredicate A) : StablePredicate B where
  holds point := ∃ argument : A.obj point.1,
    operation.app point.1 argument = point.2 ∧ predicate.holds ⟨point.1, argument⟩
  closed {first second} step available := by
    obtain ⟨argument, same, holds⟩ := available
    exact ⟨A.map step.1 argument,
      (operation.naturality step.1 argument).symm.trans
        ((congrArg (B.map step.1) same).trans step.2),
      predicate.closed (CategoryOfElements.homMk (F := A) _ _ step.1 rfl) holds⟩

/-- All future arrows are necessary for a stable universal quantifier. -/
def forallImage {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)
    (predicate : StablePredicate A) : StablePredicate B where
  holds point := ∀ (future : D) (arrival : point.1 ⟶ future) (argument : A.obj future),
    operation.app future argument = B.map arrival point.2 → predicate.holds ⟨future, argument⟩
  closed {first second} step available := by
    intro future arrival argument same
    exact available future (step.1 ≫ arrival) argument
      (same.trans ((congrArg (B.map arrival) step.2).symm.trans
        (B.map_comp_apply step.1 arrival first.2).symm))

theorem exists_inverse_adjunction {A : D ⥤ Type v} {B : D ⥤ Type w}
    (operation : NaturalHom A B) (first : StablePredicate A) (second : StablePredicate B) :
    Included (existsImage operation first) second ↔ Included first (inverseImage operation second) := by
  constructor
  · intro bound point available
    exact bound ⟨point.1, operation.app point.1 point.2⟩ ⟨point.2, rfl, available⟩
  · intro bound point available
    obtain ⟨argument, same, holds⟩ := available
    have truth := bound ⟨point.1, argument⟩ holds
    change second.holds ⟨point.1, operation.app point.1 argument⟩ at truth
    change second.holds ⟨point.1, point.2⟩
    exact same ▸ truth

theorem inverse_forall_adjunction {A : D ⥤ Type v} {B : D ⥤ Type w}
    (operation : NaturalHom A B) (first : StablePredicate B) (second : StablePredicate A) :
    Included (inverseImage operation first) second ↔ Included first (forallImage operation second) := by
  constructor
  · intro bound point available future arrival argument same
    have transported := first.closed
      (CategoryOfElements.homMk (F := B) point ⟨future, B.map arrival point.2⟩ arrival rfl) available
    apply bound ⟨future, argument⟩
    change first.holds ⟨future, operation.app future argument⟩
    exact same.symm ▸ transported
  · intro bound point available
    exact bound ⟨point.1, operation.app point.1 point.2⟩ available point.1 (𝟙 point.1) point.2
      (B.map_id_apply point.1 (operation.app point.1 point.2)).symm

theorem existsInverseGalois {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B) :
    GaloisConnection (existsImage operation) (inverseImage operation) :=
  exists_inverse_adjunction operation

theorem inverseForallGalois {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B) :
    GaloisConnection (inverseImage operation) (forallImage operation) :=
  inverse_forall_adjunction operation

def implication {A : D ⥤ Type v} (antecedent consequent : StablePredicate A) : StablePredicate A where
  holds point := ∀ (future : D) (arrival : point.1 ⟶ future),
    antecedent.holds ⟨future, A.map arrival point.2⟩ → consequent.holds ⟨future, A.map arrival point.2⟩
  closed {first second} step available := by
    intro future arrival holds
    have equality : A.map (step.1 ≫ arrival) first.2 = A.map arrival second.2 :=
      (A.map_comp_apply step.1 arrival first.2).trans (congrArg (A.map arrival) step.2)
    have truth := available future (step.1 ≫ arrival) (equality.symm ▸ holds)
    exact equality ▸ truth

theorem implication_adjunction {A : D ⥤ Type v}
    (first second third : StablePredicate A) :
    Included (conjunction first second) third ↔ Included first (implication second third) := by
  constructor
  · intro bound point available future arrival holds
    exact bound ⟨future, A.map arrival point.2⟩
      ⟨first.closed (CategoryOfElements.homMk (F := A) _ _ arrival rfl) available, holds⟩
  · intro bound point available
    have truth := bound point available.1 point.1 (𝟙 point.1)
      ((A.map_id_apply point.1 point.2).symm ▸ available.2)
    change third.holds ⟨point.1, point.2⟩
    exact (A.map_id_apply point.1 point.2) ▸ truth

theorem exists_frobenius {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)
    (first : StablePredicate A) (second : StablePredicate B) :
    existsImage operation (conjunction first (inverseImage operation second)) =
      conjunction (existsImage operation first) second := by
  apply StablePredicate.ext
  intro point
  constructor
  · rintro ⟨argument, same, available, truth⟩
    refine ⟨⟨argument, same, available⟩, ?_⟩
    change second.holds ⟨point.1, point.2⟩
    exact same ▸ truth
  · rintro ⟨⟨argument, same, available⟩, truth⟩
    refine ⟨argument, same, available, ?_⟩
    change second.holds ⟨point.1, operation.app point.1 argument⟩
    change second.holds ⟨point.1, point.2⟩ at truth
    exact same.symm ▸ truth

theorem exists_pullback {A : D ⥤ Type v} {B : D ⥤ Type w} {C : D ⥤ Type z}
    (operation : NaturalHom A B) (change : NaturalHom C B) (predicate : StablePredicate A) :
    existsImage (pullbackSecond operation change) (inverseImage (pullbackFirst operation change) predicate) =
      inverseImage change (existsImage operation predicate) := by
  apply StablePredicate.ext
  intro point
  constructor
  · rintro ⟨receipt, same, truth⟩
    exact ⟨receipt.val.1, receipt.property.trans (congrArg (change.app point.1) same), truth⟩
  · rintro ⟨argument, same, truth⟩
    exact ⟨⟨(argument, point.2), same⟩, rfl, truth⟩

theorem forall_pullback {A : D ⥤ Type v} {B : D ⥤ Type w} {C : D ⥤ Type z}
    (operation : NaturalHom A B) (change : NaturalHom C B) (predicate : StablePredicate A) :
    forallImage (pullbackSecond operation change) (inverseImage (pullbackFirst operation change) predicate) =
      inverseImage change (forallImage operation predicate) := by
  apply StablePredicate.ext
  intro point
  constructor
  · intro available future arrival argument same
    exact available future arrival
      ⟨(argument, C.map arrival point.2), same.trans (change.naturality arrival point.2)⟩ rfl
  · intro available future arrival receipt same
    exact available future arrival receipt.val.1
      (receipt.property.trans ((congrArg (change.app future) same).trans
        (change.naturality arrival point.2).symm))

end Mettapedia.TypeTheory.ContextualPresheafExactness
