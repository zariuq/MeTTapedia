import Mettapedia.CategoryTheory.InternalCategory

/-!
# Internal categories from seven local arrow diagrams

Four endpoint diagrams supply the complete composable-pair operation. Two
unit diagrams and one associativity diagram on the actual composable-triple
object earn the full category laws at every generalized context. The latter
is derived by universal factorization, rather than required as a model field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryLocalDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (C : Type u) [Category.{v} C] [HasPullbacks C]

structure Endpoints extends InternalGraph C where
  unit : vertex ⟶ edge
  composition : toInternalGraph.Composable ⟶ edge
  unit_source : unit ≫ source = 𝟙 vertex
  unit_target : unit ≫ target = 𝟙 vertex
  composition_source : composition ≫ source = pullback.fst target source ≫ source
  composition_target : composition ≫ target = pullback.snd target source ≫ target

variable {C} (operations : Endpoints C)

abbrev compose {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) : X ⟶ operations.edge :=
  operations.toInternalGraph.composeWith operations.composition first second matching

@[reassoc] theorem compose_source {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    compose operations first second matching ≫ operations.source = first ≫ operations.source := by
  rw [compose, InternalGraph.composeWith, Category.assoc, operations.composition_source,
    ← Category.assoc, pullback.lift_fst]

@[reassoc] theorem compose_target {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    compose operations first second matching ≫ operations.target = second ≫ operations.target := by
  rw [compose, InternalGraph.composeWith, Category.assoc, operations.composition_target,
    ← Category.assoc, pullback.lift_snd]

theorem compose_precompose {X Y : C} (stage : X ⟶ Y) (first second : Y ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    stage ≫ compose operations first second matching =
      compose operations (stage ≫ first) (stage ≫ second)
        (by simpa only [Category.assoc] using congrArg (fun arrow => stage ≫ arrow) matching) := by
  dsimp only [compose, InternalGraph.composeWith]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

theorem compose_congr {X : C} {first first' second second' : X ⟶ operations.edge}
    (firstSame : first = first') (secondSame : second = second')
    (matching : first ≫ operations.target = second ≫ operations.source)
    (matching' : first' ≫ operations.target = second' ≫ operations.source) :
    compose operations first second matching = compose operations first' second' matching' := by
  subst first'
  subst second'
  rfl

def triples : C := pullback
  (pullback.snd operations.target operations.source ≫ operations.target) operations.source

def initialPair : triples operations ⟶ operations.toInternalGraph.Composable :=
  pullback.fst _ _

def first : triples operations ⟶ operations.edge :=
  initialPair operations ≫ pullback.fst _ _

def middle : triples operations ⟶ operations.edge :=
  initialPair operations ≫ pullback.snd _ _

def last : triples operations ⟶ operations.edge := pullback.snd _ _

theorem first_matching : first operations ≫ operations.target = middle operations ≫ operations.source := by
  simp only [first, middle, Category.assoc]
  rw [pullback.condition]

theorem second_matching : middle operations ≫ operations.target = last operations ≫ operations.source := by
  simpa only [middle, initialPair, last, Category.assoc] using
    (pullback.condition (f := pullback.snd operations.target operations.source ≫ operations.target)
      (g := operations.source))

def associateLeft : triples operations ⟶ operations.edge :=
  compose operations (initialPair operations ≫ operations.composition) (last operations) (by
    rw [Category.assoc, operations.composition_target]
    simpa only [middle, Category.assoc] using second_matching operations)

def associateRight : triples operations ⟶ operations.edge :=
  compose operations (first operations)
    (compose operations (middle operations) (last operations) (second_matching operations)) (by
      rw [compose_source]
      exact first_matching operations)

structure Laws : Prop where
  leftUnit : compose operations (operations.source ≫ operations.unit) (𝟙 operations.edge)
    (by simp only [Category.assoc, operations.unit_target, Category.comp_id, Category.id_comp]) = 𝟙 operations.edge
  rightUnit : compose operations (𝟙 operations.edge) (operations.target ≫ operations.unit)
    (by simp only [Category.assoc, operations.unit_source, Category.comp_id, Category.id_comp]) = 𝟙 operations.edge
  associativity : associateLeft operations = associateRight operations

def factor {X : C} (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) : X ⟶ triples operations :=
  pullback.lift (pullback.lift first second firstMatch) third (by
    rw [← Category.assoc, pullback.lift_snd]
    exact secondMatch)

@[simp] theorem factor_initialPair {X : C} (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) :
    factor operations first second third firstMatch secondMatch ≫ initialPair operations =
      pullback.lift first second firstMatch := pullback.lift_fst _ _ _

@[simp] theorem factor_first {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations before middle after firstMatch secondMatch ≫ first operations = before := by
  rw [first, ← Category.assoc, factor_initialPair, pullback.lift_fst]

@[simp] theorem factor_middle {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations before middle after firstMatch secondMatch ≫ InternalCategoryLocalDiagrams.middle operations = middle := by
  rw [InternalCategoryLocalDiagrams.middle, ← Category.assoc, factor_initialPair, pullback.lift_snd]

@[simp] theorem factor_last {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations before middle after firstMatch secondMatch ≫ last operations = after := pullback.lift_snd _ _ _

theorem associativity (laws : Laws operations) {X : C} (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) :
    compose operations (compose operations first second firstMatch) third
      (by rw [compose_target]; exact secondMatch) =
    compose operations first (compose operations second third secondMatch)
      (by rw [compose_source]; exact firstMatch) := by
  let stage := factor operations first second third firstMatch secondMatch
  have localLaw := congrArg (fun arrow => stage ≫ arrow) laws.associativity
  have firstRead : stage ≫ (initialPair operations ≫ operations.composition) =
      compose operations first second firstMatch := by
    rw [← Category.assoc, factor_initialPair]
    rfl
  have innerRead : stage ≫ compose operations (middle operations) (last operations)
      (second_matching operations) = compose operations second third secondMatch :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations (factor_middle operations first second third firstMatch secondMatch)
        (factor_last operations first second third firstMatch secondMatch) _ _)
  have leftRead : stage ≫ associateLeft operations =
      compose operations (compose operations first second firstMatch) third
        (by rw [compose_target]; exact secondMatch) :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations firstRead (factor_last operations first second third firstMatch secondMatch) _ _)
  have rightRead : stage ≫ associateRight operations =
      compose operations first (compose operations second third secondMatch)
        (by rw [compose_source]; exact firstMatch) :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations (factor_first operations first second third firstMatch secondMatch) innerRead _ _)
  exact leftRead.symm.trans (localLaw.trans rightRead)

def category (laws : Laws operations) : InternalCategory C where
  toInternalGraph := operations.toInternalGraph
  unit := operations.unit
  composition := operations.composition
  unit_source := operations.unit_source
  unit_target := operations.unit_target
  composition_source := operations.composition_source
  composition_target := operations.composition_target
  unit_left := laws.leftUnit
  unit_right := laws.rightUnit
  associativity := fun _ first second third firstMatch secondMatch =>
    associativity operations laws first second third firstMatch secondMatch

end Mettapedia.CategoryTheory.InternalCategoryLocalDiagrams
