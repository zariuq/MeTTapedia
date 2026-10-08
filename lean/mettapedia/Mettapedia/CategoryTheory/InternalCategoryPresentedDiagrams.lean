import Mettapedia.CategoryTheory.InternalCategoryLocalDiagrams

/-!
# Internal categories from independently presented matching objects

Pair and triple objects retain their own earned pullback universal properties.
Seven finite arrow diagrams derive the complete category laws. The resulting
composition uses the ambient chosen pullback, with both projection readouts
proved through universal factorization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (C : Type u) [Category.{v} C]

structure Endpoints extends InternalGraph C where
  pair : PullbackCone target source
  pairLimit : IsLimit pair
  unit : vertex ⟶ edge
  composition : pair.pt ⟶ edge
  unitSource : unit ≫ source = 𝟙 vertex
  unitTarget : unit ≫ target = 𝟙 vertex
  compositionSource : composition ≫ source = pair.fst ≫ source
  compositionTarget : composition ≫ target = pair.snd ≫ target

variable {C} (operations : Endpoints C)

abbrev pairLift {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) : X ⟶ operations.pair.pt :=
  PullbackCone.IsLimit.lift operations.pairLimit first second matching

abbrev compose {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) : X ⟶ operations.edge :=
  pairLift operations first second matching ≫ operations.composition

@[reassoc] theorem compose_source {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    compose operations first second matching ≫ operations.source = first ≫ operations.source := by
  rw [compose, Category.assoc, operations.compositionSource, ← Category.assoc]
  rw [PullbackCone.IsLimit.lift_fst]

@[reassoc] theorem compose_target {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    compose operations first second matching ≫ operations.target = second ≫ operations.target := by
  rw [compose, Category.assoc, operations.compositionTarget, ← Category.assoc]
  rw [PullbackCone.IsLimit.lift_snd]

theorem compose_precompose {X Y : C} (stage : X ⟶ Y) (first second : Y ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    stage ≫ compose operations first second matching =
      compose operations (stage ≫ first) (stage ≫ second)
        (by simpa only [Category.assoc] using congrArg (fun arrow => stage ≫ arrow) matching) := by
  rw [compose, ← Category.assoc]
  congr 1
  apply PullbackCone.IsLimit.hom_ext operations.pairLimit <;>
    simp only [pairLift, Category.assoc, PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd]

theorem compose_congr {X : C} {first first' second second' : X ⟶ operations.edge}
    (firstSame : first = first') (secondSame : second = second')
    (matching : first ≫ operations.target = second ≫ operations.source)
    (matching' : first' ≫ operations.target = second' ≫ operations.source) :
    compose operations first second matching = compose operations first' second' matching' := by
  subst first'
  subst second'
  rfl

abbrev TripleCone := PullbackCone (operations.pair.snd ≫ operations.target) operations.source

variable (triples : TripleCone operations)

def first : triples.pt ⟶ operations.edge := triples.fst ≫ operations.pair.fst
def middle : triples.pt ⟶ operations.edge := triples.fst ≫ operations.pair.snd

theorem first_matching : first operations triples ≫ operations.target =
    middle operations triples ≫ operations.source := by
  simp only [first, middle, Category.assoc]
  rw [operations.pair.condition]

theorem second_matching : middle operations triples ≫ operations.target =
    triples.snd ≫ operations.source := by
  simpa only [middle, Category.assoc] using triples.condition

def associateLeft : triples.pt ⟶ operations.edge :=
  compose operations (triples.fst ≫ operations.composition) triples.snd (by
    rw [Category.assoc, operations.compositionTarget]
    exact triples.condition)

def associateRight : triples.pt ⟶ operations.edge :=
  compose operations (first operations triples)
    (compose operations (middle operations triples) triples.snd (second_matching operations triples))
    (by rw [compose_source]; exact first_matching operations triples)

structure Laws : Prop where
  leftUnit : compose operations (operations.source ≫ operations.unit) (𝟙 operations.edge)
    (by simp only [Category.assoc, operations.unitTarget, Category.comp_id, Category.id_comp]) =
      𝟙 operations.edge
  rightUnit : compose operations (𝟙 operations.edge) (operations.target ≫ operations.unit)
    (by simp only [Category.assoc, operations.unitSource, Category.comp_id, Category.id_comp]) =
      𝟙 operations.edge
  associativity : associateLeft operations triples = associateRight operations triples

variable (tripleLimit : IsLimit triples)

def factor {X : C} (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) : X ⟶ triples.pt :=
  PullbackCone.IsLimit.lift tripleLimit (pairLift operations first second firstMatch) third (by
    rw [← Category.assoc, PullbackCone.IsLimit.lift_snd]
    exact secondMatch)

@[simp] theorem factor_pair {X : C} (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) :
    factor operations triples tripleLimit first second third firstMatch secondMatch ≫ triples.fst =
      pairLift operations first second firstMatch := PullbackCone.IsLimit.lift_fst _ _ _ _

@[simp] theorem factor_first {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations triples tripleLimit before middle after firstMatch secondMatch ≫
      first operations triples = before := by
  rw [first, ← Category.assoc, factor_pair, PullbackCone.IsLimit.lift_fst]

@[simp] theorem factor_middle {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations triples tripleLimit before middle after firstMatch secondMatch ≫
      InternalCategoryPresentedDiagrams.middle operations triples = middle := by
  rw [InternalCategoryPresentedDiagrams.middle, ← Category.assoc, factor_pair,
    PullbackCone.IsLimit.lift_snd]

@[simp] theorem factor_last {X : C} (before middle after : X ⟶ operations.edge)
    (firstMatch : before ≫ operations.target = middle ≫ operations.source)
    (secondMatch : middle ≫ operations.target = after ≫ operations.source) :
    factor operations triples tripleLimit before middle after firstMatch secondMatch ≫ triples.snd =
      after := PullbackCone.IsLimit.lift_snd _ _ _ _

include tripleLimit in
theorem associativity (laws : Laws operations triples) {X : C}
    (first second third : X ⟶ operations.edge)
    (firstMatch : first ≫ operations.target = second ≫ operations.source)
    (secondMatch : second ≫ operations.target = third ≫ operations.source) :
    compose operations (compose operations first second firstMatch) third
      (by rw [compose_target]; exact secondMatch) =
    compose operations first (compose operations second third secondMatch)
      (by rw [compose_source]; exact firstMatch) := by
  let stage := factor operations triples tripleLimit first second third firstMatch secondMatch
  have localLaw := congrArg (fun arrow => stage ≫ arrow) laws.associativity
  have firstRead : stage ≫ (triples.fst ≫ operations.composition) =
      compose operations first second firstMatch := by
    rw [← Category.assoc, factor_pair]
  have innerRead : stage ≫ compose operations (middle operations triples) triples.snd
      (second_matching operations triples) = compose operations second third secondMatch :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations (factor_middle operations triples tripleLimit first second third firstMatch secondMatch)
        (factor_last operations triples tripleLimit first second third firstMatch secondMatch) _ _)
  have leftRead : stage ≫ associateLeft operations triples =
      compose operations (compose operations first second firstMatch) third
        (by rw [compose_target]; exact secondMatch) :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations firstRead
        (factor_last operations triples tripleLimit first second third firstMatch secondMatch) _ _)
  have rightRead : stage ≫ associateRight operations triples =
      compose operations first (compose operations second third secondMatch)
        (by rw [compose_source]; exact firstMatch) :=
    (compose_precompose operations stage _ _ _).trans
      (compose_congr operations (factor_first operations triples tripleLimit first second third firstMatch secondMatch)
        innerRead _ _)
  exact leftRead.symm.trans (localLaw.trans rightRead)

variable [HasPullbacks C]

def chosenEndpoints : InternalCategoryLocalDiagrams.Endpoints C where
  toInternalGraph := operations.toInternalGraph
  unit := operations.unit
  composition := pairLift operations (pullback.fst _ _) (pullback.snd _ _) pullback.condition ≫
    operations.composition
  unit_source := operations.unitSource
  unit_target := operations.unitTarget
  composition_source := by
    rw [Category.assoc, operations.compositionSource, ← Category.assoc,
      PullbackCone.IsLimit.lift_fst]
  composition_target := by
    rw [Category.assoc, operations.compositionTarget, ← Category.assoc,
      PullbackCone.IsLimit.lift_snd]

theorem chosen_compose_read {X : C} (first second : X ⟶ operations.edge)
    (matching : first ≫ operations.target = second ≫ operations.source) :
    InternalCategoryLocalDiagrams.compose (chosenEndpoints operations) first second matching =
      compose operations first second matching := by
  dsimp only [InternalCategoryLocalDiagrams.compose, InternalGraph.composeWith, chosenEndpoints, compose]
  rw [← Category.assoc]
  congr 1
  apply PullbackCone.IsLimit.hom_ext operations.pairLimit <;>
    simp only [pairLift, Category.assoc, PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd, pullback.lift_fst, pullback.lift_snd]

def category (laws : Laws operations triples) : InternalCategory C where
  toInternalGraph := operations.toInternalGraph
  unit := operations.unit
  composition := (chosenEndpoints operations).composition
  unit_source := operations.unitSource
  unit_target := operations.unitTarget
  composition_source := (chosenEndpoints operations).composition_source
  composition_target := (chosenEndpoints operations).composition_target
  unit_left := (chosen_compose_read operations _ _ _).trans laws.leftUnit
  unit_right := (chosen_compose_read operations _ _ _).trans laws.rightUnit
  associativity := by
    intro X first second third firstMatch secondMatch
    have firstRead := chosen_compose_read operations first second firstMatch
    have secondRead := chosen_compose_read operations second third secondMatch
    have leftRead : InternalCategoryLocalDiagrams.compose (chosenEndpoints operations)
        (InternalCategoryLocalDiagrams.compose (chosenEndpoints operations) first second firstMatch) third
          (by rw [InternalCategoryLocalDiagrams.compose_target]; exact secondMatch) =
      compose operations (compose operations first second firstMatch) third
          (by rw [compose_target]; exact secondMatch) :=
      (chosen_compose_read operations _ _ _).trans
      (compose_congr operations firstRead (rfl : third = third) _ _)
    have rightRead : InternalCategoryLocalDiagrams.compose (chosenEndpoints operations) first
        (InternalCategoryLocalDiagrams.compose (chosenEndpoints operations) second third secondMatch)
          (by rw [InternalCategoryLocalDiagrams.compose_source]; exact firstMatch) =
      compose operations first (compose operations second third secondMatch)
          (by rw [compose_source]; exact firstMatch) :=
      (chosen_compose_read operations _ _ _).trans
      (compose_congr operations (rfl : first = first) secondRead _ _)
    exact leftRead.trans ((associativity operations triples tripleLimit laws first second third firstMatch secondMatch).trans
      rightRead.symm)

end Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams
