import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Streams

/-!
# Labelled graphs of small contextual coalgebras

States retain their context and actual argument. Two disjoint kinds of
label retain the source context, target context and actual arrow:
deterministic context transport, and admitted future coalgebra children.

For an injective label reading, ordinary labelled bisimulation is exactly
contextual bisimulation at one context. Every related pair of graph states
has the same context: its identity transport label forces that equality.
The deterministic transport edges recover contextual stability.

Contexts, arrows and argument fibres all inhabit the same graph universe.
There is no selected branch enumeration or quotient representative.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraLabelledGraph

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type u}

abbrev State (A : D ⥤ Type u) := (point : D) × A.obj point

inductive Label (D : Type u) [Category.{u} D] : Type u
  | context (source target : D) (arrow : source ⟶ target)
  | child (source target : D) (arrow : source ⟶ target)

namespace Label

def source : Label D → D
  | .context source _ _ => source
  | .child source _ _ => source

def target : Label D → D
  | .context _ target _ => target
  | .child _ target _ => target

end Label

variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))

def Step (first : State A) (label : Label D) (second : State A) : Prop :=
  match label with
  | .context source target arrow =>
      ∃ value : A.obj source,
        first = ⟨source, value⟩ ∧ second = ⟨target, A.map arrow value⟩
  | .child source target arrow =>
      ∃ value : A.obj source, ∃ next : A.obj target,
        first = ⟨source, value⟩ ∧ second = ⟨target, next⟩ ∧
          (coalgebra.app source value).val.holds ⟨⟨target, arrow⟩, next⟩

theorem context_step {source target : D} (arrow : source ⟶ target) (value : A.obj source) :
    Step coalgebra ⟨source, value⟩ (.context source target arrow) ⟨target, A.map arrow value⟩ :=
  ⟨value, rfl, rfl⟩

theorem child_step {source target : D} (arrow : source ⟶ target)
    (value : A.obj source) (next : A.obj target)
    (available : (coalgebra.app source value).val.holds ⟨⟨target, arrow⟩, next⟩) :
    Step coalgebra ⟨source, value⟩ (.child source target arrow) ⟨target, next⟩ :=
  ⟨value, next, rfl, rfl, available⟩

theorem step_source {first second : State A} {label : Label D}
    (step : Step coalgebra first label second) : first.1 = label.source := by
  cases label with
  | context source target arrow =>
      obtain ⟨value, same, _⟩ := step
      exact congrArg Sigma.fst same
  | child source target arrow =>
      obtain ⟨value, next, same, _, _⟩ := step
      exact congrArg Sigma.fst same

theorem step_target {first second : State A} {label : Label D}
    (step : Step coalgebra first label second) : second.1 = label.target := by
  cases label with
  | context source target arrow =>
      obtain ⟨value, _, same⟩ := step
      exact congrArg Sigma.fst same
  | child source target arrow =>
      obtain ⟨value, next, _, same, _⟩ := step
      exact congrArg Sigma.fst same

theorem context_step_iff {source target : D} (arrow : source ⟶ target)
    (value : A.obj source) (second : State A) :
    Step coalgebra ⟨source, value⟩ (.context source target arrow) second ↔
      second = ⟨target, A.map arrow value⟩ := by
  constructor
  · rintro ⟨other, same, result⟩
    have values : value = other := eq_of_heq (Sigma.mk.inj same).2
    cases values
    exact result
  · intro same
    exact ⟨value, rfl, same⟩

theorem child_step_iff {source target : D} (arrow : source ⟶ target)
    (value : A.obj source) (second : State A) :
    Step coalgebra ⟨source, value⟩ (.child source target arrow) second ↔
      ∃ next : A.obj target, second = ⟨target, next⟩ ∧
        (coalgebra.app source value).val.holds ⟨⟨target, arrow⟩, next⟩ := by
  constructor
  · rintro ⟨other, next, same, result, available⟩
    have values : value = other := eq_of_heq (Sigma.mk.inj same).2
    cases values
    exact ⟨next, result, available⟩
  · rintro ⟨next, result, available⟩
    exact ⟨value, next, rfl, result, available⟩

def liftRelation (relation : ContextualCoalgebraBisimulation.Relation A)
    (first second : State A) : Prop :=
  ∃ point, ∃ left right : A.obj point,
    first = ⟨point, left⟩ ∧ second = ⟨point, right⟩ ∧ relation point left right

theorem lift_isLabelledBisimulation (reading : Label D → HSet.{u})
    {relation : ContextualCoalgebraBisimulation.Relation A}
    (bisimulation : ContextualCoalgebraBisimulation.IsBisimulation coalgebra relation) :
    IsLabelledBisimulation (Step coalgebra) (Step coalgebra) reading reading
      (liftRelation relation) := by
  rintro first second ⟨point, left, right, rfl, rfl, related⟩
  constructor
  · intro label next step
    cases label with
    | context source target arrow =>
        obtain ⟨value, same, rfl⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : left = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        exact ⟨.context point target arrow, ⟨target, A.map arrow right⟩,
          context_step coalgebra arrow right, rfl, target,
          A.map arrow left, A.map arrow right, rfl, rfl,
          bisimulation.stable arrow related⟩
    | child source target arrow =>
        obtain ⟨value, child, same, rfl, available⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : left = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        obtain ⟨matching, matched, children⟩ :=
          bisimulation.forth related ⟨target, arrow⟩ available
        exact ⟨.child point target arrow, ⟨target, matching⟩,
          child_step coalgebra arrow right matching matched, rfl,
          target, child, matching, rfl, rfl, children⟩
  · intro label next step
    cases label with
    | context source target arrow =>
        obtain ⟨value, same, rfl⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : right = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        exact ⟨.context point target arrow, ⟨target, A.map arrow left⟩,
          context_step coalgebra arrow left, rfl, target,
          A.map arrow left, A.map arrow right, rfl, rfl,
          bisimulation.stable arrow related⟩
    | child source target arrow =>
        obtain ⟨value, child, same, rfl, available⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : right = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        obtain ⟨matching, matched, children⟩ :=
          bisimulation.back related ⟨target, arrow⟩ available
        exact ⟨.child point target arrow, ⟨target, matching⟩,
          child_step coalgebra arrow left matching matched, rfl,
          target, matching, child, rfl, rfl, children⟩

theorem related_contexts_eq (reading : Label D → HSet.{u})
    (faithful : Function.Injective reading) {relation : State A → State A → Prop}
    (bisimulation : IsLabelledBisimulation (Step coalgebra) (Step coalgebra)
      reading reading relation) {first second : State A} (related : relation first second) :
    first.1 = second.1 := by
  obtain ⟨label, matching, matched, readings, _⟩ :=
    (bisimulation related).1 (.context first.1 first.1 (𝟙 first.1))
      ⟨first.1, A.map (𝟙 first.1) first.2⟩ (context_step coalgebra (𝟙 first.1) first.2)
  have labels := faithful readings
  cases labels
  exact (step_source coalgebra matched).symm

theorem contextual_isBisimulation (reading : Label D → HSet.{u})
    (faithful : Function.Injective reading) {relation : State A → State A → Prop}
    (bisimulation : IsLabelledBisimulation (Step coalgebra) (Step coalgebra)
      reading reading relation) :
    ContextualCoalgebraBisimulation.IsBisimulation coalgebra
      (fun point left right => relation ⟨point, left⟩ ⟨point, right⟩) where
  stable {source target} arrow {left right} related := by
    obtain ⟨label, matching, matched, readings, children⟩ :=
      (bisimulation related).1 (.context source target arrow) ⟨target, A.map arrow left⟩
        (context_step coalgebra arrow left)
    have labels := faithful readings
    cases labels
    have same := (context_step_iff coalgebra arrow right matching).mp matched
    cases same
    exact children
  forth {point left right} related future {child} available := by
    obtain ⟨label, matching, matched, readings, children⟩ :=
      (bisimulation related).1 (.child point future.1 future.2) ⟨future.1, child⟩
        (child_step coalgebra future.2 left child available)
    have labels := faithful readings
    cases labels
    obtain ⟨next, same, available⟩ := (child_step_iff coalgebra future.2 right matching).mp matched
    cases same
    exact ⟨next, available, children⟩
  back {point left right} related future {child} available := by
    obtain ⟨label, matching, matched, readings, children⟩ :=
      (bisimulation related).2 (.child point future.1 future.2) ⟨future.1, child⟩
        (child_step coalgebra future.2 right child available)
    have labels := faithful readings
    cases labels
    obtain ⟨next, same, available⟩ := (child_step_iff coalgebra future.2 left matching).mp matched
    cases same
    exact ⟨next, available, children⟩

theorem labelledBisimilar_iff_contextual (reading : Label D → HSet.{u})
    (faithful : Function.Injective reading) (point : D) (left right : A.obj point) :
    LabelledBisimilar (Step coalgebra) (Step coalgebra) reading reading
      ⟨point, left⟩ ⟨point, right⟩ ↔
      ContextualCoalgebraBisimulation.Bisimilar coalgebra point left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨_, contextual_isBisimulation coalgebra reading faithful bisimulation, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨liftRelation relation, lift_isLabelledBisimulation coalgebra reading bisimulation,
      point, left, right, rfl, rfl, related⟩

theorem labelledBisimilar_contexts_eq (reading : Label D → HSet.{u})
    (faithful : Function.Injective reading) {first second : State A}
    (related : LabelledBisimilar (Step coalgebra) (Step coalgebra) reading reading first second) :
    first.1 = second.1 := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact related_contexts_eq coalgebra reading faithful bisimulation related

variable {B : D ⥤ Type u}

def graphMap (operation : NaturalHom A B) (state : State A) : State B :=
  ⟨state.1, operation.app state.1 state.2⟩

/-- The whole coalgebra image square supplies the reverse matching direction;
ordinary naturality supplies deterministic context-edge matching. -/
theorem coalgebra_map_isLabelledBisimulation (reading : Label D → HSet.{u})
    (operation : NaturalHom A B) (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    IsLabelledBisimulation (Step coalgebra) (Step target) reading reading
      (fun first second => second = graphMap operation first) := by
  rintro ⟨point, argument⟩ second rfl
  constructor
  · intro label next step
    cases label with
    | context source destination arrow =>
        obtain ⟨value, same, rfl⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : argument = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        refine ⟨.context point destination arrow,
          ⟨destination, operation.app destination (A.map arrow argument)⟩, ?_, rfl, rfl⟩
        exact ⟨operation.app point argument, rfl,
          congrArg (Sigma.mk destination) (operation.naturality arrow argument).symm⟩
    | child source destination arrow =>
        obtain ⟨value, child, same, rfl, available⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : argument = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        refine ⟨.child point destination arrow, ⟨destination, operation.app destination child⟩,
          child_step target arrow (operation.app point argument) (operation.app destination child) ?_,
          rfl, rfl⟩
        exact (ContextualCoalgebraBisimulation.coalgebra_map_truth coalgebra operation target square
          point argument ⟨destination, arrow⟩ _).mpr ⟨child, rfl, available⟩
  · intro label next step
    cases label with
    | context source destination arrow =>
        obtain ⟨value, same, rfl⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : operation.app point argument = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        exact ⟨.context point destination arrow, ⟨destination, A.map arrow argument⟩,
          context_step coalgebra arrow argument, rfl,
          congrArg (Sigma.mk destination) (operation.naturality arrow argument)⟩
    | child source destination arrow =>
        obtain ⟨value, child, same, rfl, available⟩ := step
        have contexts : point = source := congrArg Sigma.fst same
        cases contexts
        have values : operation.app point argument = value := eq_of_heq (Sigma.mk.inj same).2
        cases values
        obtain ⟨original, observed, sourceStep⟩ :=
          (ContextualCoalgebraBisimulation.coalgebra_map_truth coalgebra operation target square
            point argument ⟨destination, arrow⟩ child).mp available
        exact ⟨.child point destination arrow, ⟨destination, original⟩,
          child_step coalgebra arrow argument original sourceStep, rfl,
          congrArg (Sigma.mk destination) observed.symm⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraLabelledGraph
