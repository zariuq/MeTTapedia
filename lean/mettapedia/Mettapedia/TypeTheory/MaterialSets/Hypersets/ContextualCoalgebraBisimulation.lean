import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

/-!
# Greatest contextual bisimulation of small-covered coalgebras

Argument fibres may inhabit a wider universe than the context category.
Bisimulations commute with actual contextual maps and match children at
the identical future object and arrow. Their existential union is itself
a bisimulation and a contextual equivalence relation.

The observed signature consists of these future transitions. Additional
state readings or authored event identities are not inferred from it.
Small covers remain propositional data; no cover or representative is
selected in the equivalence proofs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v}

abbrev Relation (A : D ⥤ Type v) := (point : D) → A.obj point → A.obj point → Prop

structure IsBisimulation
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (relation : Relation A) : Prop where
  stable : ∀ {first second} (step : first ⟶ second) {left right}, relation first left right →
    relation second (A.map step left) (A.map step right)
  forth : ∀ {point left right}, relation point left right →
    ∀ (future : Future.Objects point) {child},
      (coalgebra.app point left).val.holds ⟨future, child⟩ →
      ∃ matching, (coalgebra.app point right).val.holds ⟨future, matching⟩ ∧
        relation future.1 child matching
  back : ∀ {point left right}, relation point left right →
    ∀ (future : Future.Objects point) {child},
      (coalgebra.app point right).val.holds ⟨future, child⟩ →
      ∃ matching, (coalgebra.app point left).val.holds ⟨future, matching⟩ ∧
        relation future.1 matching child

variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))

def Bisimilar (point : D) (left right : A.obj point) : Prop :=
  ∃ relation, IsBisimulation coalgebra relation ∧ relation point left right

theorem equality_isBisimulation : IsBisimulation coalgebra (fun _ => Eq) where
  stable {_ _} _ {_ _} same := congrArg _ same
  forth {_ _ _} same _ {_} available := by
    cases same
    exact ⟨_, available, rfl⟩
  back {_ _ _} same _ {_} available := by
    cases same
    exact ⟨_, available, rfl⟩

theorem converse_isBisimulation {relation : Relation A}
    (bisimulation : IsBisimulation coalgebra relation) :
    IsBisimulation coalgebra (fun point left right => relation point right left) where
  stable {_ _} step {_ _} related := bisimulation.stable step related
  forth {_ _ _} related future {_} available := bisimulation.back related future available
  back {_ _ _} related future {_} available := bisimulation.forth related future available

theorem composite_isBisimulation {first second : Relation A}
    (earlier : IsBisimulation coalgebra first) (later : IsBisimulation coalgebra second) :
    IsBisimulation coalgebra
      (fun point left right => ∃ middle, first point left middle ∧ second point middle right) where
  stable {_ _} step {_ _} related := by
    obtain ⟨middle, leftMiddle, middleRight⟩ := related
    exact ⟨A.map step middle, earlier.stable step leftMiddle, later.stable step middleRight⟩
  forth {_ _ _} related future {_} available := by
    obtain ⟨middle, leftMiddle, middleRight⟩ := related
    obtain ⟨nextMiddle, middleStep, childMiddle⟩ := earlier.forth leftMiddle future available
    obtain ⟨matching, rightStep, middleMatching⟩ := later.forth middleRight future middleStep
    exact ⟨matching, rightStep, nextMiddle, childMiddle, middleMatching⟩
  back {_ _ _} related future {_} available := by
    obtain ⟨middle, leftMiddle, middleRight⟩ := related
    obtain ⟨nextMiddle, middleStep, middleChild⟩ := later.back middleRight future available
    obtain ⟨matching, leftStep, matchingMiddle⟩ := earlier.back leftMiddle future middleStep
    exact ⟨matching, leftStep, nextMiddle, matchingMiddle, middleChild⟩

theorem bisimilar_refl (point : D) (argument : A.obj point) :
    Bisimilar coalgebra point argument argument :=
  ⟨fun _ => Eq, equality_isBisimulation coalgebra, rfl⟩

theorem bisimilar_symm {point : D} {left right : A.obj point}
    (related : Bisimilar coalgebra point left right) : Bisimilar coalgebra point right left := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact ⟨fun point first second => relation point second first,
    converse_isBisimulation coalgebra bisimulation, related⟩

theorem bisimilar_trans {point : D} {left middle right : A.obj point}
    (earlier : Bisimilar coalgebra point left middle)
    (later : Bisimilar coalgebra point middle right) : Bisimilar coalgebra point left right := by
  obtain ⟨first, firstLaw, leftMiddle⟩ := earlier
  obtain ⟨second, secondLaw, middleRight⟩ := later
  exact ⟨_, composite_isBisimulation coalgebra firstLaw secondLaw,
    middle, leftMiddle, middleRight⟩

theorem bisimilar_stable {first second : D} (step : first ⟶ second)
    {left right : A.obj first} (related : Bisimilar coalgebra first left right) :
    Bisimilar coalgebra second (A.map step left) (A.map step right) := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact ⟨relation, bisimulation, bisimulation.stable step related⟩

theorem greatest {relation : Relation A} (bisimulation : IsBisimulation coalgebra relation)
    {point : D} {left right : A.obj point} (related : relation point left right) :
    Bisimilar coalgebra point left right := ⟨relation, bisimulation, related⟩

theorem bisimilar_isBisimulation : IsBisimulation coalgebra (Bisimilar coalgebra) where
  stable {_ _} step {_ _} related := bisimilar_stable coalgebra step related
  forth {_ _ _} related future {_} available := by
    obtain ⟨relation, bisimulation, related⟩ := related
    obtain ⟨matching, matched, children⟩ := bisimulation.forth related future available
    exact ⟨matching, matched, greatest coalgebra bisimulation children⟩
  back {_ _ _} related future {_} available := by
    obtain ⟨relation, bisimulation, related⟩ := related
    obtain ⟨matching, matched, children⟩ := bisimulation.back related future available
    exact ⟨matching, matched, greatest coalgebra bisimulation children⟩

def setoid (point : D) : Setoid (A.obj point) where
  r := Bisimilar coalgebra point
  iseqv := ⟨bisimilar_refl coalgebra point,
    bisimilar_symm coalgebra, bisimilar_trans coalgebra⟩

variable {B : D ⥤ Type w}

/-- A coalgebra morphism exposes every target child above a source value
as the image of an actual source child, at the same future index. -/
theorem coalgebra_map_truth (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    (point : D) (argument : A.obj point) (future : Future.Objects point) (child : B.obj future.1) :
    (target.app point (operation.app point argument)).val.holds ⟨future, child⟩ ↔
      ∃ original, operation.app future.1 original = child ∧
        (coalgebra.app point argument).val.holds ⟨future, original⟩ := by
  have same := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
    map.app point argument) square
  change CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point argument) =
    target.app point (operation.app point argument) at same
  rw [← same]
  exact Iff.rfl

/-- Matching in the target lifts along the whole coalgebra square. The
existential witnesses are used only to prove this source bisimulation. -/
theorem pullback_isBisimulation (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    {relation : Relation B} (bisimulation : IsBisimulation target relation) :
    IsBisimulation coalgebra
      (fun point left right => relation point (operation.app point left) (operation.app point right)) where
  stable {_ _} step {left right} related := by
    have moved := bisimulation.stable step related
    rw [operation.naturality step left, operation.naturality step right] at moved
    exact moved
  forth {point left right} related future {child} available := by
    have observed := (coalgebra_map_truth coalgebra operation target square point left future
      (operation.app future.1 child)).mpr ⟨child, rfl, available⟩
    obtain ⟨matching, targetStep, children⟩ := bisimulation.forth related future observed
    obtain ⟨original, same, originalStep⟩ :=
      (coalgebra_map_truth coalgebra operation target square point right future matching).mp targetStep
    rw [← same] at children
    exact ⟨original, originalStep, children⟩
  back {point left right} related future {child} available := by
    have observed := (coalgebra_map_truth coalgebra operation target square point right future
      (operation.app future.1 child)).mpr ⟨child, rfl, available⟩
    obtain ⟨matching, targetStep, children⟩ := bisimulation.back related future observed
    obtain ⟨original, same, originalStep⟩ :=
      (coalgebra_map_truth coalgebra operation target square point left future matching).mp targetStep
    rw [← same] at children
    exact ⟨original, originalStep, children⟩

theorem bisimilar_reflected (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    {point : D} {left right : A.obj point}
    (related : Bisimilar target point (operation.app point left) (operation.app point right)) :
    Bisimilar coalgebra point left right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact greatest coalgebra (pullback_isBisimulation coalgebra operation target square bisimulation) related

/-- Images of relations are formed by existential source witnesses. The
coalgebra square lifts target children before matching them in the source. -/
theorem image_isBisimulation (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    {relation : Relation A} (bisimulation : IsBisimulation coalgebra relation) :
    IsBisimulation target (fun point left right =>
      ∃ first second, operation.app point first = left ∧ operation.app point second = right ∧
        relation point first second) where
  stable {_ _} step {_ _} related := by
    obtain ⟨first, second, firstEq, secondEq, related⟩ := related
    exact ⟨A.map step first, A.map step second,
      (operation.naturality step first).symm.trans (congrArg (B.map step) firstEq),
      (operation.naturality step second).symm.trans (congrArg (B.map step) secondEq),
      bisimulation.stable step related⟩
  forth {point _ _} related future {_} available := by
    obtain ⟨first, second, firstEq, secondEq, related⟩ := related
    rw [← firstEq] at available
    obtain ⟨original, same, originalStep⟩ :=
      (coalgebra_map_truth coalgebra operation target square point first future _).mp available
    obtain ⟨matching, matched, children⟩ := bisimulation.forth related future originalStep
    refine ⟨operation.app future.1 matching, ?_, original, matching, same, rfl, children⟩
    rw [← secondEq]
    exact (coalgebra_map_truth coalgebra operation target square point second future _).mpr
      ⟨matching, rfl, matched⟩
  back {point _ _} related future {_} available := by
    obtain ⟨first, second, firstEq, secondEq, related⟩ := related
    rw [← secondEq] at available
    obtain ⟨original, same, originalStep⟩ :=
      (coalgebra_map_truth coalgebra operation target square point second future _).mp available
    obtain ⟨matching, matched, children⟩ := bisimulation.back related future originalStep
    refine ⟨operation.app future.1 matching, ?_, matching, original, rfl, same, children⟩
    rw [← firstEq]
    exact (coalgebra_map_truth coalgebra operation target square point first future _).mpr
      ⟨matching, rfl, matched⟩

theorem bisimilar_preserved (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    {point : D} {left right : A.obj point} (related : Bisimilar coalgebra point left right) :
    Bisimilar target point (operation.app point left) (operation.app point right) := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact greatest target (image_isBisimulation coalgebra operation target square bisimulation)
    ⟨left, right, rfl, rfl, related⟩

theorem bisimilar_map_iff (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    (point : D) (left right : A.obj point) :
    Bisimilar target point (operation.app point left) (operation.app point right) ↔
      Bisimilar coalgebra point left right :=
  ⟨bisimilar_reflected coalgebra operation target square,
    bisimilar_preserved coalgebra operation target square⟩

/-- An actual coalgebra morphism has a bisimulation kernel. The whole
future-image square supplies both matching directions at the same future. -/
theorem kernel_isBisimulation (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    IsBisimulation coalgebra
      (fun point left right => operation.app point left = operation.app point right) where
  stable {_ _} step {_ _} same :=
    (operation.naturality step _).symm.trans
      ((congrArg (B.map step) same).trans (operation.naturality step _))
  forth {point left right} same future {child} available := by
    have projected :
        CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point left) =
          CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point right) := by
      have first := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
        map.app point left) square
      have second := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
        map.app point right) square
      exact first.trans ((congrArg (target.app point) same).trans second.symm)
    have truth : (CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point left)).val.holds
        ⟨future, operation.app future.1 child⟩ := ⟨child, rfl, available⟩
    rw [projected] at truth
    obtain ⟨matching, sameValue, matched⟩ := truth
    exact ⟨matching, matched, sameValue.symm⟩
  back {point left right} same future {child} available := by
    have projected :
        CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point right) =
          CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point left) := by
      have first := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
        map.app point right) square
      have second := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
        map.app point left) square
      exact first.trans ((congrArg (target.app point) same.symm).trans second.symm)
    have truth : (CoveredFuturePowerFunctor.imagePower operation point (coalgebra.app point right)).val.holds
        ⟨future, operation.app future.1 child⟩ := ⟨child, rfl, available⟩
    rw [projected] at truth
    obtain ⟨matching, sameValue, matched⟩ := truth
    exact ⟨matching, matched, sameValue⟩

theorem bisimilar_of_coalgebra_map_eq (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    {point : D} {left right : A.obj point} (same : operation.app point left = operation.app point right) :
    Bisimilar coalgebra point left right :=
  greatest coalgebra (kernel_isBisimulation coalgebra operation target square) same

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation
