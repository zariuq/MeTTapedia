import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraBisimulation
import Mathlib.Data.Quot

/-!
# Constructed contextual greatest-bisimulation quotient

Each fibre is the actual quotient by contextual future bisimilarity.
Contextual maps preserve this relation. Matching at each identical future
index proves that projected child predicates are equal, so quotient
elimination constructs a natural small-covered coalgebra on the quotient.

The projection has exactly the greatest-bisimilarity kernel and satisfies
the complete future-image equation. Bisimilarity in the quotient is actual
equality. Compatible natural maps have a constructed unique factor, with
no selection of representatives. This quotient does not supply a universal
small coalgebra object or indexed finality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v}

variable (original : NaturalHom A (CoveredFuturePowerFamilies.family A))

def family : D ⥤ Type v where
  obj point := Quotient (ContextualCoalgebraBisimulation.setoid original point)
  map {first second} step := TypeCat.ofHom
    (Quotient.map (sa := ContextualCoalgebraBisimulation.setoid original first)
      (sb := ContextualCoalgebraBisimulation.setoid original second) (A.map step)
      (fun {_ _} related => ContextualCoalgebraBisimulation.bisimilar_stable original step related))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk (ContextualCoalgebraBisimulation.setoid original point))
      (congrArg (fun map => map argument) (A.map_id point))
  map_comp {first _middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    refine Quotient.inductionOn value fun argument => ?_
    exact congrArg (Quotient.mk (ContextualCoalgebraBisimulation.setoid original last))
      (congrArg (fun map => map argument) (A.map_comp earlier later))

def projection : NaturalHom A (family original) where
  app point := Quotient.mk (ContextualCoalgebraBisimulation.setoid original point)
  naturality _ _ := rfl

theorem projection_eq_iff (point : D) (first second : A.obj point) :
    (projection original).app point first = (projection original).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar original point first second :=
  ⟨Quotient.exact, fun related => Quotient.sound related⟩

theorem projection_surjective (point : D) : Function.Surjective ((projection original).app point) := by
  intro value
  exact Quotient.inductionOn value fun argument => ⟨argument, rfl⟩

theorem projection_restriction {first second : D} (step : first ⟶ second) (argument : A.obj first) :
    (family original).map step ((projection original).app first argument) =
      (projection original).app second (A.map step argument) := rfl

/-- Both matching directions preserve the complete projected predicate,
including the future arrow; equal present child sets alone are not used. -/
theorem projected_power_eq {point : D} {left right : A.obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar original point left right) :
    CoveredFuturePowerFunctor.imagePower (projection original) point (original.app point left) =
      CoveredFuturePowerFunctor.imagePower (projection original) point (original.app point right) := by
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro argument
  constructor
  · rintro ⟨child, same, available⟩
    obtain ⟨matching, matched, children⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation original).forth related argument.1 available
    exact ⟨matching, ((projection_eq_iff original argument.1.1 child matching).mpr children).symm.trans same,
      matched⟩
  · rintro ⟨child, same, available⟩
    obtain ⟨matching, matched, children⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation original).back related argument.1 available
    exact ⟨matching, ((projection_eq_iff original argument.1.1 matching child).mpr children).trans same,
      matched⟩

def coalgebra : NaturalHom (family original) (CoveredFuturePowerFamilies.family (family original)) where
  app point := Quotient.lift
    (fun argument => CoveredFuturePowerFunctor.imagePower (projection original) point (original.app point argument))
    (fun _ _ related => projected_power_eq original related)
  naturality {first second} step value := by
    refine Quotient.inductionOn value fun argument => ?_
    change CoveredFuturePowerFamilies.restrictPower (family original) step
        (CoveredFuturePowerFunctor.imagePower (projection original) first (original.app first argument)) =
      CoveredFuturePowerFunctor.imagePower (projection original) second (original.app second (A.map step argument))
    exact (CoveredFuturePowerFunctor.imagePower_restrict (projection original) step
      (original.app first argument)).trans
        (congrArg (CoveredFuturePowerFunctor.imagePower (projection original) second)
          (original.naturality step argument))

theorem coalgebra_projection (point : D) (argument : A.obj point) :
    (coalgebra original).app point ((projection original).app point argument) =
      CoveredFuturePowerFunctor.imagePower (projection original) point (original.app point argument) := rfl

theorem coalgebra_square :
    original.comp (CoveredFuturePowerFunctor.imageHom (projection original)) =
      (projection original).comp (coalgebra original) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem quotient_truth (point : D) (argument : A.obj point)
    (future : Future.Objects point) (child : (family original).obj future.1) :
    ((coalgebra original).app point ((projection original).app point argument)).val.holds ⟨future, child⟩ ↔
      ∃ originalChild, (projection original).app future.1 originalChild = child ∧
        (original.app point argument).val.holds ⟨future, originalChild⟩ :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth original (projection original)
    (coalgebra original) (coalgebra_square original) point argument future child

/-- The quotient has no further behavioral identifications. Reflection
uses the whole child-image law to lift every quotient matching witness. -/
theorem bisimilar_iff_eq (point : D) (left right : (family original).obj point) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra original) point left right ↔ left = right := by
  constructor
  · refine Quotient.inductionOn₂ left right fun first second related => ?_
    exact (projection_eq_iff original point first second).mpr
      (ContextualCoalgebraBisimulation.bisimilar_reflected original (projection original)
        (coalgebra original) (coalgebra_square original) related)
  · intro same
    cases same
    exact ContextualCoalgebraBisimulation.bisimilar_refl (coalgebra original) point left

variable {Z : D ⥤ Type w}

def Respects (operation : NaturalHom A Z) : Prop :=
  ∀ point {left right}, ContextualCoalgebraBisimulation.Bisimilar original point left right →
    operation.app point left = operation.app point right

def descend (operation : NaturalHom A Z) (compatible : Respects original operation) :
    NaturalHom (family original) Z where
  app point := Quotient.lift (operation.app point) (fun _ _ related => compatible point related)
  naturality step value := by
    refine Quotient.inductionOn value fun argument => ?_
    exact operation.naturality step argument

theorem descend_beta (operation : NaturalHom A Z) (compatible : Respects original operation)
    (point : D) (argument : A.obj point) :
    (descend original operation compatible).app point ((projection original).app point argument) =
      operation.app point argument := rfl

theorem descend_factorization (operation : NaturalHom A Z) (compatible : Respects original operation) :
    (projection original).comp (descend original operation compatible) = operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem projection_respects (operation : NaturalHom (family original) Z) :
    Respects original ((projection original).comp operation) := by
  intro point left right related
  exact congrArg (operation.app point) ((projection_eq_iff original point left right).mpr related)

theorem descend_unique (operation : NaturalHom A Z) (compatible : Respects original operation)
    (candidate : NaturalHom (family original) Z)
    (factors : (projection original).comp candidate = operation) :
    candidate = descend original operation compatible := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A Z => map.app point argument) factors

def universalHomEquiv : NaturalHom (family original) Z ≃
    {operation : NaturalHom A Z // Respects original operation} where
  toFun operation := ⟨(projection original).comp operation, projection_respects original operation⟩
  invFun operation := descend original operation.val operation.property
  left_inv operation := (descend_unique original ((projection original).comp operation)
    (projection_respects original operation) operation rfl).symm
  right_inv operation := Subtype.ext (descend_factorization original operation.val operation.property)

theorem descends_iff (operation : NaturalHom A Z) :
    (∃ factor : NaturalHom (family original) Z, (projection original).comp factor = operation) ↔
      Respects original operation := by
  constructor
  · rintro ⟨factor, rfl⟩
    exact projection_respects original factor
  · intro compatible
    exact ⟨descend original operation compatible, descend_factorization original operation compatible⟩

theorem projection_epi (first second : NaturalHom (family original) Z)
    (same : (projection original).comp first = (projection original).comp second) : first = second := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  exact congrArg (fun map : NaturalHom A Z => map.app point argument) same

theorem descend_coalgebra (operation : NaturalHom A Z) (compatible : Respects original operation)
    (target : NaturalHom Z (CoveredFuturePowerFamilies.family Z))
    (square : original.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    (coalgebra original).comp (CoveredFuturePowerFunctor.imageHom (descend original operation compatible)) =
      (descend original operation compatible).comp target := by
  apply NaturalHom.ext
  intro point value
  refine Quotient.inductionOn value fun argument => ?_
  change CoveredFuturePowerFunctor.imagePower (descend original operation compatible) point
      (CoveredFuturePowerFunctor.imagePower (projection original) point (original.app point argument)) =
    target.app point (operation.app point argument)
  have mapped : CoveredFuturePowerFunctor.imagePower operation point (original.app point argument) =
      target.app point (operation.app point argument) :=
    congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family Z) => map.app point argument) square
  have factored := congrArg
    (fun map : NaturalHom A Z => CoveredFuturePowerFunctor.imagePower map point (original.app point argument))
      (descend_factorization original operation compatible)
  exact (CoveredFuturePowerFunctor.imagePower_comp (projection original)
    (descend original operation compatible) point (original.app point argument)).trans (factored.trans mapped)

def BehaviorallySeparated (target : NaturalHom Z (CoveredFuturePowerFamilies.family Z)) : Prop :=
  ∀ point left right, ContextualCoalgebraBisimulation.Bisimilar target point left right → left = right

theorem quotient_separated : BehaviorallySeparated (coalgebra original) :=
  fun point left right related => (bisimilar_iff_eq original point left right).mp related

theorem coalgebra_map_respects (operation : NaturalHom A Z)
    (target : NaturalHom Z (CoveredFuturePowerFamilies.family Z))
    (separated : BehaviorallySeparated target)
    (square : original.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    Respects original operation := by
  intro point left right related
  exact separated point _ _
    (ContextualCoalgebraBisimulation.bisimilar_preserved original operation target square related)

/-- Every actual morphism into a behaviorally separated coalgebra has a
unique coalgebra factor. This is a universal property of this quotient,
not the existence of a final coalgebra for all argument families. -/
theorem coalgebra_universal (operation : NaturalHom A Z)
    (target : NaturalHom Z (CoveredFuturePowerFamilies.family Z))
    (separated : BehaviorallySeparated target)
    (square : original.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    ∃! factor : NaturalHom (family original) Z,
      (projection original).comp factor = operation ∧
      (coalgebra original).comp (CoveredFuturePowerFunctor.imageHom factor) = factor.comp target := by
  let compatible := coalgebra_map_respects original operation target separated square
  refine ⟨descend original operation compatible,
    ⟨descend_factorization original operation compatible,
      descend_coalgebra original operation compatible target square⟩, ?_⟩
  intro candidate factors
  exact descend_unique original operation compatible candidate factors.1

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
