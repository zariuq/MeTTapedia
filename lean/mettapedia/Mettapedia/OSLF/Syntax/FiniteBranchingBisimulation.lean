import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviour
import Mettapedia.CategoryTheory.FinitePowersetRelation
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Actual finite relation coalgebras

A two-sided labelled bisimulation supplies a coalgebra on its complete
related-pair carrier. Each action retains all related pairs of successors;
both projections are genuine coalgebra morphisms with exact original
successor-set readouts. No final coalgebra or syntax congruence is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation

open _root_.CategoryTheory Mettapedia.CategoryTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions))

abbrev Relation := ∀ base sort, left.V base sort → right.V base sort → Prop

def Admitted (relation : Relation left right) : Prop :=
  ∀ base sort value other, relation base sort value other → ∀ action,
    FinitePowerset.Related (relation base sort)
      (left.str base sort value action) (right.str base sort other action)

abbrev Pairs (relation : Relation left right) : S.Families :=
  fun base sort => FinitePowersetRelation.Pair (relation base sort)

def successors (relation : Relation left right)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (pair : Pairs left right relation base sort) (action : Actions sort) :
    Finset (Pairs left right relation base sort) :=
  FinitePowersetRelation.matching (relation base sort)
    (left.str base sort pair.val.1 action) (right.str base sort pair.val.2 action)

def relationCoalgebra (relation : Relation left right) :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  V := Pairs left right relation
  str := fun base sort => ↾(successors left right relation base sort)

def first (relation : Relation left right) :
    Pairs left right relation ⟶ left.V :=
  fun base sort => ↾(FinitePowersetRelation.first (relation base sort))

def second (relation : Relation left right) :
    Pairs left right relation ⟶ right.V :=
  fun base sort => ↾(FinitePowersetRelation.second (relation base sort))

theorem first_successors (relation : Relation left right)
    (admitted : Admitted left right relation)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (pair : Pairs left right relation base sort) (action : Actions sort) :
    FinitePowerset.map (first left right relation base sort)
        (successors left right relation base sort pair action) =
      left.str base sort pair.val.1 action :=
  FinitePowersetRelation.matching_first (relation base sort) _ _
    (admitted base sort pair.val.1 pair.val.2 pair.property action)

theorem second_successors (relation : Relation left right)
    (admitted : Admitted left right relation)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (pair : Pairs left right relation base sort) (action : Actions sort) :
    FinitePowerset.map (second left right relation base sort)
        (successors left right relation base sort pair action) =
      right.str base sort pair.val.2 action :=
  FinitePowersetRelation.matching_second (relation base sort) _ _
    (admitted base sort pair.val.1 pair.val.2 pair.property action)

def firstMorphism (relation : Relation left right)
    (admitted : Admitted left right relation) :
    relationCoalgebra left right relation ⟶ left where
  f := first left right relation
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact first_successors left right relation admitted base sort pair action

def secondMorphism (relation : Relation left right)
    (admitted : Admitted left right relation) :
    relationCoalgebra left right relation ⟶ right where
  f := second left right relation
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact second_successors left right relation admitted base sort pair action

@[simp] theorem first_readout (relation : Relation left right)
    (admitted : Admitted left right relation)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (pair : Pairs left right relation base sort) :
    (firstMorphism left right relation admitted).f base sort pair = pair.val.1 := rfl

@[simp] theorem second_readout (relation : Relation left right)
    (admitted : Admitted left right relation)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (pair : Pairs left right relation base sort) :
    (secondMorphism left right relation admitted).f base sort pair = pair.val.2 := rfl

end Mettapedia.OSLF.FiniteBranching.Bisimulation
