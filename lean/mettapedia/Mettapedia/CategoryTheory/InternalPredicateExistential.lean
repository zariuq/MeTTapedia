import Mettapedia.CategoryTheory.InternalPredicateQuantifier

/-!
# Finite local diagrams for existential predicate functions

The ordered-pair monotonicity diagram and two local unit/counit diagrams
derive the existential/precomposition adjunction in every generalized
context. The function arrow retains the complete supplied predicate, and
its context substitution is ordinary categorical composition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateExistential

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateFunctionObject InternalPredicateQuantifier

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (original : Operations C) (originalLaws : original.Laws)
variable {source target : C} (route : source ⟶ target)

structure Existential where
  operation : power original source ⟶ power original target
  monotonicity : Monotonicity original operation
  unit : (functions original source).meet
      (operation ≫ precomposition original route) (𝟙 (power original source)) = 𝟙 _
  counit : (functions original target).meet (𝟙 (power original target))
      (precomposition original route ≫ operation) = precomposition original route ≫ operation

namespace Existential

variable (quantifier : Existential original route)

theorem unit_at {context : C} (predicate : context ⟶ power original source) :
    (functions original source).meet
      ((predicate ≫ quantifier.operation) ≫ precomposition original route) predicate = predicate := by
  have natural := (functions original source).reindex_meet predicate
    (quantifier.operation ≫ precomposition original route) (𝟙 _)
  have complete := natural.symm.trans (congrArg (fun arrow => predicate ≫ arrow) quantifier.unit)
  simpa only [Operations.reindex, Category.comp_id, ← Category.assoc] using complete

theorem counit_at {context : C} (predicate : context ⟶ power original target) :
    (functions original target).meet predicate
      ((predicate ≫ precomposition original route) ≫ quantifier.operation) =
        (predicate ≫ precomposition original route) ≫ quantifier.operation := by
  have natural := (functions original target).reindex_meet predicate
    (𝟙 _) (precomposition original route ≫ quantifier.operation)
  have complete := natural.symm.trans (congrArg (fun arrow => predicate ≫ arrow) quantifier.counit)
  simpa only [Operations.reindex, Category.comp_id, ← Category.assoc] using complete

theorem adjunction (context : C) :
    letI : SemilatticeInf (context ⟶ power original source) :=
      (functions original source).semilattice (functionLaws original originalLaws source) context
    letI : SemilatticeInf (context ⟶ power original target) :=
      (functions original target).semilattice (functionLaws original originalLaws target) context
    GaloisConnection
      (fun predicate : context ⟶ power original source =>
        (predicate ≫ quantifier.operation : context ⟶ power original target))
      (fun predicate : context ⟶ power original target =>
        (predicate ≫ precomposition original route : context ⟶ power original source)) := by
  let : SemilatticeInf (context ⟶ power original source) :=
    (functions original source).semilattice (functionLaws original originalLaws source) context
  let : SemilatticeInf (context ⟶ power original target) :=
    (functions original target).semilattice (functionLaws original originalLaws target) context
  intro first second
  constructor
  · intro ordered
    have preserved := precomposition_mono original originalLaws route context ordered
    have bound : first ≤ (first ≫ quantifier.operation) ≫ precomposition original route :=
      unit_at original route quantifier first
    exact bound.trans preserved
  · intro ordered
    have preserved := monotone_from_diagram original originalLaws quantifier.operation
      quantifier.monotonicity context ordered
    have bound : (second ≫ precomposition original route) ≫ quantifier.operation ≤ second :=
      counit_at original route quantifier second
    exact preserved.trans bound

end Existential

end Mettapedia.CategoryTheory.InternalPredicateExistential
