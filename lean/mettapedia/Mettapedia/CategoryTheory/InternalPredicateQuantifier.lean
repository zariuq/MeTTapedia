import Mettapedia.CategoryTheory.InternalPredicateFunctionObject
import Mettapedia.CategoryTheory.CartesianTensorPullback

/-!
# Finite local diagrams earn all-context predicate quantification

A satisfying equalizer represents an ordered pair of predicate functions.
One finite diagram on that object earns monotonicity in every generalized
context. Together with the two generic unit/counit diagrams, this derives
the quantifier adjunction on complete function sections. Neither an
all-context adjunction nor a whole-model interpretation is an input field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifier

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject
open InternalPredicateFunctionObject

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (original : Operations C) (originalLaws : original.Laws)

abbrev functions (value : C) := InternalPredicateFunctionObject.operations original value
abbrev functionLaws (value : C) := function_laws original originalLaws value

def orderedPairs (value : C) : C :=
  equalizer (functions original value).conjunction
    (fst (power original value) (power original value))

def orderInclusion (value : C) : orderedPairs original value ⟶
    power original value ⊗ power original value := equalizer.ι _ _

def firstInput (value : C) : orderedPairs original value ⟶ power original value :=
  orderInclusion original value ≫ fst _ _

def secondInput (value : C) : orderedPairs original value ⟶ power original value :=
  orderInclusion original value ≫ snd _ _

/-- A single diagram on the independently formed ordered-pair scope. -/
structure Monotonicity {before after : C}
    (operation : power original before ⟶ power original after) : Prop where
  ordered : (functions original after).meet
    (secondInput original before ≫ operation) (firstInput original before ≫ operation) =
      firstInput original before ≫ operation

variable {before after : C}
variable (operation : power original before ⟶ power original after)

def orderFactor {context : C}
    (first second : (functions original before).Fiber context)
    (ordered : (functions original before).meet second first = first) :
    context ⟶ orderedPairs original before :=
  equalizer.lift (lift first second) (by
    have complete : lift first second ≫ (functions original before).conjunction = first :=
      ((functions original before).meet_comm
        (functionLaws original originalLaws before) first second).trans ordered
    exact complete.trans (lift_fst first second).symm)

@[reassoc (attr := simp)] theorem orderFactor_first {context : C}
    (first second : (functions original before).Fiber context)
    (ordered : (functions original before).meet second first = first) :
    orderFactor original originalLaws first second ordered ≫ firstInput original before = first := by
  simp only [orderFactor, firstInput, orderInclusion, ← Category.assoc,
    equalizer.lift_ι]
  exact lift_fst first second

@[reassoc (attr := simp)] theorem orderFactor_second {context : C}
    (first second : (functions original before).Fiber context)
    (ordered : (functions original before).meet second first = first) :
    orderFactor original originalLaws first second ordered ≫ secondInput original before = second := by
  simp only [orderFactor, secondInput, orderInclusion, ← Category.assoc,
    equalizer.lift_ι]
  exact lift_snd first second

theorem monotone_from_diagram (admitted : Monotonicity original operation) (context : C) :
    letI : SemilatticeInf (context ⟶ power original before) :=
      (functions original before).semilattice (functionLaws original originalLaws before) context
    letI : SemilatticeInf (context ⟶ power original after) :=
      (functions original after).semilattice (functionLaws original originalLaws after) context
    Monotone (fun predicate : context ⟶ power original before =>
      (predicate ≫ operation : context ⟶ power original after)) := by
  intro first second ordered
  change (functions original before).meet second first = first at ordered
  change (functions original after).meet (second ≫ operation) (first ≫ operation) = first ≫ operation
  let factor := orderFactor original originalLaws first second ordered
  have natural := (functions original after).reindex_meet factor
    (secondInput original before ≫ operation) (firstInput original before ≫ operation)
  have localRead := congrArg (fun arrow => factor ≫ arrow) admitted.ordered
  have complete := natural.symm.trans localRead
  simpa only [Operations.reindex, ← Category.assoc, factor,
    orderFactor_first, orderFactor_second] using complete

variable {source target : C} (route : source ⟶ target)

omit [HasEqualizers C] in
/-- Canonical precomposition on function objects retains the full parameter. -/
def precomposition : power original target ⟶ power original source :=
  quote original ((route ▷ power original target) ≫ (ihom.ev target).app original.proposition)

omit [HasEqualizers C] in
theorem precomposition_read {context : C} (predicate : context ⟶ power original target) :
    InternalPredicateFunctionObject.read original (predicate ≫ precomposition original route) =
      (route ▷ context) ≫ InternalPredicateFunctionObject.read original predicate := by
  rw [InternalPredicateFunctionObject.read, precomposition, quote,
    uncurry_natural_left, uncurry_curry]
  change source ◁ predicate ≫ (route ▷ power original target) ≫
      (ihom.ev target).app original.proposition =
    (route ▷ context) ≫ target ◁ predicate ≫ (ihom.ev target).app original.proposition
  rw [← Category.assoc, ← (CartesianTensorPullback.square route predicate).w, Category.assoc]

omit [HasEqualizers C] in
theorem precomposition_mono (context : C) :
    letI : SemilatticeInf (context ⟶ power original target) :=
      (functions original target).semilattice (functionLaws original originalLaws target) context
    letI : SemilatticeInf (context ⟶ power original source) :=
      (functions original source).semilattice (functionLaws original originalLaws source) context
    Monotone (fun predicate : context ⟶ power original target =>
      (predicate ≫ precomposition original route : context ⟶ power original source)) := by
  intro first second ordered
  change (functions original target).meet second first = first at ordered
  change (functions original source).meet (second ≫ precomposition original route)
    (first ≫ precomposition original route) = first ≫ precomposition original route
  apply read_injective original
  rw [read_meet]
  simp only [precomposition_read]
  have originalOrder := congrArg (InternalPredicateFunctionObject.read original) ordered
  rw [read_meet] at originalOrder
  have transported := original.reindex_meet (route ▷ context)
    (InternalPredicateFunctionObject.read original second)
    (InternalPredicateFunctionObject.read original first)
  exact transported.symm.trans (congrArg (fun arrow => (route ▷ context) ≫ arrow) originalOrder)

/-- Three finite local diagrams for a candidate universal quantifier. -/
structure Universal where
  operation : power original source ⟶ power original target
  monotonicity : Monotonicity original operation
  unit : (functions original target).meet
      (precomposition original route ≫ operation) (𝟙 (power original target)) = 𝟙 _
  counit : (functions original source).meet (𝟙 (power original source))
      (operation ≫ precomposition original route) = operation ≫ precomposition original route

namespace Universal

variable (quantifier : Universal original route)

theorem unit_at {context : C} (predicate : context ⟶ power original target) :
    (functions original target).meet
      ((predicate ≫ precomposition original route) ≫ quantifier.operation) predicate = predicate := by
  have natural := (functions original target).reindex_meet predicate
    (precomposition original route ≫ quantifier.operation) (𝟙 _)
  have complete := natural.symm.trans (congrArg (fun arrow => predicate ≫ arrow) quantifier.unit)
  simpa only [Operations.reindex, Category.comp_id, ← Category.assoc] using complete

theorem counit_at {context : C} (predicate : context ⟶ power original source) :
    (functions original source).meet predicate
      ((predicate ≫ quantifier.operation) ≫ precomposition original route) =
    (predicate ≫ quantifier.operation) ≫ precomposition original route := by
  have natural := (functions original source).reindex_meet predicate
    (𝟙 _) (quantifier.operation ≫ precomposition original route)
  have complete := natural.symm.trans (congrArg (fun arrow => predicate ≫ arrow) quantifier.counit)
  simpa only [Operations.reindex, Category.comp_id, ← Category.assoc] using complete

theorem adjunction (context : C) :
    letI : SemilatticeInf (context ⟶ power original target) :=
      (functions original target).semilattice (functionLaws original originalLaws target) context
    letI : SemilatticeInf (context ⟶ power original source) :=
      (functions original source).semilattice (functionLaws original originalLaws source) context
    GaloisConnection
      (fun predicate : context ⟶ power original target =>
        (predicate ≫ precomposition original route : context ⟶ power original source))
      (fun predicate : context ⟶ power original source =>
        (predicate ≫ quantifier.operation : context ⟶ power original target)) := by
  let : SemilatticeInf (context ⟶ power original target) :=
    (functions original target).semilattice (functionLaws original originalLaws target) context
  let : SemilatticeInf (context ⟶ power original source) :=
    (functions original source).semilattice (functionLaws original originalLaws source) context
  intro first second
  constructor
  · intro ordered
    have preserved := monotone_from_diagram original originalLaws quantifier.operation
      quantifier.monotonicity context ordered
    have unitBound : first ≤ (first ≫ precomposition original route) ≫ quantifier.operation :=
      unit_at original route quantifier first
    exact unitBound.trans preserved
  · intro ordered
    have preserved := precomposition_mono original originalLaws route context ordered
    have counitBound : (second ≫ quantifier.operation) ≫ precomposition original route ≤ second :=
      counit_at original route quantifier second
    exact preserved.trans counitBound

end Universal

end Mettapedia.CategoryTheory.InternalPredicateQuantifier
