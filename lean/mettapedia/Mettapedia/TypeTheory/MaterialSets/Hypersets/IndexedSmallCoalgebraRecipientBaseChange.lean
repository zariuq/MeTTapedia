import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange

/-!
# Substitution of the constructed parameter-slice recipient

The recipient over C is compared with the literal pullback of the recipient
over B along an arbitrary natural map C → B. The pulled coalgebra is built
using the independent indexed-power base-change construction. The comparison
and its inverse preserve whole future-child predicates, retained parameters
and behavioral values. Their inverse laws hold for whole natural maps and
compatible sections, including noninjective substitutions.

This proves substitution coherence for the constructed small-source class.
It does not select uniform enumerations from mere cover existence or assume
finality for every coalgebra whose branches are merely covered.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipientBaseChange

open _root_.CategoryTheory CoveredFuturePowerFunctor
open CoveredFuturePowerFamilies (Predicate)
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization (pullback pullbackFirst pullbackSecond)
open IndexedSmallCoalgebraRecipient

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (B : D ⥤ Type v) (C : D ⥤ Type w) (change : NaturalHom C B)

abbrev pulledFamily := pullback (parameter B) change
abbrev pulledParameter := pullbackSecond (parameter B) change
abbrev originalProjection := pullbackFirst (parameter B) change

def forward : NaturalHom (family C) (pulledFamily B C change) where
  app point value := ⟨((change.app point value.1, value.2), value.1), rfl⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext (Prod.ext (change.naturality step value.1) rfl) rfl

def backward : NaturalHom (pulledFamily B C change) (family C) where
  app _ value := (value.val.2, value.val.1.2)
  naturality _ _ := rfl

theorem backward_forward (point : D) (value : (family C).obj point) :
    (backward B C change).app point ((forward B C change).app point value) = value :=
  Prod.ext rfl rfl

theorem forward_backward (point : D) (value : (pulledFamily B C change).obj point) :
    (forward B C change).app point ((backward B C change).app point value) = value := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext value.property.symm rfl) rfl

theorem backward_forward_hom : (forward B C change).comp (backward B C change) = identityHom (family C) := by
  apply NaturalHom.ext
  exact backward_forward B C change

theorem forward_backward_hom :
    (backward B C change).comp (forward B C change) = identityHom (pulledFamily B C change) := by
  apply NaturalHom.ext
  exact forward_backward B C change

theorem forward_parameter : (forward B C change).comp (pulledParameter B C change) = parameter C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_parameter : (backward B C change).comp (parameter C) = pulledParameter B C change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem forward_behavior :
    (forward B C change).comp ((originalProjection B C change).comp (behavior B)) = behavior C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_behavior :
    (backward B C change).comp (behavior C) = (originalProjection B C change).comp (behavior B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def fibreEquiv (point : D) : (family C).obj point ≃ (pulledFamily B C change).obj point where
  toFun := (forward B C change).app point
  invFun := (backward B C change).app point
  left_inv := backward_forward B C change point
  right_inv := forward_backward B C change point

def sectionEquiv : (family C).sections ≃ (pulledFamily B C change).sections where
  toFun := (forward B C change).mapSection
  invFun := (backward B C change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact backward_forward B C change point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact forward_backward B C change point (term.val point)

def coalgebraEntry : NaturalHom (pulledFamily B C change)
    (IndexedCoveredPowerBaseChange.baseFamily (parameter B) change) where
  app point value := ⟨((indexedCoalgebra B).app point value.val.1, value.val.2), value.property⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext ((indexedCoalgebra B).naturality step value.val.1) rfl

def pulledIndexedCoalgebra : NaturalHom (pulledFamily B C change)
    (IndexedCoveredPower.family (pulledParameter B C change)) :=
  (coalgebraEntry B C change).comp (IndexedCoveredPowerBaseChange.backward (parameter B) change)

def pulledCoalgebra : NaturalHom (pulledFamily B C change)
    (CoveredFuturePowerFamilies.family (pulledFamily B C change)) :=
  (pulledIndexedCoalgebra B C change).comp (IndexedCoveredPower.predicateProjection (pulledParameter B C change))

theorem pulled_parameter_square :
    (pulledIndexedCoalgebra B C change).comp
      (IndexedCoveredPower.projection (pulledParameter B C change)) = pulledParameter B C change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem original_square :
    (pulledCoalgebra B C change).comp (imageHom (originalProjection B C change)) =
      (originalProjection B C change).comp (coalgebra B) := by
  apply NaturalHom.ext
  intro point value
  exact IndexedCoveredPowerBaseChange.image_lift (parameter B) change point value.val.2
    ((coalgebra B).app point value.val.1)
    (IndexedCoveredPowerBaseChange.input_support (parameter B) change point
      ((coalgebraEntry B C change).app point value))

theorem forward_square : (coalgebra C).comp (imageHom (forward B C change)) =
    (forward B C change).comp (pulledCoalgebra B C change) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  change (∃ child : (family C).obj future.1.1,
    (forward B C change).app future.1.1 child = future.2 ∧
      (children C point value).holds ⟨future.1, child⟩) ↔
    ((behaviorCoalgebra.app point value.2).val.holds ⟨future.1, future.2.val.1.2⟩ ∧
      future.2.val.1.1 = B.map future.1.2 (change.app point value.1)) ∧
        future.2.val.2 = C.map future.1.2 value.1
  constructor
  · rintro ⟨child, same, admitted, supported⟩
    have behavioral := congrArg (fun pair : (pulledFamily B C change).obj future.1.1 => pair.val.1.2) same
    have parameterEq := congrArg (fun pair : (pulledFamily B C change).obj future.1.1 => pair.val.2) same
    have originalParameter := congrArg (fun pair : (pulledFamily B C change).obj future.1.1 => pair.val.1.1) same
    refine ⟨⟨?_, ?_⟩, parameterEq.symm.trans supported⟩
    · rw [← behavioral]
      exact admitted
    · exact originalParameter.symm.trans ((congrArg (change.app future.1.1) supported).trans
        (change.naturality future.1.2 value.1).symm)
  · rintro ⟨⟨admitted, _originalParameter⟩, supported⟩
    refine ⟨(future.2.val.2, future.2.val.1.2), ?_, admitted, supported⟩
    apply Subtype.ext
    exact Prod.ext (Prod.ext future.2.property.symm rfl) rfl

theorem backward_square : (pulledCoalgebra B C change).comp (imageHom (backward B C change)) =
    (backward B C change).comp (coalgebra C) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  change (∃ child : (pulledFamily B C change).obj future.1.1,
    (backward B C change).app future.1.1 child = future.2 ∧
      ((coalgebra B).app point value.val.1).val.holds ⟨future.1, child.val.1⟩ ∧
        child.val.2 = C.map future.1.2 value.val.2) ↔
    (behaviorCoalgebra.app point value.val.1.2).val.holds ⟨future.1, future.2.2⟩ ∧
      future.2.1 = C.map future.1.2 value.val.2
  constructor
  · rintro ⟨child, same, ⟨admitted, _originalParameter⟩, supported⟩
    exact ⟨by rw [← congrArg Prod.snd same]; exact admitted,
      (congrArg Prod.fst same).symm.trans supported⟩
  · rintro ⟨admitted, supported⟩
    let child : (pulledFamily B C change).obj future.1.1 :=
      ⟨((change.app future.1.1 future.2.1, future.2.2), future.2.1), rfl⟩
    refine ⟨child, rfl, ⟨admitted, ?_⟩, supported⟩
    exact (congrArg (change.app future.1.1) supported).trans
      ((change.naturality future.1.2 value.val.2).symm.trans
        (congrArg (B.map future.1.2) value.property).symm)

theorem forward_indexed_square :
    (indexedCoalgebra C).comp (IndexedCoveredPower.image (parameter C) (pulledParameter B C change)
      (forward B C change) (forward_parameter B C change)) =
        (forward B C change).comp (pulledIndexedCoalgebra B C change) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext rfl (congrArg
    (fun operation : NaturalHom (family C) (CoveredFuturePowerFamilies.family (pulledFamily B C change)) =>
      operation.app point value) (forward_square B C change))

theorem backward_indexed_square :
    (pulledIndexedCoalgebra B C change).comp (IndexedCoveredPower.image (pulledParameter B C change) (parameter C)
      (backward B C change) (backward_parameter B C change)) =
        (backward B C change).comp (indexedCoalgebra C) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext rfl (congrArg
    (fun operation : NaturalHom (pulledFamily B C change) (CoveredFuturePowerFamilies.family (family C)) =>
      operation.app point value) (backward_square B C change))

def reindex : NaturalHom (family C) (family B) :=
  (forward B C change).comp (originalProjection B C change)

theorem reindex_value (point : D) (value : (family C).obj point) :
    (reindex B C change).app point value = (change.app point value.1, value.2) := rfl

theorem reindex_square : (coalgebra C).comp (imageHom (reindex B C change)) =
    (reindex B C change).comp (coalgebra B) :=
  ContextualSmallCoalgebraComparisons.compose_square (coalgebra C) (pulledCoalgebra B C change)
    (coalgebra B) (forward B C change) (originalProjection B C change)
    (forward_square B C change) (original_square B C change)

theorem reindex_parameter : (reindex B C change).comp (parameter B) = (parameter C).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_behavior : (reindex B C change).comp (behavior B) = behavior C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_kernel (point : D) (left right : (family C).obj point) :
    (reindex B C change).app point left = (reindex B C change).app point right ↔
      change.app point left.1 = change.app point right.1 ∧ left.2 = right.2 :=
  ⟨fun same => ⟨congrArg (fun pair : (family B).obj point => pair.1) same,
      congrArg (fun pair : (family B).obj point => pair.2) same⟩,
    fun same => Prod.ext same.1 same.2⟩

theorem reindex_identity : reindex B B (identityHom B) = identityHom (family B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_composition {E : D ⥤ Type z} (next : NaturalHom E C) :
    (reindex C E next).comp (reindex B C change) = reindex B E (next.comp change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem whole_reindexed_section (term : (family C).sections) :
    (reindex B C change).mapSection term =
      (originalProjection B C change).mapSection ((forward B C change).mapSection term) := by
  apply Subtype.ext
  funext point
  rfl

theorem pulled_relative_separated (point : D) {left right : (pulledFamily B C change).obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar (pulledCoalgebra B C change) point left right)
    (sameBase : left.val.2 = right.val.2) : left = right := by
  have readingEq := relative_separated C point
    (ContextualCoalgebraBisimulation.bisimilar_preserved (pulledCoalgebra B C change)
      (backward B C change) (coalgebra C) (backward_square B C change) related) sameBase
  exact (forward_backward B C change point left).symm.trans
    ((congrArg ((forward B C change).app point) readingEq).trans
      (forward_backward B C change point right))

section SmallSource

variable {A : D ⥤ Type u} (sourceParameter : NaturalHom A C)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def pulledSmallReadout : NaturalHom A (pulledFamily B C change) :=
  (fromSmall C sourceParameter transition).comp (forward B C change)

include sourceSquare in
theorem pulled_small_square :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (pulledSmallReadout B C change sourceParameter transition)) =
        (pulledSmallReadout B C change sourceParameter transition).comp (pulledCoalgebra B C change) :=
  ContextualSmallCoalgebraComparisons.compose_square
    (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra C)
    (pulledCoalgebra B C change) (fromSmall C sourceParameter transition) (forward B C change)
    (pairReadout_square C sourceParameter transition sourceSquare
      (ContextualEnumeratedCoalgebraReadout.readout A
        (IndexedCoalgebraBisimulation.original sourceParameter transition)
          (smallReceipts C sourceParameter transition))
      (ContextualEnumeratedCoalgebraReadout.readout_square A
        (IndexedCoalgebraBisimulation.original sourceParameter transition)
          (smallReceipts C sourceParameter transition)))
    (forward_square B C change)

theorem pulled_small_parameter :
    (pulledSmallReadout B C change sourceParameter transition).comp (pulledParameter B C change) =
      sourceParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

include sourceSquare in
theorem unique_small_pulled_map : ∃! operation : NaturalHom A (pulledFamily B C change),
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
      operation.comp (pulledCoalgebra B C change) ∧
        operation.comp (pulledParameter B C change) = sourceParameter := by
  let actual := pulledSmallReadout B C change sourceParameter transition
  have square := pulled_small_square B C change sourceParameter transition sourceSquare
  have base := pulled_small_parameter B C change sourceParameter transition
  refine ⟨actual, ⟨square, base⟩, ?_⟩
  intro candidate laws
  apply NaturalHom.ext
  intro point value
  apply pulled_relative_separated B C change point
  · exact ContextualCoalgebraBisimulation.greatest (pulledCoalgebra B C change)
      (ContextualSmallCoalgebraGenerators.mixed_image_isBisimulation
        (IndexedCoalgebraBisimulation.original sourceParameter transition) (pulledCoalgebra B C change)
        candidate actual laws.1 square) ⟨value, rfl, rfl⟩
  · exact (congrArg (fun operation : NaturalHom A C => operation.app point value) laws.2).trans
      (congrArg (fun operation : NaturalHom A C => operation.app point value) base).symm

end SmallSource

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipientBaseChange
