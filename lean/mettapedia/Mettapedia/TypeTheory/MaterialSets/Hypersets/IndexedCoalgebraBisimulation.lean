import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPower
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
import Mettapedia.TypeTheory.ContextualKernelQuotients

/-!
# Bisimulation retaining a contextual base parameter

An actual indexed coalgebra retains its parameter and its full-future
supported child predicate. Its behavioral relation additionally requires
equality of the retained parameter. Future support proves that this
intersection is itself a bisimulation, and it is greatest among
parameter-respecting bisimulations.

The paired parameter/behavioral observation has exactly this kernel.
No dictionary or representative of the independently larger parameter
type is selected. Indexed finality is not inferred from this quotient
relation alone.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraBisimulation

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w}
variable (parameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family parameter))
variable (parameterSquare : transition.comp (IndexedCoveredPower.projection parameter) = parameter)

def original : NaturalHom A (family A) :=
  transition.comp (IndexedCoveredPower.predicateProjection parameter)

include parameterSquare in
theorem future_support (point : D) (argument : A.obj point) (future : Arguments A point)
    (admitted : ((original parameter transition).app point argument).val.holds future) :
    parameter.app future.1.1 future.2 = B.map future.1.2 (parameter.app point argument) := by
  have saved := congrArg (fun operation : NaturalHom A B => operation.app point argument) parameterSquare
  exact ((transition.app point argument).property future admitted).trans
    (congrArg (B.map future.1.2) saved)

def Related (point : D) (left right : A.obj point) : Prop :=
  ContextualCoalgebraBisimulation.Bisimilar (original parameter transition) point left right ∧
    parameter.app point left = parameter.app point right

theorem related_refl (point : D) (argument : A.obj point) :
    Related parameter transition point argument argument :=
  ⟨ContextualCoalgebraBisimulation.bisimilar_refl (original parameter transition) point argument, rfl⟩

theorem related_symm {point : D} {left right : A.obj point}
    (related : Related parameter transition point left right) : Related parameter transition point right left :=
  ⟨ContextualCoalgebraBisimulation.bisimilar_symm (original parameter transition) related.1, related.2.symm⟩

theorem related_trans {point : D} {left middle right : A.obj point}
    (earlier : Related parameter transition point left middle)
    (later : Related parameter transition point middle right) : Related parameter transition point left right :=
  ⟨ContextualCoalgebraBisimulation.bisimilar_trans (original parameter transition) earlier.1 later.1,
    earlier.2.trans later.2⟩

theorem related_stable {first second : D} (step : first ⟶ second) {left right : A.obj first}
    (related : Related parameter transition first left right) :
    Related parameter transition second (A.map step left) (A.map step right) :=
  ⟨ContextualCoalgebraBisimulation.bisimilar_stable (original parameter transition) step related.1,
    (parameter.naturality step left).symm.trans
      ((congrArg (B.map step) related.2).trans (parameter.naturality step right))⟩

include parameterSquare in
theorem related_isBisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation (original parameter transition) (Related parameter transition) where
  stable {_ _} step {_ _} related := related_stable parameter transition step related
  forth {point left right} related future {child} admitted := by
    obtain ⟨matching, matched, children⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (original parameter transition)).forth
        related.1 future admitted
    exact ⟨matching, matched, children,
      (future_support parameter transition parameterSquare point left ⟨future, child⟩ admitted).trans
        ((congrArg (B.map future.2) related.2).trans
          (future_support parameter transition parameterSquare point right ⟨future, matching⟩ matched).symm)⟩
  back {point left right} related future {child} admitted := by
    obtain ⟨matching, matched, children⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (original parameter transition)).back
        related.1 future admitted
    exact ⟨matching, matched, children,
      (future_support parameter transition parameterSquare point left ⟨future, matching⟩ matched).trans
        ((congrArg (B.map future.2) related.2).trans
          (future_support parameter transition parameterSquare point right ⟨future, child⟩ admitted).symm)⟩

theorem greatest {relation : ContextualCoalgebraBisimulation.Relation A}
    (bisimulation : ContextualCoalgebraBisimulation.IsBisimulation (original parameter transition) relation)
    (overBase : ∀ point {left right}, relation point left right →
      parameter.app point left = parameter.app point right)
    {point : D} {left right : A.obj point} (related : relation point left right) :
    Related parameter transition point left right :=
  ⟨ContextualCoalgebraBisimulation.greatest (original parameter transition) bisimulation related,
    overBase point related⟩

def setoid (point : D) : Setoid (A.obj point) where
  r := Related parameter transition point
  iseqv := ⟨related_refl parameter transition point,
    related_symm parameter transition, related_trans parameter transition⟩

def observation : NaturalHom A
    (CoveredFuturePowerClassifier.product B (ContextualCoalgebraQuotient.family (original parameter transition))) :=
  CoveredFuturePowerClassifier.pair B (ContextualCoalgebraQuotient.family (original parameter transition))
    parameter (ContextualCoalgebraQuotient.projection (original parameter transition))

theorem observation_eq_iff (point : D) (left right : A.obj point) :
    (observation parameter transition).app point left = (observation parameter transition).app point right ↔
      Related parameter transition point left right := by
  constructor
  · intro same
    exact ⟨(ContextualCoalgebraQuotient.projection_eq_iff (original parameter transition) point left right).mp
      (congrArg Prod.snd same), congrArg Prod.fst same⟩
  · intro related
    exact Prod.ext related.2
      ((ContextualCoalgebraQuotient.projection_eq_iff (original parameter transition) point left right).mpr related.1)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraBisimulation
