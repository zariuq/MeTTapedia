import Mathlib.CategoryTheory.Products.Basic
import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mettapedia.GSLT.Core.StagePerspectiveProfunctor

/-!
# Constraint transport across ultrainfinite perspectives

Fixing one perspective in a stage--perspective profunctor produces a
presheaf over stages, hence a `ComputationalTrinity.Face`.  A morphism between
perspectives induces a natural transformation between these faces by
postcomposition.  Fragment constraints can therefore be sent forward or
pulled backward along perspective refinement.

This module is a bridge, not a selection of a language or type theory.  It
connects the existing ultrainfinite stage/perspective geometry to the
fragmentwise trinity calculus while leaving every concrete face and adequacy
claim to an explicit instantiation.
-/

namespace Mettapedia.Computability.StagePerspectiveConstraintTransport

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity
open Mettapedia.GSLT.Ultrainfinite

universe uC vC uJ vJ uI vI

variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]
variable {I : Type uI} [Category.{vI} I]

/-- The variable set over stages seen at one perspective.  This is exactly a
trinity face: stage substitution acts contravariantly by precomposition. -/
def stageVariableSetAt
    (stages : J ⥤ C) (shadows : I ⥤ C) (perspective : I) :
    Face.{uJ, vJ, vC} J :=
  stagePerspectiveProfunctor stages shadows ⋙
    (evaluation I (Type vC)).obj perspective

/-- Refining a perspective changes the corresponding stage-indexed variable
set by postcomposition with the shadow map. -/
def perspectiveChange
    (stages : J ⥤ C) (shadows : I ⥤ C)
    {first second : I} (perspectiveMap : first ⟶ second) :
    stageVariableSetAt stages shadows first ⟶
      stageVariableSetAt stages shadows second where
  app stage :=
    (stagePerspectiveProfunctor stages shadows).obj stage |>.map perspectiveMap
  naturality := by
    intro firstStage secondStage stageMap
    exact
      ((stagePerspectiveProfunctor stages shadows).map stageMap |>.naturality
        perspectiveMap).symm

/-- A substitution-stable requirement on the stage-indexed variable set seen
from one perspective. -/
abbrev PerspectiveConstraint
    (stages : J ⥤ C) (shadows : I ⥤ C) (perspective : I) :=
  Constraint (stageVariableSetAt stages shadows perspective)

/-- Forward and backward pressure across a perspective change satisfy the
same adjunction as every other trinity interpretation.  No direction is
privileged: an admitted earlier-view fragment may be projected forward, and
a later-view requirement may be pulled back. -/
theorem perspective_pressure_adjunction
    (stages : J ⥤ C) (shadows : I ⥤ C)
    {first second : I} (perspectiveMap : first ⟶ second)
    (sourceConstraint : PerspectiveConstraint stages shadows first)
    (targetConstraint : PerspectiveConstraint stages shadows second) :
    (sourceConstraint.pushforward
        (perspectiveChange stages shadows perspectiveMap)).Entails
          targetConstraint ↔
      sourceConstraint.Entails
        (targetConstraint.pullback
          (perspectiveChange stages shadows perspectiveMap)) :=
  Constraint.pushforward_entails_iff_entails_pullback
    (perspectiveChange stages shadows perspectiveMap)
    sourceConstraint targetConstraint

/-- If perspective refinement identifies two stage views, no requirement
pulled back from the refined perspective can distinguish them. -/
theorem refined_perspective_cannot_recover_fibre_distinction
    (stages : J ⥤ C) (shadows : I ⥤ C)
    {first second : I} (perspectiveMap : first ⟶ second)
    (sourceConstraint : PerspectiveConstraint stages shadows first)
    (targetConstraint : PerspectiveConstraint stages shadows second)
    {stage : Jᵒᵖ}
    {left right : (stageVariableSetAt stages shadows first).obj stage}
    (sameRefinedView :
      (perspectiveChange stages shadows perspectiveMap).app stage left =
        (perspectiveChange stages shadows perspectiveMap).app stage right)
    (leftAdmitted : sourceConstraint.holds stage left)
    (rightRejected : ¬ sourceConstraint.holds stage right) :
    ¬ sourceConstraint.Equivalent
      (targetConstraint.pullback
        (perspectiveChange stages shadows perspectiveMap)) :=
  Constraint.not_equivalent_pullback_of_separates_fibre
    (perspectiveChange stages shadows perspectiveMap)
    sourceConstraint targetConstraint sameRefinedView
    leftAdmitted rightRejected

#print axioms stageVariableSetAt
#print axioms perspectiveChange
#print axioms perspective_pressure_adjunction
#print axioms refined_perspective_cannot_recover_fibre_distinction

end Mettapedia.Computability.StagePerspectiveConstraintTransport
