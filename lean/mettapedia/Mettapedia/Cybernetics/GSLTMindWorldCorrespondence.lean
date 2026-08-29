import Mettapedia.Cybernetics.MindWorldApproximateFunctor
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Operational GSLTs as exact mind--world correspondences

The mind--world correspondence interface is deliberately more general than a
functor: a learned or compressed cognitive map may have measurable identity
and composition defects.  A proved operational translation between GSLTs is
the exact special case.

This module connects the two layers without identifying them.  Every
`OperationalTranslation` already induces a functor between free categories of
proof-relevant execution paths.  That functor embeds as a zero-budget
`BoundedPathCorrespondence`.  A simple route-length geometry is preserved
exactly because operational translation preserves every retained step.

Route length is only a minimal structural cost model.  The full resource
account may replace it with an authored engine meter while retaining the same
correspondence interface.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.GSLTMindWorldCorrespondence

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.Cybernetics.MindWorldApproximateFunctor

universe uTerm

/-! ## A structural geometry on finite executions -/

/-- Pull the ordinary real metric back along route length.  It forgets which
steps occurred while retaining a genuine distance between their structural
sizes. -/
noncomputable def routeLengthGeometry (system : GSLT.{uTerm})
    (source target : ExecutionObject system) :
    ValueGeometry (source ⟶ target) :=
  (ValueGeometry.ofPseudoMetric ℝ).comap
    (fun route : source ⟶ target => (route.length : ℝ))

theorem routeLengthGeometry_symmetric (system : GSLT.{uTerm})
    (source target : ExecutionObject system) :
    (routeLengthGeometry system source target).Symmetric := by
  intro first second
  change dist (first.length : ℝ) (second.length : ℝ) =
    dist (second.length : ℝ) (first.length : ℝ)
  exact dist_comm _ _

/-- Mapping a complete execution preserves the route-length geometry, not
merely the endpoints of the route. -/
theorem mapRoute_preserves_routeLengthGeometry
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (first last : ExecutionObject source) :
    (routeLengthGeometry source first last).Preserves
      (routeLengthGeometry target
        (translation.mapTerm first) (translation.mapTerm last))
      translation.mapRoute := by
  intro earlier later
  change
    dist ((translation.mapRoute earlier).length : ℝ)
        ((translation.mapRoute later).length : ℝ) =
      dist (earlier.length : ℝ) (later.length : ℝ)
  rw [translation.mapRoute_length, translation.mapRoute_length]

/-! ## Exact operational realization -/

/-- A proved operational translation is a zero-budget mind--world path
correspondence.  Its target path geometry is the structural route-length
geometry above. -/
noncomputable def exactCorrespondence
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    BoundedPathCorrespondence
      (ExecutionObject source) (ExecutionObject target) :=
  BoundedPathCorrespondence.ofFunctor translation.pathFunctor
    (fun first last => routeLengthGeometry target
      (translation.mapTerm first) (translation.mapTerm last))

@[simp] theorem exactCorrespondence_obj
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (term : ExecutionObject source) :
    (exactCorrespondence translation).obj term = translation.mapTerm term :=
  rfl

@[simp] theorem exactCorrespondence_map
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {first last : ExecutionObject source} (route : first ⟶ last) :
    (exactCorrespondence translation).map route = translation.mapRoute route :=
  rfl

theorem exactCorrespondence_exact
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    (exactCorrespondence translation).toPathCorrespondence.Exact :=
  BoundedPathCorrespondence.ofFunctor_exact translation.pathFunctor
    (fun first last => routeLengthGeometry target
      (translation.mapTerm first) (translation.mapTerm last))

theorem exactCorrespondence_identityDefect_zero
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (term : ExecutionObject source) :
    (exactCorrespondence translation).toPathCorrespondence.identityDefect term =
      0 :=
  PathCorrespondence.identityDefect_eq_zero_of_exact
    (exactCorrespondence translation).toPathCorrespondence
    (exactCorrespondence_exact translation) term

theorem exactCorrespondence_compositionDefect_zero
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {first middle last : ExecutionObject source}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (exactCorrespondence translation).toPathCorrespondence.compositionDefect
        earlier later = 0 :=
  PathCorrespondence.compositionDefect_eq_zero_of_exact
    (exactCorrespondence translation).toPathCorrespondence
    (exactCorrespondence_exact translation) earlier later

/-! ## Goal and structural cost readouts -/

/-- Equip the exact operational map with an independently authored goal
weight and the minimal route-length resource cost. -/
noncomputable def withGoalAndRouteCost
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (goalWeight : {first last : ExecutionObject source} →
      (first ⟶ last) → ℝ)
    (goalWeight_nonnegative : ∀ {first last : ExecutionObject source}
      (route : first ⟶ last), 0 ≤ goalWeight route) :
    MindWorldCorrespondence
      (ExecutionObject source) (ExecutionObject target) where
  toBoundedPathCorrespondence := exactCorrespondence translation
  goalWeight := goalWeight
  resourceCost := fun route => (route.length : ℝ)
  goalWeight_nonnegative := goalWeight_nonnegative
  resourceCost_nonnegative := by
    intro first last route
    positivity

@[simp] theorem withGoalAndRouteCost_resourceCost
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (goalWeight : {first last : ExecutionObject source} →
      (first ⟶ last) → ℝ)
    (goalWeight_nonnegative : ∀ {first last : ExecutionObject source}
      (route : first ⟶ last), 0 ≤ goalWeight route)
    {first last : ExecutionObject source} (route : first ⟶ last) :
    (withGoalAndRouteCost translation goalWeight
      goalWeight_nonnegative).resourceCost route = (route.length : ℝ) :=
  rfl

/-- The structural resource readout agrees before and after the operational
translation because no retained step is invented or dropped. -/
theorem withGoalAndRouteCost_cost_preserved
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (goalWeight : {first last : ExecutionObject source} →
      (first ⟶ last) → ℝ)
    (goalWeight_nonnegative : ∀ {first last : ExecutionObject source}
      (route : first ⟶ last), 0 ≤ goalWeight route)
    {first last : ExecutionObject source} (route : first ⟶ last) :
    (withGoalAndRouteCost translation goalWeight
        goalWeight_nonnegative).resourceCost route =
      ((translation.mapRoute route).length : ℝ) := by
  rw [withGoalAndRouteCost_resourceCost, translation.mapRoute_length]

theorem withGoalAndRouteCost_exact
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (goalWeight : {first last : ExecutionObject source} →
      (first ⟶ last) → ℝ)
    (goalWeight_nonnegative : ∀ {first last : ExecutionObject source}
      (route : first ⟶ last), 0 ≤ goalWeight route) :
    (withGoalAndRouteCost translation goalWeight
      goalWeight_nonnegative).toPathCorrespondence.Exact :=
  exactCorrespondence_exact translation

/-! ## Negative realization control -/

/-- A correspondence is operationally realized here when it is exactly the
path functor of some step-preserving GSLT translation with the structural
route geometry. -/
def OperationallyRealized
    {source target : GSLT.{uTerm}}
    (correspondence : PathCorrespondence
      (ExecutionObject source) (ExecutionObject target)) : Prop :=
  ∃ translation : OperationalTranslation source target,
    correspondence = (exactCorrespondence translation).toPathCorrespondence

/-- A positive composition defect is a concrete obstruction to realization
by any exact operational translation. -/
theorem positive_compositionDefect_not_operationallyRealized
    {source target : GSLT.{uTerm}}
    (correspondence : PathCorrespondence
      (ExecutionObject source) (ExecutionObject target))
    {first middle last : ExecutionObject source}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (positive : 0 < correspondence.compositionDefect earlier later) :
    ¬ OperationallyRealized correspondence := by
  intro realized
  apply correspondence.positive_compositionDefect_not_exact
    earlier later positive
  obtain ⟨translation, equality⟩ := realized
  rw [equality]
  exact exactCorrespondence_exact translation

/-! ## Axiom audit -/

#print axioms routeLengthGeometry_symmetric
#print axioms mapRoute_preserves_routeLengthGeometry
#print axioms exactCorrespondence_exact
#print axioms exactCorrespondence_compositionDefect_zero
#print axioms withGoalAndRouteCost_cost_preserved
#print axioms positive_compositionDefect_not_operationallyRealized

end Mettapedia.Cybernetics.GSLTMindWorldCorrespondence
