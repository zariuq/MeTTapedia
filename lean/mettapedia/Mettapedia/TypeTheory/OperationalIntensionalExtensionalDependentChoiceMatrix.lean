import Mettapedia.TypeTheory.DiscreteOnDependentRightAdjoint
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentFactorization

/-!
# Choice matrix for dependent operational, intensional, and extensional modes

The three context adjunctions do not lift symmetrically to dependent types.
This file records the current exact boundary in one theorem:

* free evidence completion, route quotient, and the discrete embedding each
  have an unconditional dependent-right-adjoint orientation;
* reusing an operational family unchanged in the reverse evidence direction
  can fail precisely at reflexivity coherence;
* bare point fibres need not carry the route action required in the reverse
  discrete/points direction;
* the quotient right action has a proper image among intensional families;
  and
* operational observation still factors through evidence completion at the
  dependent level.

The negative clauses are deliberately narrow.  They refute universal
unchanged reuse, not every possible repaired, restricted, or separately
structured dependent lift.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentChoiceMatrix

open CategoryTheory
open Mettapedia.TypeTheory.CwfDependentRightAdjoint
open Mettapedia.TypeTheory.DiscreteOnDependentRightAdjoint
open Mettapedia.TypeTheory.EvidenceCompletionDependentRightAdjoint
open Mettapedia.TypeTheory.OperationalFamilyCwf
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentFactorization
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

/-- The complete currently proved dependent-modality boundary for the
operational--intensional--extensional specimen.  Positive constructions and
negative controls occur in the same statement so that an unconditional DRA
cannot be confused with an unchanged reverse lift. -/
theorem dependent_modality_choice_matrix :
    Nonempty (DependentRightAdjoint dynCwf.{0} routeCwf.{0}) ∧
    Nonempty (DependentRightAdjoint routeCwf.{0} extCwf.{0}) ∧
    Nonempty (DependentRightAdjoint extCwf.{0} routeCwf.{0}) ∧
    (∃ (context : RouteType.{0})
        (family : DynFamily (forgetReflexivity.obj context)),
      ¬ Nonempty (UnchangedRouteLift family)) ∧
    (∃ (context : RouteType.{0})
        (family : context.carrier -> Type),
      ¬ Nonempty (RouteAction context family)) ∧
    (∃ (context : RouteType.{0}) (family : RouteFamily context),
      ¬ InRightImageUpToFibreEquivalence context family) ∧
    (∀ context : DynSys.{0},
      Nonempty
        (routeQuotient.obj (evidenceCompletion.obj context) ≅
          dynQuotient.obj context)) := by
  refine ⟨⟨evidenceCompletionDra⟩, ⟨routeQuotientDra⟩,
    ⟨discreteOnDra⟩, ?_, ?_, ?_, ?_⟩
  · exact
      ⟨ReflexivityCanary.point, ReflexivityCanary.flipOnReflexivity,
        ReflexivityCanary.flipOnReflexivity_no_unchanged_lift⟩
  · exact
      ⟨PointsCanary.context, PointsCanary.family,
        PointsCanary.noRouteAction⟩
  · exact
      ⟨codiscretePair, RouteFamilyCwf.Canary.codiscreteVaryingFamily,
        Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint.Canary.codiscreteVaryingFamily_not_in_right_image⟩
  · intro context
    exact ⟨evidenceReadoutContextIso context⟩

#print axioms dependent_modality_choice_matrix

end Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentChoiceMatrix
