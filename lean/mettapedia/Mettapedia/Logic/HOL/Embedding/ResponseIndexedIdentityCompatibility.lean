import Mettapedia.Logic.HOL.Embedding.ResponseIndexedProtocolObservation
import Mettapedia.TypeTheory.ResponseIndexedIdentityComparison

/-!
# Extensional observation of response-indexed identity boundaries

The response-indexed protocol has an extensional HOL observation saying that
a phase is completed.  That predicate is exact for its stated meaning:
inhabitation of the dependent result fibre.  It is nevertheless deliberately
coarser than phase identity, because both distinct completed phases satisfy
it while their result fibres are different.

This module joins the existing intensional, operational, and extensional
comparison theorems on their shared protocol.  It neither selects a HOL
logical-principle package nor promotes completion equality to source identity,
judgmental conversion, or dependent transport.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ResponseIndexedIdentityCompatibility

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
open Mettapedia.Logic.HOL.Embedding.ResponseIndexedProtocolObservation
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.DecidableIdentityRouteStructure
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.OperationalConversionFamilyBoundary
open Mettapedia.TypeTheory.OperationalPathIdentityComparison
open Mettapedia.TypeTheory.ResponseIndexedIdentityComparison
open Mettapedia.TypeTheory.ResponseIndexedResultFamily
open Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

/-! ## The HOL predicate is exact at its declared observation level -/

/-- A protocol phase embedded in the standard model's carrier. -/
def phaseValue (phase : Phase) :
    Ty.denote.{0, 0} (liftedCarrier smallCarrier) (.base .phase) :=
  ⟨phase⟩

/-- The HOL predicate agrees pointwise with inhabitation of the dependent
result family. -/
theorem completed_predicate_iff_result_inhabited (phase : Phase) :
    (constantDenotation ObservationConst.completed (phaseValue phase)).down ↔
      Nonempty (Result phase) :=
  completed_denotes_result_inhabited (phaseValue phase)

/-- Both completed branches satisfy the extensional predicate. -/
theorem both_completed_branches_are_observed :
    (constantDenotation ObservationConst.completed
        (phaseValue Phase.unitDone)).down ∧
      (constantDenotation ObservationConst.completed
        (phaseValue Phase.boolDone)).down :=
  ⟨rfl, rfl⟩

/-- The predicate is correct for fibre inhabitation but is too coarse to
serve as phase identity or as a base for dependent result transport. -/
theorem completion_observation_boundary :
    (∀ phase,
      (constantDenotation ObservationConst.completed
          (phaseValue phase)).down ↔ Nonempty (Result phase)) ∧
      (constantDenotation ObservationConst.completed
        (phaseValue Phase.unitDone)).down ∧
      (constantDenotation ObservationConst.completed
        (phaseValue Phase.boolDone)).down ∧
      (¬ Nonempty
        (IntrinsicPhaseIdentity Phase.unitDone Phase.boolDone)) ∧
      (¬ Nonempty (FamilyFactorization completion Result)) :=
  ⟨completed_predicate_iff_result_inhabited,
    both_completed_branches_are_observed.1,
    both_completed_branches_are_observed.2,
    completedBranches_have_no_intrinsicIdentity,
    result_not_completion_determined⟩

/-! ## Four-face compatibility matrix -/

/-- The same finite corpus simultaneously supports:

* strict and intrinsic identity agreement;
* endpoint-changing operational routes that are not identity proofs;
* failure of the execution-generated conversion to transport `Result`; and
* a correct but deliberately coarse HOL completion predicate.

The result is a compatibility and non-collapse matrix, not a product-language
calculus selection. -/
theorem response_indexed_four_face_matrix :
    Nonempty (Structure StrictPhaseIdentity) ∧
      Nonempty
        (IdentityEliminationBeta (familiesCwf.{0})
          Mettapedia.TypeTheory.ContextualIdentityTypes.Families.identityFormation
          Mettapedia.TypeTheory.ContextualIdentityTypes.Families.identityReflexivity) ∧
      HasEndpointChangingRoute (executionLayer (lts codedQuery)) ∧
      (¬ Nonempty (Structure (executionLayer (lts codedQuery)))) ∧
      Nonempty
        (OperationalConversion Phase.unitDone Phase.boolDone) ∧
      (¬ Nonempty (FamilyTransport OperationalConversion Result)) ∧
      observationModel.models someCompleted ∧
      (¬ observationModel.models everyCompleted) ∧
      (∀ phase,
        (constantDenotation ObservationConst.completed
          (phaseValue phase)).down ↔ Nonempty (Result phase)) ∧
      (¬ Nonempty
        (IntrinsicPhaseIdentity Phase.unitDone Phase.boolDone)) ∧
      (¬ (simpleToDependentTypeFunctor Phase).essImage resultDisplay) ∧
      (¬ Nonempty (FamilyFactorization completion Result)) :=
  ⟨⟨strictPhaseIdentityStructure⟩,
    ⟨setFamiliesIdentityElimination⟩,
    protocolExecution_changes_endpoint,
    protocolExecution_has_no_identityStructure,
    ⟨completedBranchConversion⟩,
    result_has_no_operational_conversion_transport,
    observationModel_models_someCompleted,
    observationModel_not_models_everyCompleted,
    completed_predicate_iff_result_inhabited,
    completedBranches_have_no_intrinsicIdentity,
    resultDisplay_not_in_simple_essentialImage,
    result_not_completion_determined⟩

#print axioms completed_predicate_iff_result_inhabited
#print axioms both_completed_branches_are_observed
#print axioms completion_observation_boundary
#print axioms response_indexed_four_face_matrix

end Mettapedia.Logic.HOL.Embedding.ResponseIndexedIdentityCompatibility
