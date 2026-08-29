import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Core.ControlInfluenceSeparation
import Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission

/-!
# Downstream optimization authority

Optimization is not one undifferentiated permission.  Three transformations
occur at different semantic boundaries:

* representation optimization maps complete executions through an admitted,
  observation-preserving NIK refinement at a current dependency revision;
* scheduling optimization chooses an activation plan from completion demand
  and serializability evidence; and
* permanent pruning changes the live occurrence collection only with both an
  observer-preservation proof and an exact removed-occurrence ledger.

This module packages those authorities independently and proves their product
theorem.  The product retains three conclusions rather than collapsing them
into a Boolean "optimized" flag: semantic observation agreement, lawful
activation, and observer-preserving occurrence accounting.

Profitability, grades, and learned advice may propose one of these objects,
but do not occur in their authority fields.  Missing authority therefore
leaves the corresponding transformation unavailable rather than turning a
live possibility into a rejection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKDownstreamOptimizationAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe uCandidate uObservation uItem uGuard uView uReceipt
universe uActivationReceipt

/-! ## Revision-current representation authority -/

/-- Exact authority for one optimized representation.

The family recognizer supplies the shape witness, the hosted calculus supplies
the exact source authority, and the dependency system supplies currentness.
The structure contains no profitability or scheduling field. -/
structure RepresentationAuthority
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem)
    (preparedRevision currentRevision : dependencies.Revision)
    (candidate : Candidate) where
  exactAuthority : family.ExactAuthority candidate
  shape : family.ShapeEvidence candidate
  recognized : family.recognize candidate = some shape
  current : dependencies.SameDependencies preparedRevision currentRevision

namespace RepresentationAuthority

variable {Candidate : Type uCandidate} {Observation : Type uObservation}
variable {family : OptimizationFamily Candidate Observation}
variable {dependencies : DependencySystem}
variable {preparedRevision currentRevision : dependencies.Revision}
variable {candidate : Candidate}

/-- The exact optimized plan selected by the retained witnesses. -/
def plan
    (authority : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate) :
    Prepared family dependencies preparedRevision candidate :=
  .optimized authority.exactAuthority authority.shape

/-- Generic preparation selects exactly the witnesses retained by this
authority. -/
theorem prepare_eq_plan
    (authority : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate) :
    prepare family dependencies preparedRevision candidate
        (some authority.exactAuthority) = authority.plan := by
  simp [prepare, plan, authority.recognized]

/-- Currentness is inherited from the dependency fibre and supplies no new
execution function. -/
def planCurrent
    (authority : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate) :
    authority.plan.Current currentRevision :=
  authority.current

/-- Map one complete source execution through the retained optimized
refinement. -/
def mapPath
    (authority : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate)
    {first last : (family.source candidate).operational.theory.Term}
    (path : ExecutionPath (family.source candidate).operational.theory
      first last) :
    ExecutionPath authority.plan.target.operational.theory
      (authority.plan.toObservedRefinement.refinement.realization.mapTerm first)
      (authority.plan.toObservedRefinement.refinement.realization.mapTerm last) :=
  authority.plan.mapPath path

/-- The current optimized representation preserves the independently named
semantic observation. -/
theorem observationAgreement
    (authority : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate)
    {first last : (family.source candidate).operational.theory.Term}
    (path : ExecutionPath (family.source candidate).operational.theory
      first last) :
    authority.plan.target.observe (authority.mapPath path) =
      (family.source candidate).observe path :=
  authority.plan.observationAgreement path

end RepresentationAuthority

/-! ## Observer-relative control transformation authority -/

/-- Authority for a representation or scheduling transformation on retained
occurrences.  This covers reorderings and aggregations which do not
permanently remove occurrence mass. -/
structure ControlTransformationAuthority
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Item Guard View) (Receipt : Type uReceipt) where
  change : Change Item Receipt
  preserves : contract.Preserves change

namespace ControlTransformationAuthority

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {contract : Contract Item Guard View} {Receipt : Type uReceipt}

/-- Applying the admitted control transformation preserves exactly its named
observer. -/
theorem observation_eq
    (authority : ControlTransformationAuthority contract Receipt) :
    contract.observer.observe authority.change.target =
      contract.observer.observe authority.change.source :=
  authority.preserves.symm

end ControlTransformationAuthority

/-! ## Scheduling authority -/

/-- Authority to select an activation plan at one declared observation and
completion demand.  `BatchEvidence` is proof-relevant: a Boolean request for
bulk execution cannot manufacture serializability. -/
structure SchedulingAuthority
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Item Guard View)
    (step : List Item → Item → List Item)
    (initial batch : List Item) where
  branchAuthority : BranchAuthority
  evidence : Contract.BatchEvidence contract step initial batch

namespace SchedulingAuthority

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {contract : Contract Item Guard View}
variable {step : List Item → Item → List Item}
variable {initial batch : List Item}

/-- Execute only the strategy-neutral dispatcher justified by the supplied
completion and batch evidence. -/
def plan
    (authority : SchedulingAuthority contract step initial batch) : Plan :=
  contract.dispatchCertified authority.branchAuthority authority.evidence

/-- The selected activation plan stays within the declared scheduling
authority. -/
theorem lawful
    (authority : SchedulingAuthority contract step initial batch) :
    PlanLawful contract.demand authority.branchAuthority
      authority.evidence.authority authority.plan :=
  contract.dispatchCertified_lawful authority.branchAuthority
    authority.evidence

/-- Bulk activation reflects complete-bag demand. -/
theorem bulk_requires_completeBag
    (authority : SchedulingAuthority contract step initial batch)
    (bulk : authority.plan.activation = .bulk) :
    contract.demand.completion = .completeBag :=
  contract.bulk_requires_completeBag authority.branchAuthority
    authority.evidence bulk

/-- Bulk activation also reflects a real serializability proof at the named
observer. -/
theorem bulk_requires_serializable
    (authority : SchedulingAuthority contract step initial batch)
    (bulk : authority.plan.activation = .bulk) :
    SerializableAt contract.observer.observe step initial batch :=
  contract.bulk_requires_serializable authority.branchAuthority
    authority.evidence bulk

end SchedulingAuthority

/-! ## Permanent-pruning authority -/

/-- Permanent removal authority consists of an exact occurrence ledger and a
proof that the named observer cannot distinguish the change. -/
structure PruningAuthority
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Item Guard View) (Receipt : Type uReceipt) where
  pruning : PruningChange Item Receipt
  preserves : contract.Preserves pruning.toChange

namespace PruningAuthority

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {contract : Contract Item Guard View} {Receipt : Type uReceipt}

/-- The observer sees the retained target exactly as it saw the live source. -/
theorem observation_eq
    (authority : PruningAuthority contract Receipt) :
    contract.observer.observe authority.pruning.target =
      contract.observer.observe authority.pruning.source :=
  authority.preserves.symm

/-- Every permanently removed occurrence remains present in the exact
accounting equation. -/
theorem occurrence_accounting
    (authority : PruningAuthority contract Receipt) :
    (authority.pruning.source : Multiset Item) =
      (authority.pruning.target : Multiset Item) + authority.pruning.removed :=
  authority.pruning.accounting

end PruningAuthority

/-! ## Activation followed by permanent pruning -/

/-- A temporary active/deferred partition followed by an authorized prune of
the deferred portion.  Unselected work is still live until this additional
authority is supplied. -/
structure DispositionAuthority
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    (contract : Contract Item Guard View)
    (ActivationReceipt : Type uActivationReceipt)
    (PruningReceipt : Type uReceipt) where
  activation : ActivationPartition Item ActivationReceipt
  pruning : PruningAuthority contract PruningReceipt
  prunesDeferred : pruning.pruning.source = activation.deferred

namespace DispositionAuthority

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {contract : Contract Item Guard View}
variable {ActivationReceipt : Type uActivationReceipt}
variable {PruningReceipt : Type uReceipt}

/-- Activation and permanent pruning together preserve the named observation
at the prune boundary and account for every source occurrence across active,
retained, and explicitly removed classes. -/
theorem preserves_and_accounts
    (authority : DispositionAuthority contract ActivationReceipt
      PruningReceipt) :
    contract.observer.observe authority.pruning.pruning.source =
        contract.observer.observe authority.pruning.pruning.target ∧
      (((authority.activation.active ++ authority.pruning.pruning.target :
          List Item) : Multiset Item) + authority.pruning.pruning.removed =
        (authority.activation.source : Multiset Item)) := by
  constructor
  · exact authority.pruning.preserves
  · have deferredAccounting :
        (authority.activation.deferred : Multiset Item) =
          (authority.pruning.pruning.target : Multiset Item) +
            authority.pruning.pruning.removed := by
      rw [← authority.prunesDeferred]
      exact authority.pruning.pruning.accounting
    calc
      (((authority.activation.active ++ authority.pruning.pruning.target :
          List Item) : Multiset Item) + authority.pruning.pruning.removed) =
          (authority.activation.active : Multiset Item) +
            (authority.pruning.pruning.target : Multiset Item) +
              authority.pruning.pruning.removed := by simp
      _ = (authority.activation.active : Multiset Item) +
            ((authority.pruning.pruning.target : Multiset Item) +
              authority.pruning.pruning.removed) := by ac_rfl
      _ = (authority.activation.active : Multiset Item) +
            (authority.activation.deferred : Multiset Item) := by
              rw [deferredAccounting]
      _ = ((authority.activation.active ++ authority.activation.deferred :
          List Item) : Multiset Item) := by simp
      _ = (authority.activation.source : Multiset Item) :=
        authority.activation.recombinedBag

end DispositionAuthority

/-! ## The downstream product theorem -/

/-- Representation, scheduling, and disposition authorities compose only as
independent coordinates.  The conclusion retains all three guarantees and
does not identify semantic observation, activation lawfulness, or occurrence
accounting. -/
theorem downstream_preservation
    {Candidate : Type uCandidate} {Observation : Type uObservation}
    {family : OptimizationFamily Candidate Observation}
    {dependencies : DependencySystem}
    {preparedRevision currentRevision : dependencies.Revision}
    {candidate : Candidate}
    (representation : RepresentationAuthority family dependencies
      preparedRevision currentRevision candidate)
    {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
    {contract : Contract Item Guard View}
    {TransformationReceipt : Type uReceipt}
    (transformation :
      ControlTransformationAuthority contract TransformationReceipt)
    {step : List Item → Item → List Item}
    {initial batch : List Item}
    (scheduling : SchedulingAuthority contract step initial batch)
    {ActivationReceipt : Type uActivationReceipt}
    {PruningReceipt : Type uReceipt}
    (disposition : DispositionAuthority contract ActivationReceipt
      PruningReceipt)
    {first last : (family.source candidate).operational.theory.Term}
    (path : ExecutionPath (family.source candidate).operational.theory
      first last) :
    representation.plan.target.observe (representation.mapPath path) =
        (family.source candidate).observe path ∧
      contract.observer.observe transformation.change.target =
        contract.observer.observe transformation.change.source ∧
      PlanLawful contract.demand scheduling.branchAuthority
        scheduling.evidence.authority scheduling.plan ∧
      contract.observer.observe disposition.pruning.pruning.source =
        contract.observer.observe disposition.pruning.pruning.target ∧
      (((disposition.activation.active ++ disposition.pruning.pruning.target :
          List Item) : Multiset Item) + disposition.pruning.pruning.removed =
        (disposition.activation.source : Multiset Item)) := by
  refine ⟨representation.observationAgreement path,
    transformation.observation_eq, scheduling.lawful, ?_⟩
  exact disposition.preserves_and_accounts

/-! ## Independence canary -/

namespace Canary

open Mettapedia.GSLT.Core.ObservationControlContract.Canary
open Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission.FusionCanary

/-- A real optimized representation authority exists for the generic fusion
canary. -/
def fusionRepresentation :
    RepresentationAuthority family dependencies revision revision () where
  exactAuthority := ()
  shape := ()
  recognized := rfl
  current := dependencies.sameDependencies_refl revision

/-- The same existence of semantic representation authority does not license
dropping a live `false` occurrence at the raw guarded-bag observer. -/
theorem representation_does_not_authorize_raw_drop :
    Nonempty
        (RepresentationAuthority family dependencies revision revision ()) ∧
      ¬ rawBoolBag.Preserves dropFalse :=
  ⟨⟨fusionRepresentation⟩, dropFalse_not_lawful_at_guardedRawBag⟩

/-- If filtering is explicitly part of the semantic observer, the same
occurrence transformation has genuine pruning authority with an exact
removed-occurrence ledger. -/
def authoredFilterPruning : PruningAuthority trueOnlyBag Unit where
  pruning :=
    { source := [true, false]
      target := [true]
      receipt := ()
      removed := {false}
      accounting := by decide }
  preserves := dropFalse_lawful_at_trueOnlyBag

theorem authored_filter_pruning_accounts :
    (authoredFilterPruning.pruning.source : Multiset Bool) =
      (authoredFilterPruning.pruning.target : Multiset Bool) +
        authoredFilterPruning.pruning.removed :=
  authoredFilterPruning.occurrence_accounting

end Canary

#print axioms RepresentationAuthority.prepare_eq_plan
#print axioms RepresentationAuthority.observationAgreement
#print axioms ControlTransformationAuthority.observation_eq
#print axioms SchedulingAuthority.lawful
#print axioms SchedulingAuthority.bulk_requires_completeBag
#print axioms SchedulingAuthority.bulk_requires_serializable
#print axioms PruningAuthority.observation_eq
#print axioms PruningAuthority.occurrence_accounting
#print axioms DispositionAuthority.preserves_and_accounts
#print axioms downstream_preservation
#print axioms Canary.representation_does_not_authorize_raw_drop
#print axioms Canary.authored_filter_pruning_accounts

end Mettapedia.GSLT.LanguageDef.NIKDownstreamOptimizationAuthority
