import Mettapedia.GSLT.Core.GivenClauseLoop
import Mettapedia.GSLT.LanguageDef.NIKDownstreamOptimizationAuthority
import Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationInstances

/-!
# Prime instances of downstream optimization authority

This module exercises the generic downstream authority boundary in two
different regimes.

* Metamath record fusion, nonescaping storage reuse, and revision-stable memo
  reuse inhabit revision-current NIK representation authority through their
  existing typed shape recognizers.
* A genuine given-clause loop supplies scheduling and pruning controls.  Two
  root orders produce different event streams but the same complete event
  bag.  Duplicate event pruning is admitted only by an extensional set
  observer and is refused by the multiplicity-sensitive bag observer.

The examples deliberately do not identify these authorities.  A recognized
representation does not thereby authorize scheduling or pruning, and a
coarse GCL observer does not change the source logic or construct an exact
native judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeOptimizationAuthorityInstances

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.LanguageDef.NIKDownstreamOptimizationAuthority
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeTypedOptimizationNIKBridge

/-! ## Existing typed shape optimizations inhabit representation authority -/

namespace TypedRepresentation

open NativeTypedOptimizationInstances

abbrev MetamathSource :=
  Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation.SourceProgram
    String
    (Option Mettapedia.Languages.Metamath.SourceGSLTOperations.NodeBinding)

abbrev StorageSource :=
  NonEscapingStorage.Source (width := 1) (Value := Nat) (Observation := Nat)

abbrev MemoSource :=
  RevisionStableMemo.Source (Row := Nat) (Key := Nat) (Value := Nat)

/-- Source-derived Metamath record fusion enters the generic representation
authority with its complete optimization key as revision. -/
def metamath :
    RepresentationAuthority
      (nikFamily MetamathOperationRecordFusion.spec)
      (keyDependencies MetamathSource)
      MetamathOperationRecordFusion.nativeKey
      MetamathOperationRecordFusion.nativeKey
      MetamathOperationRecordFusion.candidate where
  exactAuthority := MetamathOperationRecordFusion.authority
  shape := MetamathOperationRecordFusion.evidence
  recognized := MetamathOperationRecordFusion.recognized
  current := (keyDependencies MetamathSource).sameDependencies_refl
    MetamathOperationRecordFusion.nativeKey

/-- The generic family prepares exactly the Metamath representation retained
by the authority. -/
theorem metamath_prepares_exact_representation :
    prepareAtKey MetamathOperationRecordFusion.spec
        MetamathOperationRecordFusion.candidate
        (some MetamathOperationRecordFusion.authority) = metamath.plan :=
  metamath.prepare_eq_plan

def metamathInput :
    ExactOccurrence MetamathOperationRecordFusion.candidate :=
  ⟨MetamathOperationRecordFusion.source, rfl⟩

def metamathPath :
    ExecutionPath
      (sourceTheory MetamathOperationRecordFusion.candidate)
      metamathInput metamathInput :=
  .refl metamathInput

/-- The representation-authority theorem transports the real Metamath
source occurrence through its compiled artifact while preserving the named
source-derived observation. -/
theorem metamath_observation_agrees :
    metamath.plan.target.observe (metamath.mapPath metamathPath) =
      ((nikFamily MetamathOperationRecordFusion.spec).source
        MetamathOperationRecordFusion.candidate).observe metamathPath :=
  metamath.observationAgreement metamathPath

/-- Call-local value storage reuse enters the same generic representation
authority without sharing Metamath's authority key or shape witness. -/
def storage :
    RepresentationAuthority
      (nikFamily StorageReuse.spec)
      (keyDependencies StorageSource)
      StorageReuse.nativeKey StorageReuse.nativeKey
      StorageReuse.candidate where
  exactAuthority := StorageReuse.authority
  shape := StorageReuse.evidence
  recognized := StorageReuse.recognized
  current := (keyDependencies StorageSource).sameDependencies_refl
    StorageReuse.nativeKey

/-- Revision-stable memo reuse is a third, structurally different inhabitant
of the same representation boundary. -/
def memo :
    RepresentationAuthority
      (nikFamily StableMemo.spec)
      (keyDependencies MemoSource)
      StableMemo.nativeKey StableMemo.nativeKey
      StableMemo.candidate where
  exactAuthority := StableMemo.authority
  shape := StableMemo.evidence
  recognized := StableMemo.recognized
  current := (keyDependencies MemoSource).sameDependencies_refl
    StableMemo.nativeKey

/-- The three existing optimization families all inhabit one downstream
representation interface while retaining distinct source-indexed evidence. -/
theorem three_typed_shape_authorities_exist :
    Nonempty
        (RepresentationAuthority
          (nikFamily MetamathOperationRecordFusion.spec)
          (keyDependencies MetamathSource)
          MetamathOperationRecordFusion.nativeKey
          MetamathOperationRecordFusion.nativeKey
          MetamathOperationRecordFusion.candidate) ∧
      Nonempty
        (RepresentationAuthority
          (nikFamily StorageReuse.spec)
          (keyDependencies StorageSource)
          StorageReuse.nativeKey StorageReuse.nativeKey
          StorageReuse.candidate) ∧
      Nonempty
        (RepresentationAuthority
          (nikFamily StableMemo.spec)
          (keyDependencies MemoSource)
          StableMemo.nativeKey StableMemo.nativeKey
          StableMemo.candidate) :=
  ⟨⟨metamath⟩, ⟨storage⟩, ⟨memo⟩⟩

/-- A retained reference has a genuine native storage judgment but no shape
witness, so it cannot inhabit representation authority. -/
theorem retained_reference_has_no_representation_authority :
    ¬ Nonempty
      (RepresentationAuthority
        (nikFamily StorageReuse.spec)
        (keyDependencies StorageSource)
        StorageReuse.retainedNativeKey StorageReuse.retainedNativeKey
        StorageReuse.retainedCandidate) := by
  rintro ⟨authority⟩
  have recognized := authority.recognized
  change
    NonEscapingStorage.recognize StorageReuse.retainedSource =
      some authority.shape at recognized
  rw [NativeTypedOptimizationAdmission.Examples.Storage.retained_reference_rejected]
    at recognized
  cases recognized

end TypedRepresentation

/-! ## Actual given-clause scheduling and pruning controls -/

namespace GivenClause

abbrev Event := Emission Nat Nat

/-- A small genuine GCL: every selected occurrence emits its own value and
generates no additional passive work. -/
def emittingSystem : System Nat Nat where
  observe node _processed := some node
  generate _node _processed := []

def forwardInitial : Snapshot Nat Nat 1 :=
  Snapshot.initial Snapshot.breadthOnly [1, 2] 0

def reverseInitial : Snapshot Nat Nat 1 :=
  Snapshot.initial Snapshot.breadthOnly [2, 1] 0

def duplicateInitial : Snapshot Nat Nat 1 :=
  Snapshot.initial Snapshot.breadthOnly [1, 1] 0

def forwardRun : Snapshot Nat Nat 1 :=
  Snapshot.run emittingSystem Snapshot.breadthOnly 2 forwardInitial

def reverseRun : Snapshot Nat Nat 1 :=
  Snapshot.run emittingSystem Snapshot.breadthOnly 2 reverseInitial

def duplicateRun : Snapshot Nat Nat 1 :=
  Snapshot.run emittingSystem Snapshot.breadthOnly 2 duplicateInitial

theorem forward_events :
    forwardRun.events = [⟨1, 1⟩, ⟨2, 2⟩] := by
  decide

theorem reverse_events :
    reverseRun.events = [⟨2, 2⟩, ⟨1, 1⟩] := by
  decide

theorem duplicate_events :
    duplicateRun.events = [⟨1, 1⟩, ⟨1, 1⟩] := by
  decide

def eventBagObserver : Observer (List Event) (Multiset Event) where
  observe := fun events => (events : Multiset Event)

def eventStreamObserver : Observer (List Event) (List Event) :=
  Observer.identity (List Event)

def eventSetObserver : Observer (List Event) (Finset Event) where
  observe := List.toFinset

def completeEventBag : Contract Event Unit (Multiset Event) where
  observer := eventBagObserver
  demand := { completion := .completeBag }

def orderedEventStream : Contract Event Unit (List Event) where
  observer := eventStreamObserver
  demand := { completion := .orderedStream }

def completeEventSet : Contract Event Unit (Finset Event) where
  observer := eventSetObserver
  demand := { completion := .completeBag }

/-- Reordering the passive roots changes the exact GCL event stream. -/
def reorderEvents : Change Event Unit where
  source := forwardRun.events
  target := reverseRun.events
  receipt := ()

theorem reorder_lawful_at_complete_event_bag :
    completeEventBag.Preserves reorderEvents := by
  change (forwardRun.events : Multiset Event) =
    (reverseRun.events : Multiset Event)
  rw [forward_events, reverse_events]
  decide

theorem reorder_not_lawful_at_ordered_event_stream :
    ¬ orderedEventStream.Preserves reorderEvents := by
  change ¬ (forwardRun.events = reverseRun.events)
  rw [forward_events, reverse_events]
  decide

/-- The real GCL reordering is therefore an admitted optimization only for
the complete-bag client. -/
def bagReorderAuthority :
    ControlTransformationAuthority completeEventBag Unit where
  change := reorderEvents
  preserves := reorder_lawful_at_complete_event_bag

/-- The same GCL roots may be activated as a bulk append only under complete
bag demand and a real permutation-invariance proof. -/
def nodeBagContract : Contract Nat Unit (Multiset Nat) where
  observer := { observe := fun nodes => (nodes : Multiset Nat) }
  demand := { completion := .completeBag }

def appendNode (state : List Nat) (node : Nat) : List Nat :=
  state ++ [node]

def nodeBatchAuthority :
    SchedulingAuthority nodeBagContract appendNode [] [1, 2] where
  branchAuthority := .general
  evidence := .serializable (append_is_serializable_for_bag [] [1, 2])

theorem node_batch_dispatches_bulk :
    nodeBatchAuthority.plan.activation = .bulk :=
  nodeBagContract.completeBag_serializable_dispatches_bulk rfl
    (append_is_serializable_for_bag [] [1, 2])

/-- One of two equal GCL emissions may be collapsed only at an observer which
has explicitly forgotten multiplicity. -/
def duplicatePruning : PruningChange Event Unit where
  source := duplicateRun.events
  target := [⟨1, 1⟩]
  receipt := ()
  removed := {⟨1, 1⟩}
  accounting := by
    rw [duplicate_events]
    decide

theorem duplicate_pruning_lawful_at_event_set :
    completeEventSet.Preserves duplicatePruning.toChange := by
  change duplicateRun.events.toFinset = ([⟨1, 1⟩] : List Event).toFinset
  rw [duplicate_events]
  simp

theorem duplicate_pruning_not_lawful_at_event_bag :
    ¬ completeEventBag.Preserves duplicatePruning.toChange := by
  change ¬ ((duplicateRun.events : Multiset Event) =
    (([⟨1, 1⟩] : List Event) : Multiset Event))
  rw [duplicate_events]
  decide

def setPruningAuthority : PruningAuthority completeEventSet Unit where
  pruning := duplicatePruning
  preserves := duplicate_pruning_lawful_at_event_set

/-- Before the permanent prune, both duplicate occurrences remain deferred. -/
def duplicateDeferred : ActivationPartition Event Unit where
  source := duplicateRun.events
  active := []
  deferred := duplicateRun.events
  receipt := ()
  complete := by simp

def duplicateDisposition :
    DispositionAuthority completeEventSet Unit Unit where
  activation := duplicateDeferred
  pruning := setPruningAuthority
  prunesDeferred := rfl

/-- The admitted set-level prune still accounts for both original GCL event
occurrences: one retained, one explicitly removed. -/
theorem duplicate_disposition_preserves_and_accounts :
    completeEventSet.observer.observe
          duplicateDisposition.pruning.pruning.source =
        completeEventSet.observer.observe
          duplicateDisposition.pruning.pruning.target ∧
      (((duplicateDisposition.activation.active ++
          duplicateDisposition.pruning.pruning.target : List Event) :
          Multiset Event) + duplicateDisposition.pruning.pruning.removed =
        (duplicateDisposition.activation.source : Multiset Event)) :=
  duplicateDisposition.preserves_and_accounts

end GivenClause

#print axioms TypedRepresentation.metamath_prepares_exact_representation
#print axioms TypedRepresentation.metamath_observation_agrees
#print axioms TypedRepresentation.three_typed_shape_authorities_exist
#print axioms TypedRepresentation.retained_reference_has_no_representation_authority
#print axioms GivenClause.forward_events
#print axioms GivenClause.reorder_lawful_at_complete_event_bag
#print axioms GivenClause.reorder_not_lawful_at_ordered_event_stream
#print axioms GivenClause.node_batch_dispatches_bulk
#print axioms GivenClause.duplicate_pruning_lawful_at_event_set
#print axioms GivenClause.duplicate_pruning_not_lawful_at_event_bag
#print axioms GivenClause.duplicate_disposition_preserves_and_accounts

end Mettapedia.Languages.MeTTa.Prime.NativeOptimizationAuthorityInstances
