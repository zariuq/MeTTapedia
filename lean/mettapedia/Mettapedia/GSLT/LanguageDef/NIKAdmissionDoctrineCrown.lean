import Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
import Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation
import Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
import Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority

/-!
# The revision-fibred NIK admission doctrine

NIK admission is the retention of a semantic refinement cell, not a checker
call, an object-logic theorem, or a profitability verdict.  This module gives
the existing indexed-execution construction its intentional algebraic crown:

* proof-relevant indexed refinements form a category;
* observation-preserving refinements form a category over it;
* admissions retained at one dependency revision form a category fibre;
* equality of selected dependency views reindexes those fibres;
* common-current composition is ordinary composition after reindexing;
* the endpoint-only admission shadow is intentionally non-faithful;
* exact represented routes nevertheless determine their direct map uniquely;
* missing or stale optimization authority leaves raw execution available;
* rejection is not refutation, and execution admission does not determine a
  guest's hypothetical consequence relation;
* profitability is additional evidence about an already adequate plan.

Thus the doctrine is fibred over dependency worlds and displayed over the
proof-relevant execution equipment.  Runtime tokens and certificate formats
may realize this structure, but they are not its definition.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKAdmissionDoctrineCrown

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKOptimizationAdmission
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe u uValue

/-! ## The semantic and observed categories -/

/-- Proof-relevant semantic refinements compose as a category.  The
composition law simultaneously composes endpoint maps, execution witnesses,
and preservation of the selected semantic fibre. -/
instance : Quiver IndexedOperationalObject where
  Hom := IndexedRefinement

instance : CategoryTheory.Category IndexedOperationalObject where
  id object := IndexedRefinement.id object
  comp earlier later := IndexedRefinement.comp earlier later
  id_comp refinement := by cases refinement; rfl
  comp_id refinement := by cases refinement; rfl
  assoc earlier middle later := by
    cases earlier
    cases middle
    cases later
    rfl

/-- Observation-preserving refinement squares form a category over semantic
indexed refinements. -/
instance (Value : Type uValue) :
    Quiver (IndexedObservedOperationalObject.{u, uValue} Value) where
  Hom := IndexedObservedRefinement

instance (Value : Type uValue) :
    CategoryTheory.Category
      (IndexedObservedOperationalObject.{u, uValue} Value) where
  id object := IndexedObservedRefinement.id object
  comp earlier later := IndexedObservedRefinement.comp earlier later
  id_comp refinement := by cases refinement; rfl
  comp_id refinement := by cases refinement; rfl
  assoc earlier middle later := by
    cases earlier
    cases middle
    cases later
    rfl

/-- Forget the declared observation square while retaining the complete
proof-relevant semantic execution cell. -/
def forgetObservation (Value : Type uValue) :
    CategoryTheory.Functor
      (IndexedObservedOperationalObject.{u, uValue} Value)
      IndexedOperationalObject.{u} where
  obj object := object.operational
  map refinement := refinement.refinement
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget execution witnesses only after selecting their semantic refinement.
This is the common admission category already used throughout NIK. -/
def toAdmission :
    CategoryTheory.Functor IndexedOperationalObject.{u}
      AdmissionObject.{u} where
  obj object := object.toAdmissionObject
  map refinement := refinement.toAdmissionHom
  map_id object := by
    apply AdmissionHom.ext
    rfl
  map_comp earlier later :=
    IndexedRefinement.toAdmissionHom_comp earlier later

@[simp] theorem forgetObservation_map
    {Value : Type uValue}
    {source target : IndexedObservedOperationalObject.{u, uValue} Value}
    (refinement : source ⟶ target) :
    (forgetObservation Value).map refinement = refinement.refinement :=
  rfl

@[simp] theorem toAdmission_map_run
    {source target : IndexedOperationalObject.{u}}
    (refinement : source ⟶ target) (state : source.State) :
    ((toAdmission).map refinement).run state = refinement.mapState state :=
  rfl

/-! ## Revision fibres and dependency reindexing -/

/-- The category of complete observed admission cells retained at one exact
dependency revision. -/
structure RevisionFibre (Value : Type uValue)
    (dependencies : DependencySystem)
    (revision : dependencies.Revision) where
  object : IndexedObservedOperationalObject.{u, uValue} Value

namespace RevisionFibre

instance {Value : Type uValue} {dependencies : DependencySystem}
    {revision : dependencies.Revision} :
    Quiver (RevisionFibre.{u, uValue} Value dependencies revision) where
  Hom source target :=
    IndexedObservedAdmittedAt dependencies revision source.object target.object

instance {Value : Type uValue} {dependencies : DependencySystem}
    {revision : dependencies.Revision} :
    CategoryTheory.Category
      (RevisionFibre.{u, uValue} Value dependencies revision) where
  id object := IndexedObservedAdmittedAt.id dependencies revision object.object
  comp earlier later := IndexedObservedAdmittedAt.comp earlier later
  id_comp admission := by cases admission; rfl
  comp_id admission := by cases admission; rfl
  assoc earlier middle later := by
    cases earlier
    cases middle
    cases later
    rfl

/-- Forget the revision index while retaining the complete observed semantic
cell. -/
def forget {Value : Type uValue} (dependencies : DependencySystem)
    (revision : dependencies.Revision) :
    CategoryTheory.Functor
      (RevisionFibre.{u, uValue} Value dependencies revision)
      (IndexedObservedOperationalObject.{u, uValue} Value) where
  obj object := object.object
  map admission := admission.refinement
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Extensionally unchanged selected dependencies transport a complete
admission cell to the corresponding revision fibre.  No semantic or
observation proof is regenerated. -/
def reindex {Value : Type uValue} {dependencies : DependencySystem}
    {earlier later : dependencies.Revision}
    (_same : dependencies.SameDependencies earlier later) :
    CategoryTheory.Functor
      (RevisionFibre.{u, uValue} Value dependencies earlier)
      (RevisionFibre.{u, uValue} Value dependencies later) where
  obj object := ⟨object.object⟩
  map admission := ⟨admission.refinement⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem reindex_object {Value : Type uValue}
    {dependencies : DependencySystem}
    {earlier later : dependencies.Revision}
    (same : dependencies.SameDependencies earlier later)
    (object : RevisionFibre.{u, uValue} Value dependencies earlier) :
    ((reindex same).obj object).object = object.object :=
  rfl

@[simp] theorem reindex_refinement {Value : Type uValue}
    {dependencies : DependencySystem}
    {earlier later : dependencies.Revision}
    (same : dependencies.SameDependencies earlier later)
    {source target : RevisionFibre.{u, uValue} Value dependencies earlier}
    (admission : source ⟶ target) :
    ((reindex same).map admission).refinement = admission.refinement :=
  rfl

/-- Dependency reindexing is strictly coherent on retained admission cells.
The equality proof selecting the new fibre does not alter the cell. -/
theorem reindex_trans_refinement {Value : Type uValue}
    {dependencies : DependencySystem}
    {first second third : dependencies.Revision}
    (firstSecond : dependencies.SameDependencies first second)
    (secondThird : dependencies.SameDependencies second third)
    {source target : RevisionFibre.{u, uValue} Value dependencies first}
    (admission : source ⟶ target) :
    ((reindex secondThird).map ((reindex firstSecond).map admission)).refinement =
      ((reindex (dependencies.sameDependencies_trans
        firstSecond secondThird)).map admission).refinement :=
  rfl

/-- Common-current composition is exactly categorical composition after both
stored cells have been reindexed into their shared current fibre. -/
theorem commonCurrent_comp_is_reindexed_comp
    {Value : Type uValue} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedAdmittedAt dependencies earlierRevision
      first middle)
    (later : IndexedObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision) :
    IndexedObservedAdmittedAt.comp
        ((reindex alignment.earlierCurrent).map earlier)
        ((reindex alignment.laterCurrent).map later) =
      IndexedObservedAdmittedAt.compAtCommonCurrent earlier later alignment :=
  rfl

end RevisionFibre

/-! ## Direct active execution is inherited from the retained cell -/

/-- Activating a common-current composite performs ordinary direct function
composition.  Neither a checker nor either currentness proof appears in the
execution function. -/
theorem activeComposite_run_is_composition
    {Value : Type uValue} {dependencies : DependencySystem}
    {earlierRevision laterRevision currentRevision : dependencies.Revision}
    {first middle last : IndexedObservedOperationalObject.{u, uValue} Value}
    (earlier : IndexedObservedAdmittedAt dependencies earlierRevision
      first middle)
    (later : IndexedObservedAdmittedAt dependencies laterRevision middle last)
    (alignment : CommonCurrent dependencies earlierRevision laterRevision
      currentRevision)
    (state : first.operational.State) :
    (IndexedObservedAdmittedAt.activateComposite earlier later alignment).run
        state =
      later.refinement.refinement.mapState
        (earlier.refinement.refinement.mapState state) :=
  rfl

/-! ## The endpoint shadow is deliberately non-faithful -/

namespace ProofRelevanceCanary

/-- One state with two proof-relevant execution witnesses. -/
def proofObject : IndexedOperationalObject where
  State := Unit
  Execution := fun _ _ => Bool
  Meaning := fun _ => True

/-- Retain the execution witness unchanged. -/
def keepProof : IndexedRefinement proofObject proofObject where
  mapState := _root_.id
  mapExecution := _root_.id
  preservesMeaning := fun _ meaningful => meaningful

/-- Flip the retained execution witness while leaving endpoints and meaning
unchanged. -/
def flipProof : IndexedRefinement proofObject proofObject where
  mapState := _root_.id
  mapExecution := Bool.not
  preservesMeaning := fun _ meaningful => meaningful

theorem keepProof_ne_flipProof : keepProof ≠ flipProof := by
  intro equal
  have mapped := congrArg
    (fun refinement : IndexedRefinement proofObject proofObject =>
      refinement.mapExecution (first := ()) (last := ()) true) equal
  simp [keepProof, flipProof] at mapped

/-- Endpoint-only semantic admission forgets the execution-witness action. -/
theorem endpoint_shadows_equal :
    keepProof.toAdmissionHom = flipProof.toAdmissionHom := by
  apply AdmissionHom.ext
  rfl

/-- The forgetful functor to endpoint admission is therefore not faithful in
general.  Exact execution evidence must remain in the indexed cell. -/
theorem toAdmission_is_not_faithful :
    ∃ (first second : proofObject ⟶ proofObject),
      first ≠ second ∧
        (toAdmission).map first = (toAdmission).map second :=
  ⟨keepProof, flipProof, keepProof_ne_flipProof, endpoint_shadows_equal⟩

end ProofRelevanceCanary

/-! ## Currentness is a gate on admitted realization, not raw execution -/

namespace CurrentnessCanary

def observedProofObject : IndexedObservedOperationalObject Bool where
  operational := ProofRelevanceCanary.proofObject
  observe := fun execution => some execution

def keepObserved :
    IndexedObservedRefinement observedProofObject observedProofObject where
  refinement := ProofRelevanceCanary.keepProof
  commutes := fun _ => rfl

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

def admitted : IndexedObservedAdmittedAt dependencies false
    observedProofObject observedProofObject where
  refinement := keepObserved

def active : admitted.Active false :=
  admitted.activate (dependencies.sameDependencies_refl false)

theorem active_retains_execution_witness :
    active.mapExecution (first := ()) (last := ()) true = true :=
  rfl

theorem active_observation_agrees :
    observedProofObject.observe
        (active.mapExecution (first := ()) (last := ()) true) =
      observedProofObject.observe (first := ()) (last := ()) true :=
  active.observationAgreement true

theorem relevant_change_prevents_activation :
    ¬ admitted.Active true := by
  rintro ⟨current⟩
  have impossible := current ()
  simp [dependencies] at impossible

/-- The same raw proof-relevant execution remains available when the stored
realization is stale.  Failure to activate is not semantic refutation. -/
theorem raw_execution_survives_stale_admission :
    Nonempty (observedProofObject.operational.Execution () ()) ∧
      ¬ admitted.Active true :=
  ⟨⟨true⟩, relevant_change_prevents_activation⟩

end CurrentnessCanary

/-! ## The surrounding non-collapse laws -/

/-- If exact authority is absent, optimization preparation selects the raw
identity realization at every current revision. -/
theorem missing_optimization_authority_preserves_raw
    {Candidate : Type} {Observation : Type}
    (family : OptimizationFamily Candidate Observation)
    (dependencies : DependencySystem)
    (revision current : dependencies.Revision)
    (candidate : Candidate)
    (state : (family.source candidate).operational.theory.Term) :
    ∃ currentEvidence :
        (prepare family dependencies revision candidate none).Current current,
      (prepare family dependencies revision candidate none).runAt
        current currentEvidence state = state :=
  ⟨True.intro, rfl⟩

/-- Exact representation proofs may differ, but cannot authorize different
direct executions for the same proof-relevant route. -/
theorem exact_route_authority_is_execution_rigid
    {Source Target : Type u} {relation : Loose Source Target}
    (first second : Representation relation) :
    first.map = second.map :=
  Representation.map_unique first second

#print axioms IndexedRefinement.toCell_comp
#print axioms RevisionFibre.commonCurrent_comp_is_reindexed_comp
#print axioms activeComposite_run_is_composition
#print axioms ProofRelevanceCanary.toAdmission_is_not_faithful
#print axioms CurrentnessCanary.raw_execution_survives_stale_admission
#print axioms missing_optimization_authority_preserves_raw
#print axioms exact_route_authority_is_execution_rigid
#print axioms NIKPolarizedAuthority.Canary.rejection_is_not_refutation
#print axioms SeparationSentence.rawNIK_does_not_determine_consequence
#print axioms FusionCanary.no_unit_surcharge_profitability

end Mettapedia.GSLT.LanguageDef.NIKAdmissionDoctrineCrown
