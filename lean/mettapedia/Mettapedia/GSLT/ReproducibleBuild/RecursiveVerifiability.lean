import Mettapedia.GSLT.ReproducibleBuild.HattaProfile
import Mettapedia.Enactive.ProtectedFreedom

/-!
# Protected recursive verifiability for reproducible builds

Hatta's sixth AGI-oriented reproducible-build requirement asks an improving
system to preserve reproducibility and independent auditability recursively.
This file proves that target for an explicit class of current,
certificate-family-preserving modifications.  It does not claim preservation
for arbitrary self-modification.

The profile specification below intentionally contains no R1--R5 proofs.
Those proofs form an indexed family.  A modification is accepted only when it
transports every protected certificate fibre and carries a current,
source-scoped execution receipt.  This avoids the vacuous construction in
which a destination already bundles all certificates and “preservation” merely
returns them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability

open Mettapedia.Enactive.ProtectedFreedom
open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.ReproducibleBuild.HattaProfile
open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

universe u uProof

/-! ## Proof-erased specification and indexed obligations -/

/-- All data needed to state Hatta R1--R5, without assuming any requirement is
already satisfied. -/
structure ProfileSpecification
    (Source Artifact State Event EvidenceSource Step : Type u)
    [DecidableEq EvidenceSource] where
  build : RelationalBuild Source Artifact
  declaredInputs : InputView.{u, u} Source
  budget : ReproducibilityBudget.{u, u} Artifact
  toolchain : DependencyAxis.{u, u} Source
  hardware : DependencyAxis.{u, u} Source
  attestation : AttestationDiscipline build
  layout : SupplyChainLayout Step attestation.Issuer
  attestationRevision : attestation.Revision
  eventSystem : EventSystem State Event
  eventOrder : EventOrder.{u, u} Event
  requiredSources : Event -> Finset EvidenceSource
  authoritativeInitial : State
  authoritativeEvents : List Event
  eventLog : EventLog State Event EvidenceSource attestation.Revision

/-- The five protected requirements, represented by six indices because R3
retains its toolchain and hardware sub-obligations separately. -/
inductive Requirement where
  | r1DeclaredInputs
  | r2Reproducibility
  | r3Toolchain
  | r3Hardware
  | r4Attestation
  | r5Trajectory
deriving DecidableEq, Repr

/-- The informative proof fibre for one requirement of an uncertified profile
specification. -/
def CertificateFamily
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (specification : ProfileSpecification Source Artifact State Event
      EvidenceSource Step) : Requirement -> Type
  | .r1DeclaredInputs => PLift (DeclarationSufficient specification.build
      specification.declaredInputs specification.budget.observation)
  | .r2Reproducibility => PLift (Reproducible specification.build
      specification.budget.observation)
  | .r3Toolchain => PLift (DependencyDischarged specification.build
      specification.declaredInputs specification.budget.observation
      specification.toolchain)
  | .r3Hardware => PLift (DependencyDischarged specification.build
      specification.declaredInputs specification.budget.observation
      specification.hardware)
  | .r4Attestation => PLift (LayoutCovered specification.attestation
      specification.layout specification.attestationRevision)
  | .r5Trajectory => PLift (ReplayPremises specification.eventSystem
      specification.eventOrder specification.requiredSources
      specification.authoritativeInitial specification.authoritativeEvents
      specification.eventLog specification.attestationRevision)

/-- A specification is certified exactly when every requirement fibre is
inhabited. -/
def Certified
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (specification : ProfileSpecification Source Artifact State Event
      EvidenceSource Step) : Type :=
  forall requirement, CertificateFamily specification requirement

/-- Forget the bundled proofs of an R1--R5 profile. -/
def ProfileSpecification.ofProfile
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (profile : Profile Source Artifact State Event EvidenceSource Step) :
    ProfileSpecification Source Artifact State Event EvidenceSource Step where
  build := profile.build
  declaredInputs := profile.declaredInputs
  budget := profile.budget
  toolchain := profile.toolchain
  hardware := profile.hardware
  attestation := profile.attestation
  layout := profile.layout
  attestationRevision := profile.attestationRevision
  eventSystem := profile.eventSystem
  eventOrder := profile.eventOrder
  requiredSources := profile.requiredSources
  authoritativeInitial := profile.authoritativeInitial
  authoritativeEvents := profile.authoritativeEvents
  eventLog := profile.eventLog

/-- The bundled R1--R5 fields inhabit the indexed certificate family of the
proof-erased specification. -/
def certificatesOfProfile
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (profile : Profile Source Artifact State Event EvidenceSource Step) :
    Certified (ProfileSpecification.ofProfile profile)
  | .r1DeclaredInputs => ⟨profile.r1⟩
  | .r2Reproducibility => ⟨profile.r2⟩
  | .r3Toolchain => ⟨profile.r3Toolchain⟩
  | .r3Hardware => ⟨profile.r3Hardware⟩
  | .r4Attestation => ⟨profile.r4⟩
  | .r5Trajectory => ⟨profile.r5⟩

/-! ## The admitted modification class -/

/-- A proof-backed modification transports every protected R1--R5 certificate
fibre.  Unlike policy weakening, no order is presumed on profile
specifications. -/
structure FamilyPreservingModification
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (before after : ProfileSpecification Source Artifact State Event
      EvidenceSource Step)
    (Proof : Type uProof) where
  proof : Proof
  preserves : ProtectedFamilyMap (Set.univ : Set Requirement)
    (CertificateFamily before) (CertificateFamily after)

namespace FamilyPreservingModification

variable {Source Artifact State Event EvidenceSource Step : Type u}
  [DecidableEq EvidenceSource]
  {before after : ProfileSpecification Source Artifact State Event
    EvidenceSource Step}
  {Proof : Type uProof}

/-- Certificate transport is the strongest unconditional consequence of the
family map. -/
def transportCertified
    (modification : FamilyPreservingModification before after Proof)
    (certified : Certified before) : Certified after :=
  fun requirement =>
    modification.preserves.map requirement (Set.mem_univ requirement)
      (certified requirement)

end FamilyPreservingModification

/-- A family-preserving modification whose proof has a source-scoped current
execution receipt.  Currentness is evidence in addition to, not a consequence
of, certificate preservation. -/
structure CurrentFamilyPreservingModification
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    (before after : ProfileSpecification Source Artifact State Event
      EvidenceSource Step)
    (Proof : Type uProof) (discipline : ExecutionDiscipline Proof)
    (currentRevision : discipline.Revision) where
  modification : FamilyPreservingModification before after Proof
  receipt : IssuedReceipt discipline modification.proof
  current : receipt.CurrentAt currentRevision

namespace CurrentFamilyPreservingModification

variable {Source Artifact State Event EvidenceSource Step : Type u}
  [DecidableEq EvidenceSource]
  {before after : ProfileSpecification Source Artifact State Event
    EvidenceSource Step}
  {Proof : Type uProof} {discipline : ExecutionDiscipline Proof}
  {currentRevision : discipline.Revision}

/-- The R6 theorem for the characterized architecture class: a current
family-preserving modification transports every R1--R5 certificate and returns
the independent receipt-currentness fact. -/
theorem preserves_recursive_verifiability
    (admitted : CurrentFamilyPreservingModification before after Proof
      discipline currentRevision)
    (certified : Nonempty (Certified before)) :
    Nonempty (Certified after) /\
      admitted.receipt.CurrentAt currentRevision := by
  rcases certified with ⟨certificates⟩
  exact ⟨⟨admitted.modification.transportCertified certificates⟩,
    admitted.current⟩

end CurrentFamilyPreservingModification

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary

abbrev BaseSpecification := ProfileSpecification.ofProfile completeProfile

/-- A genuinely different audit budget: exact artifact identity is replaced by
the input projection, with an explicit acceptance test. -/
def inputBudget : ReproducibilityBudget (Bool × Bool × Bool) where
  observation :=
    (ArtifactObservation.identity (Bool × Bool × Bool)).map Prod.fst
  test := { Accepts := fun left right => left.1 = right.1 }
  sound := fun equality => equality

def coarseSpecification :
    ProfileSpecification Environment (Bool × Bool × Bool) Nat
      TrajectoryReplay.Canary.Update Unit Unit :=
  { ProfileSpecification.ofProfile completeProfile with budget := inputBudget }

inductive CoarseningProof where
  | exactArtifactToInputObservation

/-- Exact R3 discharge transports to a coarser observation.  Declared
dependencies are unchanged; an abstraction proof is mapped by forgetting the
same artifact distinction. -/
def mapDependencyDischarge
    {axis : DependencyAxis Environment}
    (discharged : DependencyDischarged environmentBuild fullEnvironmentView
      (ArtifactObservation.identity (Bool × Bool × Bool)) axis) :
    DependencyDischarged environmentBuild fullEnvironmentView
      inputBudget.observation axis := by
  cases discharged with
  | declared bound => exact .declared bound
  | abstracted independent =>
      apply DependencyDischarged.abstracted
      intro leftSource rightSource leftArtifact rightArtifact sameOtherwise
        leftBuild rightBuild
      exact congrArg Prod.fst
        (independent sameOtherwise leftBuild rightBuild)

/-- Non-identity positive modification: every exact-observation certificate is
transported to the explicitly coarser input observation. -/
def coarseningModification :
    FamilyPreservingModification BaseSpecification coarseSpecification
      CoarseningProof where
  proof := .exactArtifactToInputObservation
  preserves :=
    { map := by
        intro requirement _protected certificate
        cases requirement with
        | r1DeclaredInputs =>
            exact ⟨certificate.down.mapObservation Prod.fst⟩
        | r2Reproducibility =>
            exact ⟨certificate.down.mapObservation Prod.fst⟩
        | r3Toolchain =>
            exact ⟨mapDependencyDischarge certificate.down⟩
        | r3Hardware =>
            exact ⟨mapDependencyDischarge certificate.down⟩
        | r4Attestation => exact certificate
        | r5Trajectory => exact certificate }

def coarseningDiscipline : ExecutionDiscipline CoarseningProof where
  Source := Fin 2
  Revision := Nat
  Authority := Unit
  sourceDecidable := inferInstance
  Authorized := fun proof _ =>
    match proof with
    | .exactArtifactToInputObservation => Unit
  Realizable := fun proof =>
    match proof with
    | .exactArtifactToInputObservation => Unit

def coarseningReceipt :
    IssuedReceipt coarseningDiscipline
      CoarseningProof.exactArtifactToInputObservation where
  authority := ()
  sources := by
    change Finset (Fin 2)
    exact {0}
  issuedAt := by
    change Nat
    exact 7
  authorized := ()
  realizable := ()

def currentCoarsening :
    CurrentFamilyPreservingModification BaseSpecification coarseSpecification
      CoarseningProof coarseningDiscipline (by change Nat; exact 7) where
  modification := coarseningModification
  receipt := coarseningReceipt
  current := rfl

/-- Positive R6 control: the non-identity observation coarsening retains all
R1--R5 certificates and a current source-scoped receipt. -/
theorem currentCoarsening_preserves_recursive_verifiability :
    Nonempty (Certified coarseSpecification) /\
      coarseningReceipt.CurrentAt (by change Nat; exact 7) :=
  currentCoarsening.preserves_recursive_verifiability
    ⟨certificatesOfProfile completeProfile⟩

/-! ### Output behavior alone is insufficient -/

/-- This candidate changes only the declared input view.  The actual build and
artifact observation are untouched. -/
def incompleteDeclarationSpecification :
    ProfileSpecification Environment (Bool × Bool × Bool) Nat
      TrajectoryReplay.Canary.Update Unit Unit :=
  { ProfileSpecification.ofProfile completeProfile with
      declaredInputs := inputOnlyView }

/-- The before and after candidates have exactly the same relational build and
artifact observation. -/
theorem incompleteDeclaration_preserves_output_behavior :
    incompleteDeclarationSpecification.build = BaseSpecification.build /\
      incompleteDeclarationSpecification.budget.observation.observe =
        BaseSpecification.budget.observation.observe :=
  ⟨rfl, rfl⟩

/-- The narrower declaration erases a hardware distinction used by the exact
artifact observation. -/
theorem inputOnlyView_not_declarationSufficient :
    Not (DeclarationSufficient environmentBuild inputOnlyView
      (ArtifactObservation.identity (Bool × Bool × Bool))) := by
  intro sufficient
  let leftSource : Environment := ⟨false, false, false⟩
  let rightSource : Environment := ⟨false, false, true⟩
  let left : Occurrence environmentBuild :=
    ⟨leftSource, (false, false, false), ⟨rfl⟩⟩
  let right : Occurrence environmentBuild :=
    ⟨rightSource, (false, false, true), ⟨rfl⟩⟩
  have sameDeclaration :
      declaredOccurrence environmentBuild inputOnlyView left =
        declaredOccurrence environmentBuild inputOnlyView right := rfl
  have equal := sufficient sameDeclaration
  have hardwareEqual :=
    congrArg (fun artifact : Bool × Bool × Bool => artifact.2.2) equal
  change false = true at hardwareEqual
  cases hardwareEqual

theorem incompleteDeclaration_not_certified :
    Not (Nonempty (Certified incompleteDeclarationSpecification)) := by
  rintro ⟨certified⟩
  exact inputOnlyView_not_declarationSufficient
    (certified .r1DeclaredInputs).down

/-- Therefore no protected-family map can certify the behavior-preserving but
declaration-destroying candidate. -/
theorem no_familyPreservingModification_to_incompleteDeclaration
    (Proof : Type uProof) :
    Not (Nonempty (FamilyPreservingModification BaseSpecification
      incompleteDeclarationSpecification Proof)) := by
  rintro ⟨modification⟩
  exact incompleteDeclaration_not_certified
    ⟨modification.transportCertified (certificatesOfProfile completeProfile)⟩

/-! ### Receipt currency is not semantic preservation -/

def staleCoarseningReceipt :
    IssuedReceipt coarseningDiscipline
      CoarseningProof.exactArtifactToInputObservation :=
  { coarseningReceipt with issuedAt := by change Nat; exact 6 }

theorem stale_receipt_cannot_establish_recursive_verifiability :
    Not (staleCoarseningReceipt.CurrentAt (by change Nat; exact 7)) := by
  change (6 : Nat) ≠ 7
  decide

end Canary

end Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability

#print axioms Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.CurrentFamilyPreservingModification.preserves_recursive_verifiability
#print axioms Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.Canary.currentCoarsening_preserves_recursive_verifiability
#print axioms Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.Canary.no_familyPreservingModification_to_incompleteDeclaration
#print axioms Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.Canary.stale_receipt_cannot_establish_recursive_verifiability
