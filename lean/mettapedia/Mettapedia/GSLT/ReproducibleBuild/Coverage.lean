import Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability
import Mettapedia.GSLT.ReproducibleBuild.Feasibility

/-!
# Theorem-level coverage of Hatta's R1--R7

This module is an executable index into the formal obligations corresponding
to Masayuki Hatta's seven requirements for AGI-oriented reproducible builds.
Each row contains an actual formal object, a proved positive claim, and a
proved negative control.  The scope field records the premise boundary that
must remain visible when the row is cited.

The source requirements are Hatta's *Reproducibility Is the New Copyleft:
Defining AGI-Oriented Reproducible Builds* (2026), Sections 7.1--7.7.  The
factorization, replay-equivalence, protected-family, and resource-separation
theorems are MeTTapedia extensions.  In particular, Hatta's R5 motivates full
trajectory retention; the replay equivalence used here additionally requires
the explicit premises in `TrajectoryReplay.ReplayPremises`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.Coverage

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.ReproducibleBuild.HattaProfile
open Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability
open Mettapedia.GSLT.ReproducibleBuild.Feasibility

universe u

/-- The seven requirements, kept distinct from the six proof fibres used to
represent R1--R5 internally (R3 has separate toolchain and hardware fibres). -/
inductive HattaRequirement where
  | r1CompleteInputs
  | r2ReproducibleExecution
  | r3BoundEnvironment
  | r4ThirdPartyAttestation
  | r5CompleteTrajectory
  | r6RecursiveVerifiability
  | r7FeasibleVerification
deriving DecidableEq, Repr

/-- Exact attribution boundary for each formal row. -/
inductive Attribution where
  | hatta2026R1
  | hatta2026R2
  | hatta2026R3
  | hatta2026R4WithInTotoDiscipline
  | hatta2026R5WithReplayExtension
  | hatta2026R6ForProtectedCurrentModifications
  | hatta2026R7WithWorkSpanExtension
deriving DecidableEq, Repr

/-- Premise boundary that must accompany a theorem-level coverage claim. -/
inductive Scope where
  | declaredViewAtSelectedObservation
  | fullSourceAtSelectedBudget
  | dependencyDeclaredOrObservationallyAbstracted
  | authorizedAuthenticatedAndCurrentLinks
  | initialSourceTransitionOrderAndCurrentnessPremises
  | currentFamilyPreservingModificationOnly
  | declaredCoverageAndResourceEnvelope
deriving DecidableEq, Repr

/-- One non-vacuous coverage row. `Positive` and `Negative` are data supplied
by the imported theorem tranche, not checklist booleans. -/
structure Row (requirement : HattaRequirement) where
  FormalObject : Type u
  formalObject : FormalObject
  Positive : Prop
  positive : Positive
  Negative : Prop
  negative : Negative
  attribution : Attribution
  scope : Scope

namespace Canary

open Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary
open Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.Canary
open Mettapedia.GSLT.ReproducibleBuild.Feasibility.Canary

/-- R1: declaration sufficiency is inhabited by the complete environment view;
the input-only view demonstrably omits an observed hardware distinction. -/
def r1Coverage : Row.{1} .r1CompleteInputs where
  FormalObject := InputView Environment
  formalObject := fullEnvironmentView
  Positive := DeclarationSufficient environmentBuild fullEnvironmentView
    (ArtifactObservation.identity (Bool × Bool × Bool))
  positive := completeProfile.r1
  Negative := Not (DeclarationSufficient environmentBuild inputOnlyView
    (ArtifactObservation.identity (Bool × Bool × Bool)))
  negative := inputOnlyView_not_declarationSufficient
  attribution := .hatta2026R1
  scope := .declaredViewAtSelectedObservation

/-- R2: an exact identity build supplies universal reproducibility, while the
branching build is rebuildable but not reproducible at exact observation. -/
def r2Coverage : Row.{1} .r2ReproducibleExecution where
  FormalObject := RelationalBuild Bool Bool
  formalObject := identityBuild
  Positive := Reproducible identityBuild (ArtifactObservation.identity Bool)
  positive := identityBuild_reproducible
  Negative := Not (Reproducible branchingBuild
    HattaProfile.Canary.exactBool)
  negative := branchingBuild_not_reproducible
  attribution := .hatta2026R2
  scope := .fullSourceAtSelectedBudget

/-- R3: the complete view declares both toolchain and hardware axes.  The
input-only view neither binds hardware nor abstracts it at exact observation. -/
def r3Coverage : Row.{1} .r3BoundEnvironment where
  FormalObject := DependencyAxis Environment × DependencyAxis Environment
  formalObject := (toolchainAxis, hardwareAxis)
  Positive :=
    DependencyDischarged environmentBuild fullEnvironmentView
        (ArtifactObservation.identity (Bool × Bool × Bool)) toolchainAxis /\
      DependencyDischarged environmentBuild fullEnvironmentView
        (ArtifactObservation.identity (Bool × Bool × Bool)) hardwareAxis
  positive := ⟨completeProfile.r3Toolchain, completeProfile.r3Hardware⟩
  Negative :=
    Not (DependencyBound inputOnlyView hardwareAxis) /\
      Not (DependencyAbstracted environmentBuild
        (ArtifactObservation.identity (Bool × Bool × Bool)) hardwareAxis)
  negative :=
    ⟨hardware_not_bound_in_input_only_view,
      hardware_not_abstracted_at_exact_observation⟩
  attribution := .hatta2026R3
  scope := .dependencyDeclaredOrObservationallyAbstracted

/-- R4: the authorized current environment link covers its layout; an
authenticated link cannot cover a layout that rejects its issuer. -/
def r4Coverage : Row.{0} .r4ThirdPartyAttestation where
  FormalObject := SupplyChainLayout Unit environmentAttestation.Issuer
  formalObject := environmentLayout
  Positive := LayoutCovered environmentAttestation environmentLayout (7 : Nat)
  positive := environmentLayout_covered
  Negative := Not (LayoutCovered environmentAttestation unauthorizedLayout
    (7 : Nat))
  negative := unauthorizedLayout_not_covered
  attribution := .hatta2026R4WithInTotoDiscipline
  scope := .authorizedAuthenticatedAndCurrentLinks

/-- R5: the complete source-scoped ordered log reconstructs the current state;
dropping one receipt destroys both event completeness and reconstruction. -/
def r5Coverage : Row.{0} .r5CompleteTrajectory where
  FormalObject := TrajectoryReplay.EventLog Nat TrajectoryReplay.Canary.Update
    Unit Nat
  formalObject := TrajectoryReplay.Canary.completeLog
  Positive := TrajectoryReplay.replay TrajectoryReplay.Canary.updateSystem
    TrajectoryReplay.Canary.completeLog.initial
    TrajectoryReplay.Canary.completeLog.events = some 1
  positive := completeProfile_reconstructs_current
  Negative :=
    Not (TrajectoryReplay.Canary.lostReceiptLog.events.Perm
      TrajectoryReplay.Canary.authoritativeEvents) /\
      TrajectoryReplay.replay TrajectoryReplay.Canary.updateSystem
        TrajectoryReplay.Canary.lostReceiptLog.initial
        TrajectoryReplay.Canary.lostReceiptLog.events != some 1
  negative :=
    ⟨TrajectoryReplay.Canary.lostReceiptLog_not_eventComplete,
      TrajectoryReplay.Canary.lostReceiptLog_does_not_reconstruct_current⟩
  attribution := .hatta2026R5WithReplayExtension
  scope := .initialSourceTransitionOrderAndCurrentnessPremises

/-- R6: the current, non-identity observation-coarsening transports the complete
protected certificate family.  Output equality alone cannot create the
corresponding family map, and a stale receipt is not current evidence. -/
def r6Coverage : Row.{0} .r6RecursiveVerifiability where
  FormalObject := CurrentFamilyPreservingModification BaseSpecification
    coarseSpecification CoarseningProof coarseningDiscipline (7 : Nat)
  formalObject := currentCoarsening
  Positive := Nonempty (Certified coarseSpecification) /\
    coarseningReceipt.CurrentAt (7 : Nat)
  positive := currentCoarsening_preserves_recursive_verifiability
  Negative :=
    Not (Nonempty (FamilyPreservingModification BaseSpecification
      incompleteDeclarationSpecification Unit)) /\
      Not (staleCoarseningReceipt.CurrentAt (7 : Nat))
  negative :=
    ⟨no_familyPreservingModification_to_incompleteDeclaration Unit,
      stale_receipt_cannot_establish_recursive_verifiability⟩
  attribution := .hatta2026R6ForProtectedCurrentModifications
  scope := .currentFamilyPreservingModificationOnly

/-- R7: a full two-case verification meets its exact envelope.  A sampled
certificate does not establish the omitted universal obligation, and semantic
reproducibility can coexist with an infeasible audit plan. -/
def r7Coverage : Row.{0} .r7FeasibleVerification where
  FormalObject := VerificationRequirement Bool
  formalObject := completeIdentityRequirement
  Positive := MeetsRequirement completeIdentityCertificate
    completeIdentityRequirement
  positive := small_full_verification_meets_requirement
  Negative :=
    (selectiveSourceProperty false /\
      Not (forall source, selectiveSourceProperty source)) /\
      (Reproducible identityBuild (ArtifactObservation.identity Bool) /\
        Not (ResourceFeasible expensivePlan tinyLimit))
  negative :=
    ⟨sampled_verification_does_not_imply_universal,
      reproducible_but_verification_infeasible⟩
  attribution := .hatta2026R7WithWorkSpanExtension
  scope := .declaredCoverageAndResourceEnvelope

/-- The complete theorem-backed matrix.  Its fields cannot be populated by a
manifest or prose claim: each row contains its positive and negative proof
terms. -/
structure Matrix where
  r1 : Row.{1} .r1CompleteInputs
  r2 : Row.{1} .r2ReproducibleExecution
  r3 : Row.{1} .r3BoundEnvironment
  r4 : Row.{0} .r4ThirdPartyAttestation
  r5 : Row.{0} .r5CompleteTrajectory
  r6 : Row.{0} .r6RecursiveVerifiability
  r7 : Row.{0} .r7FeasibleVerification

def theoremCoverage : Matrix where
  r1 := r1Coverage
  r2 := r2Coverage
  r3 := r3Coverage
  r4 := r4Coverage
  r5 := r5Coverage
  r6 := r6Coverage
  r7 := r7Coverage

theorem every_requirement_has_positive_and_negative_coverage :
    (forall requirement : HattaRequirement,
      match requirement with
      | .r1CompleteInputs => r1Coverage.Positive /\ r1Coverage.Negative
      | .r2ReproducibleExecution => r2Coverage.Positive /\ r2Coverage.Negative
      | .r3BoundEnvironment => r3Coverage.Positive /\ r3Coverage.Negative
      | .r4ThirdPartyAttestation => r4Coverage.Positive /\ r4Coverage.Negative
      | .r5CompleteTrajectory => r5Coverage.Positive /\ r5Coverage.Negative
      | .r6RecursiveVerifiability => r6Coverage.Positive /\ r6Coverage.Negative
      | .r7FeasibleVerification => r7Coverage.Positive /\ r7Coverage.Negative) := by
  intro requirement
  cases requirement with
  | r1CompleteInputs => exact ⟨r1Coverage.positive, r1Coverage.negative⟩
  | r2ReproducibleExecution => exact ⟨r2Coverage.positive, r2Coverage.negative⟩
  | r3BoundEnvironment => exact ⟨r3Coverage.positive, r3Coverage.negative⟩
  | r4ThirdPartyAttestation => exact ⟨r4Coverage.positive, r4Coverage.negative⟩
  | r5CompleteTrajectory => exact ⟨r5Coverage.positive, r5Coverage.negative⟩
  | r6RecursiveVerifiability => exact ⟨r6Coverage.positive, r6Coverage.negative⟩
  | r7FeasibleVerification => exact ⟨r7Coverage.positive, r7Coverage.negative⟩

end Canary

end Mettapedia.GSLT.ReproducibleBuild.Coverage

#print axioms Mettapedia.GSLT.ReproducibleBuild.Coverage.Canary.every_requirement_has_positive_and_negative_coverage
