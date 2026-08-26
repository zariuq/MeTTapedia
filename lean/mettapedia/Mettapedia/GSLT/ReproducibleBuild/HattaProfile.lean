import Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

/-!
# Hatta's AGI-oriented reproducible-build requirements R1--R5

This module turns the first five requirements in Masayuki Hatta,
*Reproducibility Is the New Copyleft: Defining AGI-Oriented Reproducible
Builds* (2026), into a typed profile over relational reproducible builds.

R1 and R2 use the factorization and observation disciplines of the general
build core.  R3 distinguishes a declared dependency from a proved abstraction
that removes the dependency's observable influence.  R4 keeps authenticated
provenance and revision currentness separate from result reproducibility.  R5
uses the proof-relevant source-scoped trajectory theory rather than a final
state or recursively summarized log.

The in-toto-inspired layout/link interface below retains the distinction
between an owner's required supply-chain steps and authenticated evidence for
particular executions.  It abstracts authentication rather than claiming a
particular cryptographic scheme.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.HattaProfile

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

universe u uValue uKey uObserved

/-! ## R2: observations and explicit acceptance budgets -/

/-- A non-bit-exact reproducibility claim names both its artifact observation
and the acceptance test that observational equality is proved to satisfy.
Nothing here assumes the test is transitive or quotient-valued. -/
structure ReproducibilityBudget (Artifact : Type u) where
  observation : ArtifactObservation.{u, uObserved} Artifact
  test : AgreementTest Artifact
  sound : ObservationSoundForTest observation test

namespace ReproducibilityBudget

/-- Bit identity is the finest standard budget. -/
def bitExact (Artifact : Type u) : ReproducibilityBudget Artifact where
  observation := ArtifactObservation.identity Artifact
  test := { Accepts := Eq }
  sound := fun equality => equality

/-- Reproducibility at the declared observation discharges the budget's
acceptance test for every pair of executions from one source. -/
theorem accepts_of_reproducible
    {Source Artifact : Type u} {build : RelationalBuild Source Artifact}
    (budget : ReproducibilityBudget Artifact)
    (reproducible : Reproducible build budget.observation)
    {source : Source} {left right : Artifact}
    (leftBuild : build source left) (rightBuild : build source right) :
    budget.test.Accepts left right :=
  budget.sound (reproducible.2 source leftBuild rightBuild)

end ReproducibilityBudget

/-! ## R3: declared dependencies or proved abstraction -/

/-- One environmental dependency axis, together with the relation saying that
two full source states differ, if at all, only along that axis. -/
structure DependencyAxis (Source : Type u) where
  Value : Type uValue
  value : Source -> Value
  SameOtherwise : Source -> Source -> Prop

/-- The dependency is declared when its value factors through the declared
input view. -/
def DependencyBound
    {Source : Type u} (view : InputView Source)
    (axis : DependencyAxis.{u, uValue} Source) : Prop :=
  Function.FactorsThrough axis.value view.project

/-- An abstraction removes a dependency's observable influence when changing
only that axis cannot change any selected artifact observation. -/
def DependencyAbstracted
    {Source Artifact : Type u} (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation Artifact)
    (axis : DependencyAxis.{u, uValue} Source) : Prop :=
  forall {leftSource rightSource leftArtifact rightArtifact},
    axis.SameOtherwise leftSource rightSource ->
    build leftSource leftArtifact -> build rightSource rightArtifact ->
    observation.observe leftArtifact = observation.observe rightArtifact

/-- Hatta R3 permits exactly two honest treatments of a toolchain or hardware
dependency: declare it, or prove that the selected abstraction removes its
observable influence. -/
inductive DependencyDischarged
    {Source Artifact : Type u} (build : RelationalBuild Source Artifact)
    (view : InputView Source) (observation : ArtifactObservation Artifact)
    (axis : DependencyAxis.{u, uValue} Source) : Prop where
  | declared (bound : DependencyBound view axis)
  | abstracted (independent : DependencyAbstracted build observation axis)

/-! ## R4: authenticated provenance and in-toto-style coverage -/

/-- An attestation discipline states abstractly what evidence authenticates a
particular proof-relevant build occurrence for an issuer and revision. -/
structure AttestationDiscipline
    {Source Artifact : Type u} (build : RelationalBuild Source Artifact) where
  Issuer : Type u
  Revision : Type u
  Evidence : Type u
  Authenticates : Issuer -> Revision -> Occurrence build -> Evidence -> Prop

/-- Authenticated evidence for one concrete occurrence.  The occurrence keeps
the full source identity and execution witness. -/
structure Attestation
    {Source Artifact : Type u} {build : RelationalBuild Source Artifact}
    (discipline : AttestationDiscipline build) where
  occurrence : Occurrence build
  issuer : discipline.Issuer
  issuedAt : discipline.Revision
  evidence : discipline.Evidence
  authenticated : discipline.Authenticates issuer issuedAt occurrence evidence

namespace Attestation

variable {Source Artifact : Type u} {build : RelationalBuild Source Artifact}
  {discipline : AttestationDiscipline build}

/-- Attestation currentness is deliberately not part of authentication. -/
def CurrentAt (attestation : Attestation discipline)
    (currentRevision : discipline.Revision) : Prop :=
  attestation.issuedAt = currentRevision

/-- The full source state remains recoverable from an attestation. -/
def source (attestation : Attestation discipline) : Source :=
  attestation.occurrence.source

/-- The produced artifact remains recoverable from an attestation. -/
def artifact (attestation : Attestation discipline) : Artifact :=
  attestation.occurrence.artifact

end Attestation

/-- A project-owner layout identifies required steps and the issuers permitted
to attest them.  It is a policy object, not an execution record. -/
structure SupplyChainLayout (Step Issuer : Type u) where
  Required : Step -> Prop
  Authorizes : Step -> Issuer -> Prop

/-- An in-toto-style link joins one required step to authenticated evidence for
a particular build occurrence and proves the issuer was authorized. -/
structure SupplyChainLink
    {Source Artifact Step : Type u} {build : RelationalBuild Source Artifact}
    (discipline : AttestationDiscipline build)
    (layout : SupplyChainLayout Step discipline.Issuer) where
  step : Step
  attestation : Attestation discipline
  authorized : layout.Authorizes step attestation.issuer

/-- Every required layout step has an authenticated, authorized, current link.
The layout and its links remain distinct data. -/
def LayoutCovered
    {Source Artifact Step : Type u} {build : RelationalBuild Source Artifact}
    (discipline : AttestationDiscipline build)
    (layout : SupplyChainLayout Step discipline.Issuer)
    (currentRevision : discipline.Revision) : Prop :=
  forall step, layout.Required step ->
    exists link : SupplyChainLink discipline layout,
      link.step = step /\ link.attestation.CurrentAt currentRevision

/-! ## The combined R1--R5 profile -/

/-- A theorem-backed profile for Hatta R1--R5.  Every field is a semantic
obligation or typed evidence object; a manifest or checklist alone cannot
inhabit this structure. -/
structure Profile
    (Source Artifact State Event EvidenceSource Step : Type u)
    [DecidableEq EvidenceSource] where
  build : RelationalBuild Source Artifact
  declaredInputs : InputView.{u, u} Source
  budget : ReproducibilityBudget.{u, u} Artifact

  /-- R1: the declared view contains every distinction used by the selected
  artifact observation. -/
  r1 : DeclarationSufficient build declaredInputs budget.observation

  /-- R2: every full source rebuilds and its executions agree at the selected
  observation. -/
  r2 : Reproducible build budget.observation

  toolchain : DependencyAxis.{u, u} Source
  hardware : DependencyAxis.{u, u} Source

  /-- R3: bind the toolchain or prove it observationally abstracted. -/
  r3Toolchain : DependencyDischarged build declaredInputs budget.observation
    toolchain

  /-- R3: bind the hardware or prove it observationally abstracted. -/
  r3Hardware : DependencyDischarged build declaredInputs budget.observation
    hardware

  attestation : AttestationDiscipline build
  layout : SupplyChainLayout Step attestation.Issuer
  attestationRevision : attestation.Revision

  /-- R4: every required step has a current authenticated link from an
  authorized issuer. -/
  r4 : LayoutCovered attestation layout attestationRevision

  eventSystem : EventSystem State Event
  eventOrder : EventOrder.{u, u} Event
  requiredSources : Event -> Finset EvidenceSource
  authoritativeInitial : State
  authoritativeEvents : List Event
  eventLog : EventLog State Event EvidenceSource attestation.Revision

  /-- R5: the retained log has the exact initial state and complete ordered
  event/source coverage, faithfully implements transitions, and is current. -/
  r5 : ReplayPremises eventSystem eventOrder requiredSources
    authoritativeInitial authoritativeEvents eventLog attestationRevision

/-- R1 and R2 jointly recover declared-view reproducibility. -/
theorem Profile.declaredViewReproducible
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    {profile : Profile Source Artifact State Event EvidenceSource Step} :
    DeclaredViewReproducible profile.build profile.declaredInputs
      profile.budget.observation :=
  ⟨profile.r2.1, profile.r1⟩

/-- R5 supplies the proof-relevant-trajectory/executable-replay equivalence for
the profile's current revision. -/
theorem Profile.reconstruction_iff_replay
    {Source Artifact State Event EvidenceSource Step : Type u}
    [DecidableEq EvidenceSource]
    {profile : Profile Source Artifact State Event EvidenceSource Step}
    (final : State) :
    Nonempty (Trajectory profile.eventSystem.Step
      profile.authoritativeInitial profile.authoritativeEvents final) <->
      replay profile.eventSystem profile.eventLog.initial
        profile.eventLog.events = some final :=
  currentStateReconstruction_iff_logReplay profile.eventSystem
    profile.eventOrder profile.requiredSources profile.authoritativeInitial
    profile.authoritativeEvents profile.eventLog profile.attestationRevision
    profile.r5 final

/-! ## Independence and dependency controls -/

namespace Canary

/-! ### Authenticated provenance does not imply reproducibility -/

def branchingBuild : RelationalBuild Unit Bool := fun _ _ => PUnit

def exactBool : ArtifactObservation Bool := ArtifactObservation.identity Bool

theorem branchingBuild_not_reproducible :
    Not (Reproducible branchingBuild exactBool) := by
  rintro ⟨_, consistent⟩
  have equal := consistent () (left := false) (right := true) ⟨⟩ ⟨⟩
  simp [exactBool, ArtifactObservation.identity] at equal

def permissiveAttestation : AttestationDiscipline branchingBuild where
  Issuer := Unit
  Revision := Nat
  Evidence := Unit
  Authenticates := fun _ revision _ _ => revision = (0 : Nat)

def authenticatedBranch : Attestation permissiveAttestation where
  occurrence := ⟨(), false, ⟨⟩⟩
  issuer := ()
  issuedAt := by
    change Nat
    exact 0
  evidence := ()
  authenticated := by
    change (0 : Nat) = 0
    rfl

theorem authenticatedBranch_current :
    authenticatedBranch.CurrentAt (0 : Nat) := by
  simp [Attestation.CurrentAt, authenticatedBranch, permissiveAttestation]

theorem authentic_provenance_does_not_imply_reproducibility :
    Nonempty (Attestation permissiveAttestation) /\
      Not (Reproducible branchingBuild exactBool) :=
  ⟨⟨authenticatedBranch⟩, branchingBuild_not_reproducible⟩

/-! ### Reproducibility does not imply trustworthy provenance -/

def identityBuild : RelationalBuild Bool Bool :=
  fun source artifact => PLift (artifact = source)

theorem identityBuild_reproducible :
    Reproducible identityBuild (ArtifactObservation.identity Bool) := by
  constructor
  · intro source
    exact ⟨⟨source, ⟨rfl⟩⟩⟩
  · intro source left right leftBuild rightBuild
    cases leftBuild with
    | up leftEq =>
        cases rightBuild with
        | up rightEq => simp_all

def rejectingAttestation : AttestationDiscipline identityBuild where
  Issuer := Unit
  Revision := Nat
  Evidence := Unit
  Authenticates := fun _ _ _ _ => False

theorem no_rejectingAttestation :
    Not (Nonempty (Attestation rejectingAttestation)) := by
  rintro ⟨attestation⟩
  exact attestation.authenticated

theorem matching_artifacts_do_not_imply_trustworthy_provenance :
    Reproducible identityBuild (ArtifactObservation.identity Bool) /\
      Not (Nonempty (Attestation rejectingAttestation)) :=
  ⟨identityBuild_reproducible, no_rejectingAttestation⟩

/-! ### R3 declaration and abstraction are distinct -/

structure Environment where
  input : Bool
  toolchain : Bool
  hardware : Bool
deriving DecidableEq

def environmentBuild : RelationalBuild Environment (Bool × Bool × Bool) :=
  fun source artifact =>
    PLift (artifact = (source.input, source.toolchain, source.hardware))

def fullEnvironmentView : InputView Environment where
  View := Environment
  project := id

def inputOnlyView : InputView Environment where
  View := Bool
  project := Environment.input

def hardwareAxis : DependencyAxis Environment where
  Value := Bool
  value := Environment.hardware
  SameOtherwise := fun left right =>
    left.input = right.input /\ left.toolchain = right.toolchain

theorem hardware_bound_in_full_view :
    DependencyBound fullEnvironmentView hardwareAxis := by
  intro left right equal
  simpa [hardwareAxis, fullEnvironmentView] using
    congrArg Environment.hardware equal

theorem hardware_not_bound_in_input_only_view :
    Not (DependencyBound inputOnlyView hardwareAxis) := by
  intro bound
  let left : Environment := ⟨false, false, false⟩
  let right : Environment := ⟨false, false, true⟩
  have collision : inputOnlyView.project left = inputOnlyView.project right := rfl
  have equal := bound collision
  simp [hardwareAxis, left, right] at equal

def inputObservation : ArtifactObservation (Bool × Bool × Bool) where
  Observed := Bool
  observe := Prod.fst

theorem hardware_abstracted_at_input_observation :
    DependencyAbstracted environmentBuild inputObservation hardwareAxis := by
  intro leftSource rightSource leftArtifact rightArtifact sameOther
    leftBuild rightBuild
  cases leftBuild with
  | up leftEq =>
      cases rightBuild with
      | up rightEq =>
          subst leftArtifact
          subst rightArtifact
          exact sameOther.1

theorem hardware_not_abstracted_at_exact_observation :
    Not (DependencyAbstracted environmentBuild
      (ArtifactObservation.identity (Bool × Bool × Bool)) hardwareAxis) := by
  intro abstracted
  let left : Environment := ⟨false, false, false⟩
  let right : Environment := ⟨false, false, true⟩
  have sameOther : hardwareAxis.SameOtherwise left right := ⟨rfl, rfl⟩
  have equal := abstracted sameOther (leftArtifact := (false, false, false))
    (rightArtifact := (false, false, true)) ⟨rfl⟩ ⟨rfl⟩
  simp [ArtifactObservation.identity] at equal

/-! ### A complete R1--R5 inhabitant and a missing-link rejection -/

def toolchainAxis : DependencyAxis Environment where
  Value := Bool
  value := Environment.toolchain
  SameOtherwise := fun left right =>
    left.input = right.input /\ left.hardware = right.hardware

theorem toolchain_bound_in_full_view :
    DependencyBound fullEnvironmentView toolchainAxis := by
  intro left right equal
  simpa [toolchainAxis, fullEnvironmentView] using
    congrArg Environment.toolchain equal

theorem environmentBuild_reproducible :
    Reproducible environmentBuild
      (ArtifactObservation.identity (Bool × Bool × Bool)) := by
  constructor
  · intro source
    exact ⟨⟨(source.input, source.toolchain, source.hardware), ⟨rfl⟩⟩⟩
  · intro source left right leftBuild rightBuild
    cases leftBuild with
    | up leftEq =>
        cases rightBuild with
        | up rightEq => simp_all

theorem environmentBuild_declarationSufficient :
    DeclarationSufficient environmentBuild fullEnvironmentView
      (ArtifactObservation.identity (Bool × Bool × Bool)) := by
  intro left right sameDeclaration
  have sameSource : left.source = right.source := by
    simpa [declaredOccurrence, fullEnvironmentView] using sameDeclaration
  have leftArtifact : left.artifact =
      (left.source.input, left.source.toolchain, left.source.hardware) :=
    left.witness.down
  have rightArtifact : right.artifact =
      (right.source.input, right.source.toolchain, right.source.hardware) :=
    right.witness.down
  simp [observedOccurrence, ArtifactObservation.identity, leftArtifact,
    rightArtifact, sameSource]

def environmentAttestation : AttestationDiscipline environmentBuild where
  Issuer := Unit
  Revision := Nat
  Evidence := Unit
  Authenticates := fun _ _ _ _ => True

def environmentLayout :
    SupplyChainLayout Unit environmentAttestation.Issuer where
  Required := fun _ => True
  Authorizes := fun _ _ => True

def environmentOccurrence : Occurrence environmentBuild :=
  ⟨⟨false, false, false⟩, (false, false, false), ⟨rfl⟩⟩

def environmentAuthenticatedOccurrence :
    Attestation environmentAttestation where
  occurrence := environmentOccurrence
  issuer := ()
  issuedAt := by
    change Nat
    exact 7
  evidence := ()
  authenticated := trivial

def environmentLink :
    SupplyChainLink environmentAttestation environmentLayout where
  step := ()
  attestation := environmentAuthenticatedOccurrence
  authorized := trivial

theorem environmentLayout_covered :
    LayoutCovered environmentAttestation environmentLayout (7 : Nat) := by
  intro step _required
  rcases step with ⟨⟩
  refine ⟨environmentLink, rfl, ?_⟩
  simp [Attestation.CurrentAt, environmentLink,
    environmentAuthenticatedOccurrence]

/-- The complete canary inhabits all five requirements simultaneously.  Its
R5 component is the ordered reset/increment history from the replay canary. -/
def completeProfile :
    Profile Environment (Bool × Bool × Bool) Nat
      TrajectoryReplay.Canary.Update Unit Unit where
  build := environmentBuild
  declaredInputs := fullEnvironmentView
  budget := ReproducibilityBudget.bitExact _
  r1 := environmentBuild_declarationSufficient
  r2 := environmentBuild_reproducible
  toolchain := toolchainAxis
  hardware := hardwareAxis
  r3Toolchain := .declared toolchain_bound_in_full_view
  r3Hardware := .declared hardware_bound_in_full_view
  attestation := environmentAttestation
  layout := environmentLayout
  attestationRevision := by
    change Nat
    exact 7
  r4 := environmentLayout_covered
  eventSystem := TrajectoryReplay.Canary.updateSystem
  eventOrder := TrajectoryReplay.Canary.updateOrder
  requiredSources := TrajectoryReplay.Canary.requiredSources
  authoritativeInitial := 41
  authoritativeEvents := TrajectoryReplay.Canary.authoritativeEvents
  eventLog := TrajectoryReplay.Canary.completeLog
  r5 := TrajectoryReplay.Canary.completeLog_premises

theorem completeProfile_reconstructs_current :
    replay completeProfile.eventSystem completeProfile.eventLog.initial
      completeProfile.eventLog.events = some 1 :=
  completeProfile.reconstruction_iff_replay 1 |>.mp
    TrajectoryReplay.Canary.authoritativeTrajectory

def unauthorizedLayout :
    SupplyChainLayout Unit environmentAttestation.Issuer where
  Required := fun _ => True
  Authorizes := fun _ _ => False

/-- Authentication alone cannot fill a required link when the layout does not
authorize its issuer. -/
theorem unauthorizedLayout_not_covered :
    Not (LayoutCovered environmentAttestation unauthorizedLayout (7 : Nat)) := by
  intro covered
  obtain ⟨link, _, _⟩ := covered () trivial
  exact link.authorized

end Canary

end Mettapedia.GSLT.ReproducibleBuild.HattaProfile

#print axioms Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Profile.reconstruction_iff_replay
#print axioms Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.authentic_provenance_does_not_imply_reproducibility
#print axioms Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.matching_artifacts_do_not_imply_trustworthy_provenance
#print axioms Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.completeProfile_reconstructs_current
#print axioms Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.unauthorizedLayout_not_covered
