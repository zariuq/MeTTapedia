import Mettapedia.GSLT.LanguageDef.NIKDefaultCertifiedCompilation
import Mettapedia.GSLT.LanguageDef.ProofGSLTCheckerCapabilities

/-!
# Compilation traces as a NIK authority

A checked compilation trace should be replayable by the same NIK authority
family that checks guest proofs.  This module turns the generic compiler-state
trace calculus into one exact checker fibre.

The exact certificate scope and its semantic projection are deliberately
different:

* `Certified` says that an endpoint-matching trace exists and every local
  compiler certificate replays successfully;
* `Meaning` says only that the named observation agrees at the two endpoints.

Thus an accepted compilation article proves observation preservation, while
mere accidental equality of observations does not fabricate a compilation
article.  Concrete serialization remains a separate fail-closed frontend or
partial-codec obligation.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKCompilationAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.CompilationTraceChecker
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation
open Mettapedia.GSLT.LanguageDef.NIKDefaultCertifiedCompilation
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT.LanguageDef.NIKGSLT

universe uState uObservation uClaim uCertificate uMachine uKind uRequest

/-! ## Endpoint-bound compilation evidence -/

/-- The public claim made by one compilation article. -/
structure Claim (State : Type uState) where
  source : State
  artifact : State

/-- A linked compiler trace together with the endpoints at which its dependent
type was constructed.  The public checker separately compares these endpoints
with the submitted claim. -/
structure Certificate {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  source : State
  artifact : State
  trace : compilerChecker.Trace source artifact

/-- The exact scope characterized by compilation-certificate existence. -/
def Certified {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    (claim : Claim State) : Prop :=
  Nonempty (AcceptedTrace compilerChecker claim.source claim.artifact)

/-- The semantic observation projected from an accepted compilation article. -/
def Meaning {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    (claim : Claim State) : Prop :=
  compilerChecker.observe claim.artifact =
    compilerChecker.observe claim.source

/-- Replay an untrusted compiler trace, rejecting evidence whose stored
endpoints do not exactly match the submitted claim. -/
def replayChecker {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] : Checker (Claim State) (Certificate compilerChecker)
    where
  check := fun claim certificate =>
    if certificate.source = claim.source /\
        certificate.artifact = claim.artifact then
      certificate.trace.check
    else
      false

@[simp] theorem replayChecker_matching
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] {source artifact : State}
    (trace : compilerChecker.Trace source artifact) :
    (replayChecker compilerChecker).check
        ⟨source, artifact⟩ ⟨source, artifact, trace⟩ = trace.check := by
  simp [replayChecker]

theorem replayChecker_soundCertified
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (replayChecker compilerChecker).Sound (Certified compilerChecker) := by
  rintro ⟨claimSource, claimArtifact⟩
    ⟨certificateSource, certificateArtifact, trace⟩ accepted
  simp only [replayChecker] at accepted
  split at accepted
  next endpoints =>
    rcases endpoints with ⟨rfl, rfl⟩
    exact ⟨⟨trace, accepted⟩⟩
  next mismatch =>
    simp at accepted

theorem replayChecker_completeCertified
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (replayChecker compilerChecker).CertificateComplete
      (Certified compilerChecker) := by
  rintro ⟨source, artifact⟩ ⟨⟨trace, accepted⟩⟩
  exact ⟨⟨source, artifact, trace⟩, by
    simpa using accepted⟩

/-- Endpoint-bound compiler replay is exact for accepted-trace existence. -/
theorem replayChecker_authority
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (replayChecker compilerChecker).Authority (Certified compilerChecker)
    where
  sound := replayChecker_soundCertified compilerChecker
  complete := replayChecker_completeCertified compilerChecker

/-- Exact compilation evidence projects soundly to the named observation. -/
theorem certified_implies_meaning
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    (claim : Claim State) :
    Certified compilerChecker claim -> Meaning compilerChecker claim := by
  rintro ⟨acceptedTrace⟩
  exact acceptedTrace.observation_preserved

/-- The compilation checker fibre retains both its exact evidence scope and
the weaker observation-level consequence. -/
def authorityProjection
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (replayChecker compilerChecker).AuthorityProjection
      (Certified compilerChecker) (Meaning compilerChecker) where
  authority := replayChecker_authority compilerChecker
  project := certified_implies_meaning compilerChecker

/-! ## Agreement with OSLF/ProofGSLT finite reachability -/

/-- Every path in the checker-induced compiler GSLT can be reified back into
an accepted dependent compiler trace.  This is the converse of
`AcceptedTrace.toMultiStep` and uses the evidence retained in every generated
compiler edge. -/
theorem acceptedTrace_of_multiStep
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    {source artifact : State}
    (path : compilerChecker.toGSLT.MultiStep source artifact) :
    Nonempty (AcceptedTrace compilerChecker source artifact) := by
  refine GSLT.MultiStep.rec
    (motive := fun source artifact _ =>
      Nonempty (AcceptedTrace compilerChecker source artifact))
    (fun state => ⟨⟨.refl state, rfl⟩⟩) ?_ path
  intro source middle artifact edge rest inductionHypothesis
  · show Nonempty (AcceptedTrace compilerChecker source artifact)
    obtain ⟨evidence, edgeAccepted⟩ := edge
    obtain ⟨⟨tail, tailAccepted⟩⟩ := inductionHypothesis
    exact ⟨⟨.step evidence tail, by
      simp [CompilationTraceChecker.Trace.check, edgeAccepted,
        tailAccepted]⟩⟩

/-- Accepted compiler articles and finite reachability in the generated
compiler GSLT are the same exact scope. -/
theorem certified_iff_multiStep
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    (claim : Claim State) :
    Certified compilerChecker claim ↔
      compilerChecker.toGSLT.MultiStep claim.source claim.artifact := by
  constructor
  · rintro ⟨acceptedTrace⟩
    exact acceptedTrace.toMultiStep
  · exact acceptedTrace_of_multiStep compilerChecker

/-- Endpoint-bound evidence for one local edge of the generated compiler
GSLT. -/
structure EdgeCertificate
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  source : State
  target : State
  evidence : compilerChecker.Evidence source target

/-- The generated compiler theory has the same state carrier, so decidable
state equality transports definitionally to its term carrier. -/
instance instDecidableEqCompilerGSLTTerm
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] : DecidableEq compilerChecker.toGSLT.Term :=
  inferInstanceAs (DecidableEq State)

/-- The compiler's local evidence checker, viewed as an exact OSLF edge
authority for `compilerChecker.toGSLT`. -/
def stepAuthority
    {AuthorityId : Type uClaim}
    {State : Type uState} {Observation : Type uObservation}
    (authorityId : AuthorityId)
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    ProofGSLT.StepAuthority AuthorityId compilerChecker.toGSLT where
  id := authorityId
  Certificate := EdgeCertificate compilerChecker
  check := fun claim certificate =>
    if certificate.source = claim.source /\
        certificate.target = claim.target then
      compilerChecker.check certificate.source certificate.target
        certificate.evidence
    else
      false
  sound := by
    rintro ⟨claimSource, claimTarget⟩
      ⟨certificateSource, certificateTarget, evidence⟩ accepted
    simp only at accepted
    split at accepted
    next endpoints =>
      rcases endpoints with ⟨rfl, rfl⟩
      exact ⟨evidence, accepted⟩
    next mismatch =>
      simp at accepted

/-- The generated local edge authority is complete because every edge of
`toGSLT` was defined by existence of accepted compiler evidence. -/
theorem stepAuthority_complete
    {AuthorityId : Type uClaim}
    {State : Type uState} {Observation : Type uObservation}
    (authorityId : AuthorityId)
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (stepAuthority authorityId compilerChecker).Complete := by
  rintro ⟨source, target⟩ edge
  obtain ⟨evidence, accepted⟩ := edge
  exact ⟨⟨source, target, evidence⟩, by
    simp [stepAuthority, accepted]⟩

/-- OSLF-generated finite-trace replay is an exact authority for compiler
reachability.  This is the ProofGSLT/NIK route, rather than a second semantic
definition of compilation. -/
theorem generatedFiniteTrace_authority
    {AuthorityId : Type uClaim}
    {State : Type uState} {Observation : Type uObservation}
    (authorityId : AuthorityId)
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :
    (ProofGSLT.CheckerCapabilities.finiteTraceChecker
      (stepAuthority authorityId compilerChecker)).Authority
        ProofGSLT.TraceClaim.Meaning :=
  ProofGSLT.CheckerCapabilities.finiteTraceChecker_authority
    (stepAuthority authorityId compilerChecker)
    (stepAuthority_complete authorityId compilerChecker)

/-- The direct dependent compilation article and the OSLF-generated finite
trace authority characterize the same compiler-state relation. -/
theorem certified_iff_generatedFiniteTraceMeaning
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    (claim : Claim State) :
    Certified compilerChecker claim ↔
      ProofGSLT.TraceClaim.Meaning
        (theory := compilerChecker.toGSLT)
        ⟨claim.source, claim.artifact⟩ :=
  certified_iff_multiStep compilerChecker claim

/-! ## ProofGSLT-presented compiler steps -/

/-- When compiler edges have a two-sided ProofGSLT presentation, its ordinary
versioned articles become the local evidence inside the generated finite-trace
checker. -/
def proofGSLTFiniteTraceChecker
    {AuthorityId : Type uClaim}
    (authorityId : AuthorityId)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    {presentation : InferenceChecker.ValidatedPresentation}
    (adequacy : ProofGSLT.ExactStepPresentation
      compilerChecker.toGSLT presentation)
    [DecidableEq State] :=
  ProofGSLT.CheckerCapabilities.finiteTraceChecker
    (ProofGSLT.exactWireStepAuthority authorityId adequacy)

/-- Exact local ProofGSLT adequacy lifts compositionally to exact compiler
trace authority. -/
theorem proofGSLTFiniteTraceChecker_authority
    {AuthorityId : Type uClaim}
    (authorityId : AuthorityId)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    {presentation : InferenceChecker.ValidatedPresentation}
    (adequacy : ProofGSLT.ExactStepPresentation
      compilerChecker.toGSLT presentation)
    [DecidableEq State] :
    (proofGSLTFiniteTraceChecker authorityId compilerChecker adequacy).Authority
      ProofGSLT.TraceClaim.Meaning :=
  ProofGSLT.CheckerCapabilities.finiteTraceChecker_authority
    (ProofGSLT.exactWireStepAuthority authorityId adequacy)
    (ProofGSLT.exactWireStepAuthority_complete authorityId adequacy)

/-- The native dependent compiler article and a ProofGSLT-presented finite
article exist for exactly the same source/artifact pairs. -/
theorem certified_iff_exists_proofGSLTTraceCertificate
    {AuthorityId : Type uClaim}
    (authorityId : AuthorityId)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    {presentation : InferenceChecker.ValidatedPresentation}
    (adequacy : ProofGSLT.ExactStepPresentation
      compilerChecker.toGSLT presentation)
    [DecidableEq State] (claim : Claim State) :
    Certified compilerChecker claim ↔
      ∃ certificate,
        (proofGSLTFiniteTraceChecker authorityId compilerChecker adequacy).check
          (⟨claim.source, claim.artifact⟩ :
            ProofGSLT.TraceClaim compilerChecker.toGSLT)
          certificate = true := by
  exact (certified_iff_generatedFiniteTraceMeaning compilerChecker claim).trans
    ((proofGSLTFiniteTraceChecker_authority authorityId compilerChecker
      adequacy).meaning_iff_exists_certificate
        (⟨claim.source, claim.artifact⟩ :
          ProofGSLT.TraceClaim compilerChecker.toGSLT))

/-! ## Admission into the default NIK family -/

/-- The compilation authority as a one-fibre dependent family.  It can be
combined with guest authorities by the ordinary family-composition boundary;
no compiler-specific branch is added to the NIK machine. -/
def family {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] : AuthorityFamily Unit where
  Claim := fun _ => Claim State
  Certificate := fun _ => Certificate compilerChecker
  checker := fun _ => replayChecker compilerChecker
  Certified := fun _ => Certified compilerChecker
  Meaning := fun _ => Meaning compilerChecker
  projection := fun _ => authorityProjection compilerChecker

/-- The semantic no-serialization frontend used to establish the default-NIK
contract before choosing a concrete Prime request codec. -/
def typedFrontend
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :=
  Frontend.typed (family compilerChecker)

/-- Extend an arbitrary guest authority family with compiler-trace checking.
The disjoint kind tag is the only dispatcher extension; the NIK evaluator
remains generic. -/
def withCompilation
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :=
  AuthorityFamily.sum guest (family compilerChecker)

/-- The semantic frontend for the combined guest-plus-compilation family. -/
def combinedTypedFrontend
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :=
  Frontend.typed (withCompilation guest compilerChecker)

/-- A concrete request carrier enters only through a faithful, fail-closed
codec for typed submissions.  This is the staging seam implemented by a Prime
S-expression parser or another transport. -/
def encodedCombinedFrontend
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] {Request : Type uRequest}
    (codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request) :=
  Frontend.ofRequestCodec (withCompilation guest compilerChecker) codec

/-- Canonically package an accepted compiler trace as a typed NIK request. -/
def submission
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    TypedSubmission (family compilerChecker) :=
  ⟨(), ⟨source, artifact⟩,
    ⟨source, artifact, acceptedTrace.trace⟩⟩

/-- Package compiler evidence in the compilation branch of a combined NIK
family. -/
def combinedSubmission
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    TypedSubmission (withCompilation guest compilerChecker) :=
  ⟨.inr (), ULift.up ⟨source, artifact⟩,
    ULift.up ⟨source, artifact, acceptedTrace.trace⟩⟩

/-- Any independently accepted compiler trace is accepted by the ordinary
statusful NIK frontend, not by a privileged compiler-only path. -/
theorem acceptedTrace_defaultRun
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    (typedFrontend compilerChecker).run
        ((typedFrontend compilerChecker).encode (submission acceptedTrace)) =
      .accepted
        (TypedSubmission.claim (submission acceptedTrace)) := by
  have checked :
      ((family compilerChecker).checker ()).check
        (submission acceptedTrace).2.1
        (submission acceptedTrace).2.2 = true := by
    simpa [family, submission] using acceptedTrace.accepted
  simpa [checked] using
    (typedFrontend compilerChecker).run_encode (submission acceptedTrace)

/-- The same accepted request is a genuine execution of the default NIK GSLT. -/
theorem acceptedTrace_defaultNIKExecution
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    let frontend := typedFrontend compilerChecker
    let request := frontend.encode (submission acceptedTrace)
    let claim := TypedSubmission.claim (submission acceptedTrace)
    (NIKDefaultProfile.Atomic.theory frontend).MultiStep
      (.submitted request) (.completed (.accepted claim)) := by
  dsimp only
  exact (NIKDefaultProfile.Atomic.submitted_multiStep_completed_iff
    (typedFrontend compilerChecker) _ _).2
      (acceptedTrace_defaultRun acceptedTrace)

/-- Guest authorities and compilation authority genuinely coexist in one
statusful NIK dispatcher. -/
theorem acceptedTrace_combinedDefaultRun
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    (combinedTypedFrontend guest compilerChecker).run
        ((combinedTypedFrontend guest compilerChecker).encode
          (combinedSubmission guest acceptedTrace)) =
      .accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace)) := by
  have checked :
      ((withCompilation guest compilerChecker).checker (.inr ())).check
        (combinedSubmission guest acceptedTrace).2.1
        (combinedSubmission guest acceptedTrace).2.2 = true := by
    change (replayChecker compilerChecker).check
      ⟨source, artifact⟩
      ⟨source, artifact, acceptedTrace.trace⟩ = true
    simpa using acceptedTrace.accepted
  rw [(combinedTypedFrontend guest compilerChecker).run_encode]
  change (match
      ((withCompilation guest compilerChecker).checker (.inr ())).check
        (combinedSubmission guest acceptedTrace).2.1
        (combinedSubmission guest acceptedTrace).2.2 with
    | false => SubmissionOutcome.rejected
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))
    | true => SubmissionOutcome.accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))) =
      SubmissionOutcome.accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))
  rw [checked]

/-- The combined default NIK executes a compiler-certificate request without
a privileged compilation evaluator. -/
theorem acceptedTrace_combinedDefaultNIKExecution
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    let frontend := combinedTypedFrontend guest compilerChecker
    let request := frontend.encode (combinedSubmission guest acceptedTrace)
    let claim := TypedSubmission.claim (combinedSubmission guest acceptedTrace)
    (NIKDefaultProfile.Atomic.theory frontend).MultiStep
      (.submitted request) (.completed (.accepted claim)) := by
  dsimp only
  exact (NIKDefaultProfile.Atomic.submitted_multiStep_completed_iff
    (combinedTypedFrontend guest compilerChecker) _ _).2
      (acceptedTrace_combinedDefaultRun guest acceptedTrace)

/-- Canonically encoded compiler evidence receives the same result as the
semantic typed frontend.  Decoder failure and noncanonical forms remain
outside this theorem and fail as `malformed`. -/
theorem acceptedTrace_encodedDefaultRun
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {Request : Type uRequest}
    (codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request)
    {source artifact : State}
    (acceptedTrace : AcceptedTrace compilerChecker source artifact) :
    (encodedCombinedFrontend guest compilerChecker codec).run
        (codec.encode (combinedSubmission guest acceptedTrace)) =
      .accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace)) := by
  have checked :
      ((withCompilation guest compilerChecker).checker (.inr ())).check
        (combinedSubmission guest acceptedTrace).2.1
        (combinedSubmission guest acceptedTrace).2.2 = true := by
    change (replayChecker compilerChecker).check
      ⟨source, artifact⟩
      ⟨source, artifact, acceptedTrace.trace⟩ = true
    simpa using acceptedTrace.accepted
  change (encodedCombinedFrontend guest compilerChecker codec).run
      ((encodedCombinedFrontend guest compilerChecker codec).encode
        (combinedSubmission guest acceptedTrace)) =
    SubmissionOutcome.accepted
      (TypedSubmission.claim (combinedSubmission guest acceptedTrace))
  rw [(encodedCombinedFrontend guest compilerChecker codec).run_encode]
  change (match
      ((withCompilation guest compilerChecker).checker (.inr ())).check
        (combinedSubmission guest acceptedTrace).2.1
        (combinedSubmission guest acceptedTrace).2.2 with
    | false => SubmissionOutcome.rejected
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))
    | true => SubmissionOutcome.accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))) =
      SubmissionOutcome.accepted
        (TypedSubmission.claim (combinedSubmission guest acceptedTrace))
  rw [checked]

/-! ## Connection to certified NIK compilation -/

/-- The compiler article already stored by a certified machine compilation is
accepted by the compilation authority fibre. -/
theorem CertifiedMachineCompilation.compilation_checked_by_NIK
    {ClaimType : Type uClaim} {CertificateType : Type uCertificate}
    {guestChecker : Checker ClaimType CertificateType}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State]
    (compiled : CertifiedMachineCompilation.{uClaim, uCertificate, uState,
      uObservation, uMachine} guestChecker compilerChecker) :
    let frontend := typedFrontend compilerChecker
    let request := frontend.encode (submission compiled.compilation)
    let claim := TypedSubmission.claim (submission compiled.compilation)
    (NIKDefaultProfile.Atomic.theory frontend).MultiStep
      (.submitted request) (.completed (.accepted claim)) :=
  acceptedTrace_defaultNIKExecution compiled.compilation

/-! ## Non-circular Stage-0/Stage-1 bootstrapping -/

/-- A staged NIK compilation whose request language contains both the guest
authorities and its own compiler-trace authority. -/
abbrev BootstrapCompilation
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] :=
  NIKDefaultCertifiedCompilation.CertifiedCompilation
    (combinedTypedFrontend guest compilerChecker) compilerChecker

/-- The same bootstrap contract over a concrete, faithfully decoded request
carrier. -/
abbrev EncodedBootstrapCompilation
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] {Request : Type uRequest}
    (codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request) :=
  NIKDefaultCertifiedCompilation.CertifiedCompilation
    (encodedCombinedFrontend guest compilerChecker codec) compilerChecker

/-- The independently admitted source machine can replay the compilation
article that connects it to the generated artifact machine.  This is Stage 0
checking Stage 1, not the generated checker asserting its own correctness. -/
theorem BootstrapCompilation.sourceMachine_checks_compilation
    {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State]
    (compiled : BootstrapCompilation guest compilerChecker) :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest :=
      (combinedTypedFrontend guest compilerChecker).encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    (compiled.machineAt compiled.source).theory.MultiStep
      ((compiled.machineAt compiled.source).submit bootstrapRequest)
      ((compiled.machineAt compiled.source).completed
        (.accepted bootstrapClaim)) := by
  dsimp only
  exact ((compiled.machineAt compiled.source).completes_iff _ _).2
    (acceptedTrace_combinedDefaultRun guest compiled.compilation)

/-- Stage 0 also checks the compiler article after concrete request decoding;
the codec's left inverse connects this execution to the exact semantic
submission. -/
theorem EncodedBootstrapCompilation.sourceMachine_checks_compilation
    {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {Request : Type uRequest}
    {codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request}
    (compiled : EncodedBootstrapCompilation guest compilerChecker codec) :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest := codec.encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    (compiled.machineAt compiled.source).theory.MultiStep
      ((compiled.machineAt compiled.source).submit bootstrapRequest)
      ((compiled.machineAt compiled.source).completed
        (.accepted bootstrapClaim)) := by
  dsimp only
  exact ((compiled.machineAt compiled.source).completes_iff _ _).2
    (acceptedTrace_encodedDefaultRun guest codec compiled.compilation)

/-- Embed an ordinary guest claim into the guest branch of the combined NIK
family. -/
def guestClaim
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] (kind : Kind) (claim : guest.Claim kind) :
    (withCompilation guest compilerChecker).PackedClaim :=
  ⟨.inl kind, ULift.up claim⟩

@[simp] theorem guestClaim_meaning
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] (kind : Kind) (claim : guest.Claim kind) :
    (withCompilation guest compilerChecker).packedMeaning
        (guestClaim guest compilerChecker kind claim) ↔
      guest.Meaning kind claim := by
  rfl

/-- The complete bootstrap square.  Stage 0 checks the compilation article;
the compiler article preserves the named machine observation; and a distinct
Stage-1 execution receipt proves the selected combined-family meaning. -/
theorem BootstrapCompilation.compilation_and_execution_sound
    {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State]
    (compiled : BootstrapCompilation guest compilerChecker)
    {request : TypedSubmission (withCompilation guest compilerChecker)}
    {claim : (withCompilation guest compilerChecker).PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest :=
      (combinedTypedFrontend guest compilerChecker).encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    (compiled.machineAt compiled.source).theory.MultiStep
        ((compiled.machineAt compiled.source).submit bootstrapRequest)
        ((compiled.machineAt compiled.source).completed
          (.accepted bootstrapClaim)) /\
      compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) /\
      (withCompilation guest compilerChecker).packedMeaning claim := by
  dsimp only
  exact ⟨compiled.sourceMachine_checks_compilation,
    NIKDefaultCertifiedCompilation.CertifiedCompilation.compilation_and_execution_sound
      compiled receipt⟩

/-- Concrete-request version of the complete bootstrap square. -/
theorem EncodedBootstrapCompilation.compilation_and_execution_sound
    {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {Request : Type uRequest}
    {codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request}
    (compiled : EncodedBootstrapCompilation guest compilerChecker codec)
    {request : Request}
    {claim : (withCompilation guest compilerChecker).PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest := codec.encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    (compiled.machineAt compiled.source).theory.MultiStep
        ((compiled.machineAt compiled.source).submit bootstrapRequest)
        ((compiled.machineAt compiled.source).completed
          (.accepted bootstrapClaim)) /\
      compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) /\
      (withCompilation guest compilerChecker).packedMeaning claim := by
  dsimp only
  exact ⟨compiled.sourceMachine_checks_compilation,
    NIKDefaultCertifiedCompilation.CertifiedCompilation.compilation_and_execution_sound
      compiled receipt⟩

/-- Guest-specialized bootstrap theorem: successful Stage-1 replay returns to
the original guest meaning after the combined-family tag is erased. -/
theorem BootstrapCompilation.guest_execution_sound
    {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State]
    (compiled : BootstrapCompilation guest compilerChecker)
    {kind : Kind} {guestClaimPayload : guest.Claim kind}
    {request : TypedSubmission (withCompilation guest compilerChecker)}
    (receipt : compiled.CompletionReceipt request
      (.accepted (guestClaim guest compilerChecker kind guestClaimPayload))) :
    compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) /\
      guest.Meaning kind guestClaimPayload := by
  have sound := compiled.compilation_and_execution_sound receipt
  exact ⟨sound.2.1,
    (guestClaim_meaning guest compilerChecker kind guestClaimPayload).mp
      sound.2.2⟩

/-! ## Separating canaries -/

namespace Canary

open Mettapedia.GSLT.CompilationTraceCanary

def goodClaim : Claim State := ⟨.authored 7, .serialized 7⟩

def goodCertificate : Certificate checker :=
  ⟨.authored 7, .serialized 7, goodTrace⟩

theorem good_compilation_accepted :
    (replayChecker checker).check goodClaim goodCertificate = true := by
  exact goodTrace_accepted

/-- Negative: valid trace bytes cannot be replayed under a different public
endpoint claim. -/
theorem endpoint_mismatch_rejected :
    (replayChecker checker).check
      ⟨.authored 7, .serialized 8⟩ goodCertificate = false := by
  rfl

/-- Negative: a trace with an altered payload remains rejected even though its
stored endpoints agree with its submitted claim. -/
theorem payload_tamper_rejected :
    (replayChecker checker).check
      ⟨.authored 7, .serialized 8⟩
      ⟨.authored 7, .serialized 8, payloadTamperTrace⟩ = false := by
  exact payloadTamperTrace_rejected

inductive DisconnectedState where
  | left
  | right
deriving DecidableEq

def disconnectedChecker : CompilationTraceChecker DisconnectedState Unit where
  Evidence := fun _ _ => Unit
  check := fun _ _ _ => false
  observe := fun _ => ()
  sound := by
    intro source target evidence accepted
    simp at accepted

def disconnectedClaim : Claim DisconnectedState := ⟨.left, .right⟩

theorem disconnected_meaning :
    Meaning disconnectedChecker disconnectedClaim := by
  rfl

theorem disconnected_notCertified :
    Not (Certified disconnectedChecker disconnectedClaim) := by
  rintro ⟨⟨trace, accepted⟩⟩
  cases trace with
  | step evidence tail => simp [CompilationTraceChecker.Trace.check,
      disconnectedChecker] at accepted

/-- Observation equality is strictly weaker than evidence that a compilation
path occurred. -/
theorem observation_equality_is_not_compilation_evidence :
    Meaning disconnectedChecker disconnectedClaim /\
      Not (Certified disconnectedChecker disconnectedClaim) :=
  ⟨disconnected_meaning, disconnected_notCertified⟩

/-! A complete non-vacuous bootstrap instance. -/

def truthBootstrap : BootstrapCompilation
    NIKDefaultProfile.Canary.family
    NIKCertifiedCompilation.Canary.buildChecker where
  source := .authored
  artifact := .artifact
  machineAt := fun _ => NIKDefaultProfile.Refinement.atomic
    (combinedTypedFrontend NIKDefaultProfile.Canary.family
      NIKCertifiedCompilation.Canary.buildChecker)
  observeMachine := fun _ => true
  observesMachine := by
    intro state
    cases state <;> rfl
  compilation :=
    ⟨NIKCertifiedCompilation.Canary.buildTrace,
      NIKCertifiedCompilation.Canary.buildTrace_accepted⟩

def trueGuestSubmission : TypedSubmission
    (withCompilation NIKDefaultProfile.Canary.family
      NIKCertifiedCompilation.Canary.buildChecker) :=
  ⟨.inl .truth, ULift.up true, ULift.up ()⟩

def trueGuestReceipt : truthBootstrap.CompletionReceipt trueGuestSubmission
    (.accepted (guestClaim NIKDefaultProfile.Canary.family
      NIKCertifiedCompilation.Canary.buildChecker .truth true)) where
  path := (truthBootstrap.artifactMachine.completes_iff _ _).2 rfl

/-- Positive: the source NIK checks its compiler article and the generated NIK
separately checks a true guest judgment. -/
theorem truth_bootstrap_end_to_end :
    let bootstrapSubmission := combinedSubmission
      NIKDefaultProfile.Canary.family truthBootstrap.compilation
    let bootstrapRequest :=
      (combinedTypedFrontend NIKDefaultProfile.Canary.family
        NIKCertifiedCompilation.Canary.buildChecker).encode
          bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    (truthBootstrap.machineAt truthBootstrap.source).theory.MultiStep
        ((truthBootstrap.machineAt truthBootstrap.source).submit
          bootstrapRequest)
        ((truthBootstrap.machineAt truthBootstrap.source).completed
          (.accepted bootstrapClaim)) /\
      truthBootstrap.observeMachine truthBootstrap.artifactMachine =
        truthBootstrap.observeMachine
          (truthBootstrap.machineAt truthBootstrap.source) /\
      NIKDefaultProfile.Canary.family.Meaning .truth true := by
  have endToEnd :=
    truthBootstrap.compilation_and_execution_sound trueGuestReceipt
  exact ⟨endToEnd.1, endToEnd.2.1,
    (guestClaim_meaning NIKDefaultProfile.Canary.family
      NIKCertifiedCompilation.Canary.buildChecker .truth true).mp
        endToEnd.2.2⟩

def falseGuestSubmission : TypedSubmission
    (withCompilation NIKDefaultProfile.Canary.family
      NIKCertifiedCompilation.Canary.buildChecker) :=
  ⟨.inl .truth, ULift.up false, ULift.up ()⟩

/-- Negative: a valid compiler article cannot create an accepting execution
receipt for a rejected guest request. -/
theorem valid_compilation_does_not_accept_false_guest :
    Not (Nonempty (truthBootstrap.CompletionReceipt falseGuestSubmission
      (.accepted (guestClaim NIKDefaultProfile.Canary.family
        NIKCertifiedCompilation.Canary.buildChecker .truth false)))) := by
  rintro ⟨receipt⟩
  have accepted :=
    (truthBootstrap.artifactMachine.completes_iff _ _).mp receipt.path
  cases accepted

end Canary

end Mettapedia.GSLT.LanguageDef.NIKCompilationAuthority
