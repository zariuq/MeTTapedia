import Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

/-!
# Certified compilation of the statusful default NIK

The default NIK frontend includes parsing, authority resolution, and all four
logical outcomes.  A native Prime implementation may refine that reference
function through an arbitrary multi-stage GSLT.  Separately, its compiler may
emit an article proving that authored source reached the generated artifact
while preserving a named machine observation.

This module composes those obligations without conflating their evidence:

* the compilation article binds source to artifact;
* the execution receipt binds one request to one public result;
* exact frontend refinement binds both Stage 0 and the artifact to the same
  admitted authority family.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKDefaultCertifiedCompilation

open Mettapedia.GSLT
open Mettapedia.GSLT.CompilationTraceChecker
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

universe uKind uClaim uCertificate uRequest uParsed uState uObservation uMachine

/-- An independently certified compiler path whose states denote exact
implementations of one statusful frontend. -/
structure CertifiedCompilation
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  source : State
  artifact : State
  machineAt : State →
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend
  observeMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend → Observation
  observesMachine : ∀ state,
    compilerChecker.observe state = observeMachine (machineAt state)
  compilation : AcceptedTrace compilerChecker source artifact

namespace CertifiedCompilation

variable {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    {frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (compiled : CertifiedCompilation frontend compilerChecker)

/-- Adapt an ordinary proof-producing compiler.  Its normal artifact remains
the compiler output; certificate production is an erasable side channel. -/
def ofProofProducingCompilation
    (compiler : ProofProducingCompilation compilerChecker)
    (source : State)
    (machineAt : State →
      NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
        uCertificate, uParsed} frontend)
    (observeMachine :
      NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
        uCertificate, uParsed} frontend → Observation)
    (observesMachine : ∀ state,
      compilerChecker.observe state = observeMachine (machineAt state)) :
    CertifiedCompilation frontend compilerChecker where
  source := source
  artifact := compiler.compile source
  machineAt := machineAt
  observeMachine := observeMachine
  observesMachine := observesMachine
  compilation := ⟨compiler.certificate source, compiler.accepted source⟩

@[simp] theorem ofProofProducingCompilation_artifact
    (compiler : ProofProducingCompilation compilerChecker)
    (source : State)
    (machineAt : State →
      NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
        uCertificate, uParsed} frontend)
    (observeMachine :
      NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
        uCertificate, uParsed} frontend → Observation)
    (observesMachine : ∀ state,
      compilerChecker.observe state = observeMachine (machineAt state)) :
    (ofProofProducingCompilation compiler source machineAt observeMachine
      observesMachine).artifact = compiler.compile source :=
  rfl

/-- The exact statusful machine denoted by the compiled artifact. -/
abbrev artifactMachine := compiled.machineAt compiled.artifact

/-- The independent compiler article preserves the selected machine
observation. -/
theorem machineObservation_preserved :
    compiled.observeMachine compiled.artifactMachine =
      compiled.observeMachine (compiled.machineAt compiled.source) := by
  rw [← compiled.observesMachine compiled.artifact,
    ← compiled.observesMachine compiled.source]
  exact compiled.compilation.observation_preserved

/-- Because both compiler endpoints are exact refinements of the same
frontend, they agree on every public outcome independently of their internal
state representation. -/
theorem source_artifact_outcome_agreement (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    compiled.artifactMachine.theory.MultiStep
        (compiled.artifactMachine.submit request)
        (compiled.artifactMachine.completed outcome) ↔
      (compiled.machineAt compiled.source).theory.MultiStep
        ((compiled.machineAt compiled.source).submit request)
        ((compiled.machineAt compiled.source).completed outcome) :=
  NIKDefaultProfile.Refinement.machines_agree frontend
    compiled.artifactMachine (compiled.machineAt compiled.source)
    request outcome

/-- A runtime receipt is a concrete path in the generated machine.  It is not
the compiler article. -/
structure CompletionReceipt (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) where
  path : compiled.artifactMachine.theory.MultiStep
    (compiled.artifactMachine.submit request)
    (compiled.artifactMachine.completed outcome)

/-- An accepting artifact receipt establishes the exact certificate scope. -/
theorem acceptance_implies_certified
    {request : Request} {claim : family.PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    family.packedCertified claim := by
  apply frontend.accepted_implies_certified
  exact (compiled.artifactMachine.completes_iff request (.accepted claim)).mp
    receipt.path

/-- Guest meaning is a separate projection from the exact certificate scope. -/
theorem acceptance_implies_meaning
    {request : Request} {claim : family.PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    family.packedMeaning claim :=
  family.packedCertified_implies_meaning claim
    (compiled.acceptance_implies_certified receipt)

/-- The compositional end-to-end theorem retains compilation identity and
establishes the guest meaning from a separate execution receipt. -/
theorem compilation_and_execution_sound
    {request : Request} {claim : family.PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) ∧
      family.packedMeaning claim :=
  ⟨compiled.machineObservation_preserved,
    compiled.acceptance_implies_meaning receipt⟩

/-- Exact source-to-artifact certificate completeness for the declared
certified scope.  The compiler observation remains in the statement and the
request is transported through the frontend's canonical encoder. -/
theorem certified_correspondence (claim : family.PackedClaim) :
    family.packedCertified claim ↔
      compiled.observeMachine compiled.artifactMachine =
          compiled.observeMachine (compiled.machineAt compiled.source) ∧
        ∃ certificate : family.Certificate claim.1,
          Nonempty (compiled.CompletionReceipt
            (frontend.encode ⟨claim.1, claim.2, certificate⟩)
            (.accepted claim)) := by
  constructor
  · intro certified
    obtain ⟨certificate, accepted⟩ :=
      frontend.certified_has_accepted_request claim certified
    refine ⟨compiled.machineObservation_preserved, certificate, ?_⟩
    exact ⟨⟨(compiled.artifactMachine.completes_iff _ (.accepted claim)).2
      accepted⟩⟩
  · rintro ⟨_, certificate, ⟨receipt⟩⟩
    exact compiled.acceptance_implies_certified receipt

end CertifiedCompilation

/-! ## Positive and negative bootstrap canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation.Canary
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile.Canary

def compiledTruth : CertifiedCompilation frontend buildChecker where
  source := .authored
  artifact := .artifact
  machineAt := fun _ => NIKDefaultProfile.Refinement.atomic frontend
  observeMachine := fun _ => true
  observesMachine := by
    intro state
    cases state <;> rfl
  compilation := ⟨buildTrace, buildTrace_accepted⟩

def trueReceipt :
    compiledTruth.CompletionReceipt (.knownTruth true)
      (.accepted (truthClaim true)) where
  path := (compiledTruth.artifactMachine.completes_iff _ _).2 rfl

theorem true_end_to_end :
    compiledTruth.observeMachine compiledTruth.artifactMachine =
        compiledTruth.observeMachine
          (compiledTruth.machineAt compiledTruth.source) ∧
      family.packedMeaning (truthClaim true) :=
  compiledTruth.compilation_and_execution_sound trueReceipt

/-- Negative: a well-formed request whose checker returns false has no
acceptance receipt merely because the compiler article is valid. -/
theorem rejected_request_has_no_acceptance_receipt :
    ¬ Nonempty (compiledTruth.CompletionReceipt (.knownTruth false)
      (.accepted (truthClaim false))) := by
  rintro ⟨receipt⟩
  have accepted :=
    (compiledTruth.artifactMachine.completes_iff _ _).mp receipt.path
  cases accepted

end Canary

end Mettapedia.GSLT.LanguageDef.NIKDefaultCertifiedCompilation
