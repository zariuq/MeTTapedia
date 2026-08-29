import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.NIKCompilationAuthority

/-!
# Endpoint-certified staged NIK pipelines

Compilation intermediates need not each denote an entire executable NIK.
They need locally checked transition evidence.  Only the authored source and
generated artifact endpoints need exact interpretations as implementations of
the same public NIK frontend.

This module isolates that minimal boundary and then composes it with the
compiler-trace authority:

1. an independently accepted compiler trace connects source to artifact;
2. the source and artifact are exact refinements of one statusful frontend;
3. the source machine can replay the compiler article as an ordinary NIK
   request;
4. a separate artifact execution receipt establishes the guest meaning.

An authored `CalculusLanguageDef` may supply the source endpoint through
`AuthoredMachine`.  A concrete Prime request grammar enters only through the
faithful partial codec already required by `encodedCombinedFrontend`.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKStagedPipeline

open Mettapedia.GSLT
open Mettapedia.GSLT.CompilationTraceChecker
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKCompilationAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT.LanguageDef.TotalGSLT

universe uKind uClaim uCertificate uRequest uParsed uMachine
  uState uObservation uFiber

/-! ## Minimal endpoint-certified compilation -/

/-- A semantic interpretation of the two externally meaningful compiler
endpoints.  The relations may be graphs of verified decoders, elaborators, or
artifact interpreters.  They are deliberately distinct from the compiler's
observation: a digest can identify an artifact without explaining what that
artifact executes.

No interpretation is required for private intermediate compiler states. -/
structure EndpointDenotation
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  SourceDenotes : State ->
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend -> Prop
  ArtifactDenotes : State ->
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend -> Prop
  source_functional : forall {state left right},
    SourceDenotes state left -> SourceDenotes state right -> left = right
  artifact_functional : forall {state left right},
    ArtifactDenotes state left -> ArtifactDenotes state right -> left = right
  observeMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend -> Observation
  source_observation : forall {state machine},
    SourceDenotes state machine ->
      compilerChecker.observe state = observeMachine machine
  artifact_observation : forall {state machine},
    ArtifactDenotes state machine ->
      compilerChecker.observe state = observeMachine machine

/-- A checked compiler path with exact NIK interpretations only at its two
semantic endpoints.  Intermediate compiler states remain ordinary states of
the compiler GSLT. -/
structure EndpointCompilation
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  source : State
  artifact : State
  sourceMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend
  artifactMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend
  observeMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend -> Observation
  observesSource :
    compilerChecker.observe source = observeMachine sourceMachine
  observesArtifact :
    compilerChecker.observe artifact = observeMachine artifactMachine
  compilation : AcceptedTrace compilerChecker source artifact

/-- The endpoint-minimal compiler contract with an explicit interpretation of
the exact source and artifact states.  This is the appropriate boundary for a
serialized descriptor or generated pack: identity evidence and machine
meaning are both retained, but remain different obligations. -/
structure DenotedEndpointCompilation
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  denotation : EndpointDenotation.{uKind, uClaim, uCertificate, uRequest,
    uParsed, uMachine, uState, uObservation} frontend compilerChecker
  source : State
  artifact : State
  sourceMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend
  artifactMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, uMachine, uClaim,
      uCertificate, uParsed} frontend
  sourceDenoted : denotation.SourceDenotes source sourceMachine
  artifactDenoted : denotation.ArtifactDenotes artifact artifactMachine
  compilation : AcceptedTrace compilerChecker source artifact

namespace DenotedEndpointCompilation

variable {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    {frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (compiled : DenotedEndpointCompilation.{uKind, uClaim, uCertificate,
      uRequest, uParsed, uMachine, uState, uObservation} frontend
        compilerChecker)

/-- Forget the explicit denotation witnesses only after deriving their
observation equations. -/
def toEndpointCompilation : EndpointCompilation frontend compilerChecker where
  source := compiled.source
  artifact := compiled.artifact
  sourceMachine := compiled.sourceMachine
  artifactMachine := compiled.artifactMachine
  observeMachine := compiled.denotation.observeMachine
  observesSource :=
    compiled.denotation.source_observation compiled.sourceDenoted
  observesArtifact :=
    compiled.denotation.artifact_observation compiled.artifactDenoted
  compilation := compiled.compilation

@[simp] theorem toEndpointCompilation_source :
    compiled.toEndpointCompilation.source = compiled.source :=
  rfl

@[simp] theorem toEndpointCompilation_artifact :
    compiled.toEndpointCompilation.artifact = compiled.artifact :=
  rfl

end DenotedEndpointCompilation

namespace EndpointCompilation

variable {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    {frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (compiled : EndpointCompilation.{uKind, uClaim, uCertificate, uRequest,
      uParsed, uMachine, uState, uObservation} frontend compilerChecker)

/-- Compiler replay preserves the selected endpoint-machine observation. -/
theorem machineObservation_preserved :
    compiled.observeMachine compiled.artifactMachine =
      compiled.observeMachine compiled.sourceMachine := by
  rw [<- compiled.observesArtifact, <- compiled.observesSource]
  exact compiled.compilation.observation_preserved

/-- Both endpoints expose exactly the same public logical outcomes because
they refine one frontend, independently of compiler observation choice. -/
theorem source_artifact_outcome_agreement (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    compiled.artifactMachine.theory.MultiStep
        (compiled.artifactMachine.submit request)
        (compiled.artifactMachine.completed outcome) <->
      compiled.sourceMachine.theory.MultiStep
        (compiled.sourceMachine.submit request)
        (compiled.sourceMachine.completed outcome) :=
  NIKDefaultProfile.Refinement.machines_agree frontend
    compiled.artifactMachine compiled.sourceMachine request outcome

/-- A runtime receipt is a path in the generated endpoint, distinct from the
compiler article. -/
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

/-- Projection from exact certificate scope to guest meaning remains a
separate authority-family theorem. -/
theorem acceptance_implies_meaning
    {request : Request} {claim : family.PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    family.packedMeaning claim :=
  family.packedCertified_implies_meaning claim
    (compiled.acceptance_implies_certified receipt)

/-- Endpoint-only compilation and artifact execution compose without
assigning machine meanings to intermediate compiler states. -/
theorem compilation_and_execution_sound
    {request : Request} {claim : family.PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine compiled.sourceMachine /\
      family.packedMeaning claim :=
  ⟨compiled.machineObservation_preserved,
    compiled.acceptance_implies_meaning receipt⟩

/-- The older every-state interpretation is a specialization of the minimal
endpoint boundary. -/
def ofEveryState
    (everyState :
      NIKDefaultCertifiedCompilation.CertifiedCompilation frontend
        compilerChecker) : EndpointCompilation frontend compilerChecker where
  source := everyState.source
  artifact := everyState.artifact
  sourceMachine := everyState.machineAt everyState.source
  artifactMachine := everyState.artifactMachine
  observeMachine := everyState.observeMachine
  observesSource := everyState.observesMachine everyState.source
  observesArtifact := everyState.observesMachine everyState.artifact
  compilation := everyState.compilation

@[simp] theorem ofEveryState_source
    (everyState :
      NIKDefaultCertifiedCompilation.CertifiedCompilation frontend
        compilerChecker) :
    (ofEveryState everyState).source = everyState.source :=
  rfl

@[simp] theorem ofEveryState_artifact
    (everyState :
      NIKDefaultCertifiedCompilation.CertifiedCompilation frontend
        compilerChecker) :
    (ofEveryState everyState).artifact = everyState.artifact :=
  rfl

end EndpointCompilation

/-! ## Authored source endpoint -/

/-- An admitted flat calculus language whose denoted GSLT exactly implements
one statusful NIK frontend.  This is the authoring-to-semantics obligation for
an eventual `--lang prime` NIK pack; syntax alone is not authority. -/
structure AuthoredMachine
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request) where
  definition : CalculusLanguageDef
  admitted : definition.isAdmitted = true
  reductionLaws : ReductionRespectsEquations definition.toLanguageDef
  submit : Request -> (definition.toGSLT admitted reductionLaws).Term
  completed : SubmissionOutcome family.PackedClaim ->
    (definition.toGSLT admitted reductionLaws).Term
  completes_iff : forall request outcome,
    (definition.toGSLT admitted reductionLaws).MultiStep
        (submit request) (completed outcome) <->
      frontend.run request = outcome

namespace AuthoredMachine

variable {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    {frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request}
    (authored : AuthoredMachine frontend)

/-- The authored adequacy record is exactly an ordinary staged-machine
refinement whose theory is generated by the admitted language definition. -/
def toRefinement : NIKDefaultProfile.Refinement.Machine frontend where
  theory := authored.definition.toGSLT authored.admitted authored.reductionLaws
  submit := authored.submit
  completed := authored.completed
  completes_iff := authored.completes_iff

/-- Any generated/native machine implementing the same frontend agrees with
the authored GSLT on every public request outcome. -/
theorem agrees_with
    (native : NIKDefaultProfile.Refinement.Machine frontend)
    (request : Request) (outcome : SubmissionOutcome family.PackedClaim) :
    native.theory.MultiStep (native.submit request) (native.completed outcome) <->
      (authored.toRefinement).theory.MultiStep
        ((authored.toRefinement).submit request)
        ((authored.toRefinement).completed outcome) :=
  NIKDefaultProfile.Refinement.machines_agree frontend
    native authored.toRefinement request outcome

end AuthoredMachine

/-! ## Proof-producing compilation from an authored endpoint -/

/-- The implementation-facing staged contract.

The ordinary compiler function chooses the artifact.  Certificate mode adds a
trace for that same function; it does not choose another artifact.  The source
endpoint is the GSLT denoted by an admitted authored language, while the exact
compiler source and artifact states are interpreted through an explicit
endpoint denotation. -/
structure AuthoredProofProducingPipeline
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    (frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  denotation : EndpointDenotation.{uKind, uClaim, uCertificate, uRequest,
    uParsed, 0, uState, uObservation} frontend compilerChecker
  source : State
  compiler : ProofProducingCompilation compilerChecker
  authored : AuthoredMachine frontend
  artifactMachine :
    NIKDefaultProfile.Refinement.Machine.{uKind, uRequest, 0, uClaim,
      uCertificate, uParsed} frontend
  sourceDenoted : denotation.SourceDenotes source authored.toRefinement
  artifactDenoted : denotation.ArtifactDenotes (compiler.compile source)
    artifactMachine

namespace AuthoredProofProducingPipeline

variable {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {Request : Type uRequest}
    {frontend : Frontend.{uKind, uRequest, uParsed, uClaim, uCertificate}
      family Request}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (pipeline : AuthoredProofProducingPipeline frontend compilerChecker)

/-- Retain endpoint denotation while specializing the generic compiler trace
to the artifact selected by the ordinary compiler function. -/
def toDenotedEndpointCompilation :
    DenotedEndpointCompilation frontend compilerChecker where
  denotation := pipeline.denotation
  source := pipeline.source
  artifact := pipeline.compiler.compile pipeline.source
  sourceMachine := pipeline.authored.toRefinement
  artifactMachine := pipeline.artifactMachine
  sourceDenoted := pipeline.sourceDenoted
  artifactDenoted := pipeline.artifactDenoted
  compilation :=
    ⟨pipeline.compiler.certificate pipeline.source,
      pipeline.compiler.accepted pipeline.source⟩

/-- The ordinary endpoint theorem follows only after preserving the explicit
source/artifact interpretation. -/
def toEndpointCompilation : EndpointCompilation frontend compilerChecker :=
  pipeline.toDenotedEndpointCompilation.toEndpointCompilation

/-- Certificate production and normal compilation select definitionally the
same artifact. -/
@[simp] theorem certified_artifact_is_ordinary_compile :
    pipeline.toEndpointCompilation.artifact =
      pipeline.compiler.toRealization.compile () pipeline.source :=
  rfl

/-- The compiled artifact and admitted authored language have exactly the
same public outcome relation because both implement the same frontend. -/
theorem artifact_agrees_with_authored (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    pipeline.artifactMachine.theory.MultiStep
        (pipeline.artifactMachine.submit request)
        (pipeline.artifactMachine.completed outcome) <->
      (pipeline.authored.toRefinement).theory.MultiStep
        ((pipeline.authored.toRefinement).submit request)
        ((pipeline.authored.toRefinement).completed outcome) :=
  AuthoredMachine.agrees_with pipeline.authored pipeline.artifactMachine
    request outcome

end AuthoredProofProducingPipeline

/-! ## Encoded self-hosting endpoint pipeline -/

/-- Minimal staged endpoint pipeline over a concrete request codec. -/
abbrev EncodedEndpointBootstrap
    {Kind : Type uKind}
    (guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation)
    [DecidableEq State] {Request : Type uRequest}
    (codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request) :=
  EndpointCompilation
    (encodedCombinedFrontend guest compilerChecker codec) compilerChecker

namespace EncodedEndpointBootstrap

variable {Kind : Type uKind}
    {guest : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    [DecidableEq State] {Request : Type uRequest}
    {codec : Checker.PartialCodec
      (TypedSubmission (withCompilation guest compilerChecker)) Request}
    (compiled : EncodedEndpointBootstrap guest compilerChecker codec)

/-- The independently admitted source endpoint checks the concrete compiler
request that produced the artifact endpoint. -/
theorem sourceMachine_checks_compilation :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest := codec.encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    compiled.sourceMachine.theory.MultiStep
      (compiled.sourceMachine.submit bootstrapRequest)
      (compiled.sourceMachine.completed (.accepted bootstrapClaim)) := by
  dsimp only
  exact (compiled.sourceMachine.completes_iff _ _).2
    (acceptedTrace_encodedDefaultRun guest codec compiled.compilation)

/-- The endpoint-minimal, concrete-request bootstrap theorem. -/
theorem compilation_and_execution_sound
    {request : Request}
    {claim : (withCompilation guest compilerChecker).PackedClaim}
    (receipt : compiled.CompletionReceipt request (.accepted claim)) :
    let bootstrapSubmission :=
      combinedSubmission guest compiled.compilation
    let bootstrapRequest := codec.encode bootstrapSubmission
    let bootstrapClaim := TypedSubmission.claim bootstrapSubmission
    compiled.sourceMachine.theory.MultiStep
        (compiled.sourceMachine.submit bootstrapRequest)
        (compiled.sourceMachine.completed (.accepted bootstrapClaim)) /\
      compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine compiled.sourceMachine /\
      (withCompilation guest compilerChecker).packedMeaning claim := by
  dsimp only
  exact ⟨compiled.sourceMachine_checks_compilation,
    EndpointCompilation.compilation_and_execution_sound compiled receipt⟩

end EncodedEndpointBootstrap

/-! ## Endpoint canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! An admitted authored-language realization. -/

private theorem multiStep_stays_right_shape
    {left right : GSLT}
    {source target : (GSLT.disjointSum left right).Term}
    (steps : (GSLT.disjointSum left right).MultiStep source target)
    (start : right.Term) (shape : source = Sum.inr start) :
    exists finish : right.Term, target = Sum.inr finish := by
  let motive : forall (first second : (GSLT.disjointSum left right).Term),
      (GSLT.disjointSum left right).MultiStep first second -> Prop :=
    fun first second _ => forall initial : right.Term,
      first = Sum.inr initial ->
        exists finish : right.Term, second = Sum.inr finish
  refine GSLT.MultiStep.rec (motive := motive) ?_ ?_ steps start shape
  · intro term initial equal
    subst equal
    exact ⟨initial, rfl⟩
  · intro first middle final head rest inductionHypothesis initial equal
    subst equal
    cases head with
    | right reduction =>
        exact inductionHypothesis _ rfl

private theorem no_right_multiStep_left
    (left right : GSLT) (source : right.Term) (target : left.Term) :
    Not ((GSLT.disjointSum left right).MultiStep
      (Sum.inr source) (Sum.inl target)) := by
  intro steps
  obtain ⟨finish, impossible⟩ :=
    multiStep_stays_right_shape steps source rfl
  cases impossible

inductive AuthoredKind where
  | theoremhood
deriving DecidableEq

def authoredFamily : AuthorityFamily AuthoredKind where
  Claim := fun _ => Unit
  Certificate := fun _ => Unit
  checker := fun _ => { check := fun _ _ => true }
  Certified := fun _ _ => True
  Meaning := fun _ _ => True
  projection := by
    intro kind
    exact
      { authority :=
          { sound := by intro claim certificate accepted; trivial
            complete := by intro claim meaningful; exact ⟨(), rfl⟩ }
        project := by intro claim certified; trivial }

def authoredFrontend := Frontend.typed authoredFamily

private def evenGoal : GoalState :=
  [.apply "Even" [.apply "z" []]]

private def zeroPattern : Pattern := .apply "z" []

private def evenLaws : ReductionRespectsEquations
    Example.evenNumbers.toLanguageDef :=
  ReductionRespectsEquations.of_no_equations rfl

private abbrev evenLanguageTheory : GSLT :=
  languageGSLT Example.evenNumbers.toLanguageDef evenLaws

private abbrev evenProofTheory : GSLT :=
  proofSearchGSLT
    (Example.evenNumbers.validated Example.evenNumbers_admitted)

/-- A real admitted flat calculus language implementing the one-request NIK
frontend.  Its accepting execution is the existing derivation that zero is
even; every non-accepting public outcome is placed in the disjoint object
summand and is therefore unreachable from the proof-search summand. -/
def authoredEvenMachine : AuthoredMachine authoredFrontend where
  definition := Example.evenNumbers
  admitted := Example.evenNumbers_admitted
  reductionLaws := evenLaws
  submit := fun _ => inCalculus evenGoal
  completed
    | .accepted _ => inCalculus []
    | .malformed => inLanguage zeroPattern
    | .unsupported => inLanguage zeroPattern
    | .rejected _ => inLanguage zeroPattern
  completes_iff := by
    rintro ⟨kind, claim, certificate⟩ outcome
    cases kind
    cases claim
    cases certificate
    cases outcome with
    | malformed =>
        constructor
        · intro path
          exact (no_right_multiStep_left evenLanguageTheory evenProofTheory
            evenGoal zeroPattern path).elim
        · intro impossible
          cases impossible
    | unsupported =>
        constructor
        · intro path
          exact (no_right_multiStep_left evenLanguageTheory evenProofTheory
            evenGoal zeroPattern path).elim
        · intro impossible
          cases impossible
    | rejected packedClaim =>
        rcases packedClaim with ⟨packedKind, packedClaim⟩
        cases packedKind
        cases packedClaim
        constructor
        · intro path
          exact (no_right_multiStep_left evenLanguageTheory evenProofTheory
            evenGoal zeroPattern path).elim
        · intro impossible
          cases impossible
    | accepted packedClaim =>
        rcases packedClaim with ⟨packedKind, packedClaim⟩
        cases packedKind
        cases packedClaim
        constructor
        · intro path
          rfl
        · intro accepted
          exact .step Example.zero_is_even (.refl _)

/-- Positive: the authored GSLT reaches the accepting terminal. -/
theorem authored_even_accepts :
    (authoredEvenMachine.toRefinement).theory.MultiStep
      ((authoredEvenMachine.toRefinement).submit
        ⟨.theoremhood, (), ()⟩)
      ((authoredEvenMachine.toRefinement).completed
        (.accepted ⟨.theoremhood, ()⟩)) :=
  ((authoredEvenMachine.toRefinement).completes_iff _ _).2 rfl

/-- Negative: the same submitted request cannot reach `malformed`. -/
theorem authored_even_cannot_be_malformed :
    Not ((authoredEvenMachine.toRefinement).theory.MultiStep
      ((authoredEvenMachine.toRefinement).submit
        ⟨.theoremhood, (), ()⟩)
      ((authoredEvenMachine.toRefinement).completed .malformed)) := by
  intro path
  have impossible :=
    ((authoredEvenMachine.toRefinement).completes_iff _ _).mp path
  cases impossible

private def boolDenotes (state machine : Bool) : Prop :=
  state = machine

/-- Negative: equality under a coarse observation does not recover an
endpoint-denotation witness. -/
theorem constant_observation_does_not_imply_denotation :
    (fun _ : Bool => ()) false = (fun _ : Bool => ()) true /\
      Not (boolDenotes false true) := by
  simp [boolDenotes]

def authoredEndpointDenotation : EndpointDenotation authoredFrontend
    NIKCertifiedCompilation.Canary.buildChecker where
  SourceDenotes := fun state machine =>
    state = .authored /\ machine = authoredEvenMachine.toRefinement
  ArtifactDenotes := fun state machine =>
    state = .artifact /\ machine = authoredEvenMachine.toRefinement
  source_functional := by
    rintro state left right ⟨_, leftEqual⟩ ⟨_, rightEqual⟩
    exact leftEqual.trans rightEqual.symm
  artifact_functional := by
    rintro state left right ⟨_, leftEqual⟩ ⟨_, rightEqual⟩
    exact leftEqual.trans rightEqual.symm
  observeMachine := fun _ => true
  source_observation := by
    rintro state machine ⟨rfl, rfl⟩
    rfl
  artifact_observation := by
    rintro state machine ⟨rfl, rfl⟩
    rfl

/-- A proof-producing compiler whose certificate mode selects exactly the
artifact returned by its normal compile function. -/
private def authoredCompile :
    NIKCertifiedCompilation.Canary.BuildState ->
      NIKCertifiedCompilation.Canary.BuildState
  | _ => .artifact

def authoredBuildCompiler : ProofProducingCompilation
    NIKCertifiedCompilation.Canary.buildChecker where
  compile := authoredCompile
  certificate
    | .authored => NIKCertifiedCompilation.Canary.buildTrace
    | .artifact => .refl NIKCertifiedCompilation.Canary.BuildState.artifact
  accepted
    | .authored => NIKCertifiedCompilation.Canary.buildTrace_accepted
    | .artifact => rfl

def authoredPipeline : AuthoredProofProducingPipeline authoredFrontend
    NIKCertifiedCompilation.Canary.buildChecker where
  denotation := authoredEndpointDenotation
  source := .authored
  compiler := authoredBuildCompiler
  authored := authoredEvenMachine
  artifactMachine := authoredEvenMachine.toRefinement
  sourceDenoted := ⟨rfl, rfl⟩
  artifactDenoted := ⟨rfl, rfl⟩

/-- Positive: the certified artifact is exactly the ordinary compiler output,
and its public behavior agrees with the authored GSLT. -/
theorem authored_pipeline_erasure_and_agreement :
    authoredPipeline.toEndpointCompilation.artifact =
        authoredPipeline.compiler.toRealization.compile ()
          authoredPipeline.source /\
      authoredPipeline.artifactMachine.theory.MultiStep
          (authoredPipeline.artifactMachine.submit
            ⟨.theoremhood, (), ()⟩)
          (authoredPipeline.artifactMachine.completed
            (.accepted ⟨.theoremhood, ()⟩)) := by
  constructor
  · exact authoredPipeline.certified_artifact_is_ordinary_compile
  · simpa [authoredPipeline] using authored_even_accepts

def endpointTruth : EndpointCompilation
    NIKDefaultProfile.Canary.frontend
    NIKCertifiedCompilation.Canary.buildChecker where
  source := .authored
  artifact := .artifact
  sourceMachine := NIKDefaultProfile.Refinement.atomic
    NIKDefaultProfile.Canary.frontend
  artifactMachine := NIKDefaultProfile.Refinement.atomic
    NIKDefaultProfile.Canary.frontend
  observeMachine := fun _ => true
  observesSource := rfl
  observesArtifact := rfl
  compilation :=
    ⟨NIKCertifiedCompilation.Canary.buildTrace,
      NIKCertifiedCompilation.Canary.buildTrace_accepted⟩

def endpointTruthReceipt : endpointTruth.CompletionReceipt
    (.knownTruth true) (.accepted (NIKDefaultProfile.Canary.truthClaim true)) where
  path := (endpointTruth.artifactMachine.completes_iff _ _).2 rfl

/-- Positive: endpoint-only compilation plus execution establishes truth. -/
theorem endpoint_truth_sound :
    endpointTruth.observeMachine endpointTruth.artifactMachine =
        endpointTruth.observeMachine endpointTruth.sourceMachine /\
      NIKDefaultProfile.Canary.family.packedMeaning
        (NIKDefaultProfile.Canary.truthClaim true) :=
  endpointTruth.compilation_and_execution_sound endpointTruthReceipt

/-- Negative: a checked compiler trace cannot turn a rejected request into an
accepting endpoint receipt. -/
theorem endpoint_false_has_no_accepting_receipt :
    Not (Nonempty (endpointTruth.CompletionReceipt
      (.knownTruth false)
      (.accepted (NIKDefaultProfile.Canary.truthClaim false)))) := by
  rintro ⟨receipt⟩
  have accepted :=
    (endpointTruth.artifactMachine.completes_iff _ _).mp receipt.path
  cases accepted

end Canary

end Mettapedia.GSLT.LanguageDef.NIKStagedPipeline
