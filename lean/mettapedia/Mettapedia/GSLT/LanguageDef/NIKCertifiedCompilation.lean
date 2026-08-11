import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.GSLT.LanguageDef.NIKGSLT

/-!
# Certified compilation and execution of NIK machines

The NIK checker is itself a GSLT, but reification is not self-certification.
Bootstrapping therefore has two independent evidence channels:

1. an accepted compiler-state trace preserving a named machine observation;
2. an execution receipt in a compiled machine that exactly refines an admitted
   checker.

Only the second channel, combined with checker soundness, authorizes guest
meaning.  The first channel proves that the artifact came through the admitted
compilation boundary.  Their conjunction is the non-circular source-to-result
contract needed by a staged NIK implementation.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation

open Mettapedia.GSLT
open Mettapedia.GSLT.CompilationTraceChecker
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKGSLT

universe uClaim uCertificate uState uObservation uMachine uKind

/-! ## The certified machine boundary -/

/-- An independently checked compilation path whose every compiler state has
a semantic NIK-machine interpretation.  `observesMachine` is the binding
between serialized/compiler state and the machine-level observation; without
it the compilation trace and the executed artifact would be unrelated facts.
-/
structure CertifiedMachineCompilation
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) where
  source : State
  artifact : State
  machineAt : State -> Refinement.Machine.{uClaim, uCertificate, uMachine} checker
  observeMachine : Refinement.Machine.{uClaim, uCertificate, uMachine} checker ->
    Observation
  observesMachine : forall state,
    compilerChecker.observe state = observeMachine (machineAt state)
  compilation : AcceptedTrace compilerChecker source artifact

namespace CertifiedMachineCompilation

variable {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (compiled : CertifiedMachineCompilation.{uClaim, uCertificate, uState,
      uObservation, uMachine} checker compilerChecker)

/-- Bind an ordinary proof-producing compiler to semantic NIK machines at
each compiler state.  This is the direct adapter for a build mode that emits
the same artifact as its normal compiler plus an independently replayed
sidecar certificate. -/
def ofProofProducingCompilation
    (compiler : ProofProducingCompilation compilerChecker)
    (source : State)
    (machineAt : State ->
      Refinement.Machine.{uClaim, uCertificate, uMachine} checker)
    (observeMachine :
      Refinement.Machine.{uClaim, uCertificate, uMachine} checker ->
        Observation)
    (observesMachine : forall state,
      compilerChecker.observe state = observeMachine (machineAt state)) :
    CertifiedMachineCompilation checker compilerChecker where
  source := source
  artifact := compiler.compile source
  machineAt := machineAt
  observeMachine := observeMachine
  observesMachine := observesMachine
  compilation :=
    ⟨compiler.certificate source, compiler.accepted source⟩

@[simp] theorem ofProofProducingCompilation_artifact
    (compiler : ProofProducingCompilation compilerChecker)
    (source : State)
    (machineAt : State ->
      Refinement.Machine.{uClaim, uCertificate, uMachine} checker)
    (observeMachine :
      Refinement.Machine.{uClaim, uCertificate, uMachine} checker ->
        Observation)
    (observesMachine : forall state,
      compilerChecker.observe state = observeMachine (machineAt state)) :
    (ofProofProducingCompilation compiler source machineAt observeMachine
      observesMachine).artifact = compiler.compile source :=
  rfl

/-- The exact multi-stage NIK machine denoted by the compiled artifact. -/
abbrev artifactMachine : Refinement.Machine checker :=
  compiled.machineAt compiled.artifact

/-- Independent compiler replay preserves the explicitly selected
machine-level observation from authored source to artifact. -/
theorem machineObservation_preserved :
    compiled.observeMachine compiled.artifactMachine =
      compiled.observeMachine (compiled.machineAt compiled.source) := by
  rw [<- compiled.observesMachine compiled.artifact,
    <- compiled.observesMachine compiled.source]
  exact compiled.compilation.observation_preserved

/-- A runtime receipt is a concrete accepting path in the compiled machine.
It is intentionally distinct from the compilation certificate. -/
structure AcceptanceReceipt (claim : Claim) (certificate : Certificate) where
  path : compiled.artifactMachine.theory.MultiStep
    (compiled.artifactMachine.submit claim certificate)
    (compiled.artifactMachine.accepted claim)

/-- A separately admitted checker-soundness theorem turns an artifact
execution receipt into guest meaning.  Compiler certification alone is not an
argument to this theorem. -/
theorem acceptance_implies_meaning {Meaning : Claim -> Prop}
    (sound : checker.Sound Meaning)
    {claim : Claim} {certificate : Certificate}
    (receipt : compiled.AcceptanceReceipt claim certificate) :
    Meaning claim :=
  Refinement.acceptance_sound compiled.artifactMachine sound receipt.path

/-- The compositional source-to-result theorem: compiler replay preserves the
named machine observation, while runtime replay establishes the guest claim.
-/
theorem compilation_and_execution_sound {Meaning : Claim -> Prop}
    (sound : checker.Sound Meaning)
    {claim : Claim} {certificate : Certificate}
    (receipt : compiled.AcceptanceReceipt claim certificate) :
    compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) /\
      Meaning claim :=
  ⟨compiled.machineObservation_preserved,
    compiled.acceptance_implies_meaning sound receipt⟩

/-- With exact checker authority, the compiled NIK machine has a two-sided
end-to-end characterization.  The compilation observation remains in the
statement, so certificate-existence cannot silently discard artifact
identity. -/
theorem authority_correspondence {Meaning : Claim -> Prop}
    (authority : checker.Authority Meaning) (claim : Claim) :
    Meaning claim <->
      compiled.observeMachine compiled.artifactMachine =
          compiled.observeMachine (compiled.machineAt compiled.source) /\
        Exists fun certificate : Certificate =>
          Nonempty (compiled.AcceptanceReceipt claim certificate) := by
  constructor
  · intro meaningful
    obtain ⟨certificate, path⟩ :=
      Refinement.meaningful_has_accepting_execution compiled.artifactMachine
        authority.complete claim meaningful
    exact ⟨compiled.machineObservation_preserved, certificate, ⟨⟨path⟩⟩⟩
  · rintro ⟨_, certificate, ⟨receipt⟩⟩
    exact compiled.acceptance_implies_meaning authority.sound receipt

end CertifiedMachineCompilation

/-! ## Dependent NIK authority families -/

/-- Certified compilation of the packed fail-closed dispatcher for a
dependent authority family. -/
abbrev CertifiedFamilyCompilation
    {Kind : Type uKind} (family : AuthorityFamily Kind) [DecidableEq Kind]
    {State : Type uState} {Observation : Type uObservation}
    (compilerChecker : CompilationTraceChecker State Observation) :=
  CertifiedMachineCompilation family.packedChecker compilerChecker

/-- Any accepting receipt from a compiled family machine projects through
the selected authority's exact certificate scope into guest meaning. -/
theorem family_compilation_and_execution_sound
    {Kind : Type uKind} (family : AuthorityFamily Kind) [DecidableEq Kind]
    {State : Type uState} {Observation : Type uObservation}
    {compilerChecker : CompilationTraceChecker State Observation}
    (compiled : CertifiedFamilyCompilation family compilerChecker)
    {claim : family.PackedClaim}
    {certificate : family.PackedCertificate}
    (receipt : compiled.AcceptanceReceipt claim certificate) :
    compiled.observeMachine compiled.artifactMachine =
        compiled.observeMachine (compiled.machineAt compiled.source) /\
      family.packedMeaning claim :=
  compiled.compilation_and_execution_sound
    family.packedAuthorityProjection.sound receipt

/-! ## Positive and negative bootstrapping canaries -/

namespace Canary

inductive BuildState where
  | authored
  | artifact
deriving DecidableEq

inductive BuildEvidence where
  | lower
deriving DecidableEq

/-- A minimal compiler checker with one admitted source-to-artifact edge. -/
def buildChecker : CompilationTraceChecker BuildState Bool where
  Evidence := fun _ _ => BuildEvidence
  check
    | .authored, .artifact, .lower => true
    | _, _, _ => false
  observe := fun _ => true
  sound := by
    intro source target evidence accepted
    cases source <;> cases target <;> cases evidence <;> rfl

def buildTrace : buildChecker.Trace BuildState.authored BuildState.artifact :=
  Trace.step (checker := buildChecker)
    (source := BuildState.authored) (middle := BuildState.artifact)
    BuildEvidence.lower (Trace.refl BuildState.artifact)

theorem buildTrace_accepted : buildTrace.check = true := by
  rfl

def truthChecker : Checker Bool Unit where
  check claim _ := claim

def TruthMeaning (claim : Bool) : Prop := claim = true

theorem truthChecker_sound : truthChecker.Sound TruthMeaning := by
  intro claim certificate accepted
  exact accepted

def truthCompilation :
    CertifiedMachineCompilation truthChecker buildChecker where
  source := .authored
  artifact := .artifact
  machineAt := fun _ => Refinement.atomic truthChecker
  observeMachine := fun _ => true
  observesMachine := by intro state; cases state <;> rfl
  compilation := ⟨buildTrace, buildTrace_accepted⟩

def truthReceipt : truthCompilation.AcceptanceReceipt true () where
  path := (Refinement.atomic truthChecker).accepts_iff true () |>.mpr rfl

/-- Positive: accepted compilation and accepted runtime replay jointly retain
artifact identity and prove the independently stated meaning. -/
theorem truth_end_to_end :
    truthCompilation.observeMachine truthCompilation.artifactMachine =
        truthCompilation.observeMachine
          (truthCompilation.machineAt truthCompilation.source) /\
      TruthMeaning true :=
  truthCompilation.compilation_and_execution_sound
    truthChecker_sound truthReceipt

def unsoundCompilation :
    CertifiedMachineCompilation NIKGSLT.Canary.unsoundChecker buildChecker where
  source := .authored
  artifact := .artifact
  machineAt := fun _ => Refinement.atomic NIKGSLT.Canary.unsoundChecker
  observeMachine := fun _ => true
  observesMachine := by intro state; cases state <;> rfl
  compilation := ⟨buildTrace, buildTrace_accepted⟩

def unsoundReceipt : unsoundCompilation.AcceptanceReceipt () () where
  path := NIKGSLT.Canary.unsoundMachine_accepts

/-- Negative: a valid compilation certificate and a reachable `accepted`
state do not manufacture semantic authority for an unsound checker.  The
missing premise is exactly the independently proved checker-soundness law. -/
theorem compilation_is_not_self_certification :
    unsoundCompilation.observeMachine unsoundCompilation.artifactMachine =
        unsoundCompilation.observeMachine
          (unsoundCompilation.machineAt unsoundCompilation.source) /\
      Nonempty (unsoundCompilation.AcceptanceReceipt () ()) /\
      Not (NIKGSLT.Canary.FalseMeaning ()) :=
  ⟨unsoundCompilation.machineObservation_preserved,
    ⟨unsoundReceipt⟩, id⟩

end Canary

end Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation
