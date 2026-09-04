import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot
import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition
import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection

/-!
# Official ground resolution through the status-indexed derivation machine

This module joins four independently owned layers for one ground-CNF canary:

1. official TSTP structural admission;
2. the generic status/assumption/fresh-symbol projection;
3. the authored ground-resolution calculus service; and
4. the calculus-neutral derivation-check machine.

The initial vocabulary is derived from admitted input formulae.  It is not a
guest-calculus callback and it is not copied from the expected proof.  Thus an
inference that first uses a symbol must carry exact official `new_symbols`
metadata before the calculus is consulted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.Languages.TPTP.StatusSemantics

abbrev MachineFormula := SemanticNode Formula
abbrev MachineEvidence := OfficialEvidence Unit
abbrev MachineProgram := List
  (Instruction MachineFormula Rule MachineEvidence Provenance Obligation)
abbrev MachineArtifact := Artifact
  MachineFormula Rule MachineEvidence Provenance Obligation

/-! ## Ground-CNF guest projection -/

/-- Ground resolution decodes only its own formula, provenance, rule, local
evidence, and empty-clause obligation.  Official graph structure, status,
assumptions, and introduced symbols remain outside this guest boundary. -/
def guest : GuestProjection Formula Rule Unit Provenance Obligation where
  formula? := fun node =>
    match decodeFormula? node with
    | some formula => .ok formula
    | none => .error .unsupported
  inputProvenance? := fun node _ =>
    match decodeInput? node with
    | some (_, provenance) => .ok provenance
    | none => .error .unsupported
  rule? := fun ruleName _ _ =>
    if ruleName = "resolution" then .ok resolutionKey
    else .error .unsupported
  evidence? := fun ruleName _ _ =>
    if ruleName = "resolution" then .ok ()
    else .error .unsupported
  root? := fun node _ =>
    match rootObligation? node with
    | some obligation => .ok obligation
    | none => .error .unsupported

def projection :
    TargetProjection MachineFormula Rule MachineEvidence Provenance Obligation :=
  TptpOfficialStatusIndexedProjection.projection guest

/-! ## Problem boundary and source-derived initial signature -/

def inputAuthorizedB (problem : ParsedProblem) (provenance : Provenance)
    (formula : MachineFormula) : Bool :=
  decide (provenance ∈ problem.clauses /\
    formula.name = provenance.name /\
    groundInputRole? formula.role = some provenance.role /\
    formula.body = .clause provenance.literals)

def boundary (problem : ParsedProblem) (initialSymbols : Finset PrincipalSymbolId) :
    MachineBoundary Formula Provenance Obligation where
  initialMetadata := { knownSymbols := initialSymbols }
  inputAuthorized := inputAuthorizedB problem
  rootAuthorized := fun _ formula obligation =>
    decide (formula.body = obligation /\ obligation = .clause [])

def services (problem : ParsedProblem) (initialSymbols : Finset PrincipalSymbolId) :=
  machineServices
    Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
    (boundary problem initialSymbols)

/-! ## Continuous semantic invariant -/

/-- Every live formula occurrence is a theorem relative to the admitted input
problem.  Metadata state is threaded separately by the machine and therefore
cannot be used as a proof of formula truth. -/
def RelativeTheorem (problem : ParsedProblem) (formula : MachineFormula) : Prop :=
  TptpOfficialStatusIndexedComposition.RelativeTheorem
    (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
      (Atom := Pattern)) problem.formulas formula

/-- Ground resolution instantiates the common theorem-only composition law.
Input soundness comes from the authenticated problem boundary, while the
accepted-status obligation follows from the calculus's explicit `.thm`
guard. -/
def theoremProfile (problem : ParsedProblem)
    (initialSymbols : Finset PrincipalSymbolId) :
    AllTheoremProfile
      (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
        (Atom := Pattern))
      problem.formulas
      Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
      (boundary problem initialSymbols) where
  meaning_eq := rfl
  input_sound := by
    intro state provenance formula conditions
    have authorized := conditions.2.2.1
    change decide (provenance ∈ problem.clauses /\
      formula.name = provenance.name /\
      groundInputRole? formula.role = some provenance.role /\
      formula.body = .clause provenance.literals) = true at authorized
    have authorized := of_decide_eq_true authorized
    intro valuation problemSatisfied
    rw [authorized.2.2.2]
    apply problemSatisfied
    exact List.mem_map.mpr ⟨provenance, authorized.1, rfl⟩
  accepted_status := by
    intro rule status parents evidence conclusion accepted
    have parts :
        decide (status = .thm) = true /\
          inferAccepted rule parents conclusion = true := by
      simpa [
        Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service,
        Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.calculus,
        Bool.and_eq_true] using accepted
    exact of_decide_eq_true parts.1

/-- The selected empty-clause obligation is exactly the formula whose
relative theoremhood the composition policy established. -/
def objectivePolicy (problem : ParsedProblem)
    (initialSymbols : Finset PrincipalSymbolId) :
    ObjectivePolicy (theoremProfile problem initialSymbols).compositionPolicy where
  Objective := TptpGroundResolutionCheckService.RelativeTheorem problem
  root_sound := by
    intro state formula obligation valid _assumptionsClosed authorized
    simp only [boundary, decide_eq_true_eq] at authorized
    change RelativeTheorem problem formula at valid
    unfold RelativeTheorem
      TptpOfficialStatusIndexedComposition.RelativeTheorem at valid
    unfold TptpGroundResolutionCheckService.RelativeTheorem
    intro valuation problemSatisfied
    rw [← authorized.1]
    exact valid valuation problemSatisfied

/-- The generic derivation-machine invariant instantiated by the
status-indexed ground-resolution service.  The proof consumes the exact
one-record calculus decision retained by `StepSound`; the executable canary
below is not used. -/
def servicesSound (problem : ParsedProblem)
    (initialSymbols : Finset PrincipalSymbolId) :
    SoundServices (services problem initialSymbols) :=
  TptpOfficialStatusIndexedComposition.soundServices
    (theoremProfile problem initialSymbols).compositionPolicy
    (objectivePolicy problem initialSymbols)

structure CompiledGroundRoot where
  problem : ParsedProblem
  initialSymbols : Finset PrincipalSymbolId
  artifact : MachineArtifact

def compileWhole? (admitted : AdmittedDerivation) (rootName : String) :
    Except CompileFailure CompiledGroundRoot := do
  let clauses <-
    match collectProblemClauses? admitted.compiled.nodes with
    | .error failure => .error (.projection failure)
    | .ok clauses => .ok clauses
  let initialSymbols <-
    match collectInputPrincipalSymbols? guest admitted.compiled.nodes with
    | .error failure => .error (.projection failure)
    | .ok symbols => .ok symbols
  let artifact <- TptpOfficialDerivationProgram.compileAdmittedWhole?
    projection admitted rootName
  .ok {
    problem := {
      sourceDigest := admitted.derivation.sourceDigest
      clauses
    }
    initialSymbols
    artifact
  }

/-- Successful status-indexed compilation retains exactly the artifact
produced by the generic calculus-neutral official-DAG compiler. -/
theorem compileWhole?_semantic_exact
    {admitted : AdmittedDerivation} {rootName : String}
    {compiled : CompiledGroundRoot}
    (compiledEq : compileWhole? admitted rootName = .ok compiled) :
    TptpOfficialDerivationProgram.compileAdmittedWhole?
        projection admitted rootName = .ok compiled.artifact := by
  unfold compileWhole? at compiledEq
  generalize clausesEq :
      collectProblemClauses? admitted.compiled.nodes = clausesResult
    at compiledEq
  cases clausesResult with
  | error failure => cases compiledEq
  | ok clauses =>
      generalize symbolsEq :
          collectInputPrincipalSymbols? guest admitted.compiled.nodes =
            symbolsResult
        at compiledEq
      cases symbolsResult with
      | error failure => cases compiledEq
      | ok symbols =>
          generalize semanticEq :
              TptpOfficialDerivationProgram.compileAdmittedWhole?
                projection admitted rootName = semanticResult
            at compiledEq
          cases semanticResult with
          | error failure => cases compiledEq
          | ok artifact =>
              have compiledValueEq :
                  ({
                    problem := {
                      sourceDigest := admitted.derivation.sourceDigest
                      clauses
                    }
                    initialSymbols := symbols
                    artifact
                  } : CompiledGroundRoot) = compiled :=
                Except.ok.inj compiledEq
              have artifactEq : artifact = compiled.artifact :=
                congrArg (fun result : CompiledGroundRoot => result.artifact)
                  compiledValueEq
              exact congrArg
                (fun value : MachineArtifact =>
                  (Except.ok value : Except CompileFailure MachineArtifact))
                artifactEq

/-- Any artifact accepted by this status-indexed machine establishes its root
as a theorem relative to the admitted problem.  This is the semantic result;
it follows from the reusable per-instruction machine invariant, independently
of the closed qualification computation below. -/
theorem acceptedArtifact_relativeTheorem
    (compiled : CompiledGroundRoot)
    (root : RootClaim MachineFormula Obligation)
    (accepted : execute (services compiled.problem compiled.initialSymbols)
      compiled.artifact.program = .halted (.verified root)) :
    TptpGroundResolutionCheckService.RelativeTheorem
      compiled.problem root.obligation :=
  accepted_artifact_sound
    (services compiled.problem compiled.initialSymbols)
    (servicesSound compiled.problem compiled.initialSymbols)
    compiled.artifact root accepted

/-- The same accepted run also yields the calculus-plural structural ledger:
every leaf has exact authorization, every edge retains its own status meaning,
and the selected root has closed assumptions. -/
theorem acceptedArtifact_statusChecked
    (compiled : CompiledGroundRoot)
    (root : RootClaim MachineFormula Obligation)
    (accepted : execute (services compiled.problem compiled.initialSymbols)
      compiled.artifact.program = .halted (.verified root)) :
    StatusCheckedObjective
      Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
      (boundary compiled.problem compiled.initialSymbols) root.obligation :=
  accepted_artifact_sound
    (services compiled.problem compiled.initialSymbols)
    (structuralSoundServices
      Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
      (boundary compiled.problem compiled.initialSymbols))
    compiled.artifact root accepted

/-- An accepted empty-clause root refutes the admitted ground-CNF problem. -/
theorem acceptedEmptyRoot_unsatisfiable
    (compiled : CompiledGroundRoot)
    (root : RootClaim MachineFormula Obligation)
    (accepted : execute (services compiled.problem compiled.initialSymbols)
      compiled.artifact.program = .halted (.verified root))
    (emptyRoot : root.obligation = .clause []) :
    TptpGroundResolutionCheckService.ProblemUnsatisfiable compiled.problem := by
  intro valuation problemSatisfied
  have rootSatisfied :=
    acceptedArtifact_relativeTheorem compiled root accepted valuation problemSatisfied
  rw [emptyRoot] at rootSatisfied
  rcases rootSatisfied with ⟨literal, membership, _⟩
  simp at membership

/-! ## Executable qualification controls -/

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

def pSymbol : PrincipalSymbolId := { kind := .functor, name := "p" }
def qSymbol : PrincipalSymbolId := { kind := .functor, name := "q" }

theorem admitted_input_signature_is_exact :
    collectInputPrincipalSymbols? guest validAdmitted.compiled.nodes =
      .ok ([pSymbol, qSymbol].toFinset) := by
  decide +kernel

theorem valid_compilation_succeeds :
    (compileWhole? validAdmitted "empty").toOption.isSome = true := by
  rfl

theorem compilation_uses_source_derived_signature :
    (compileWhole? validAdmitted "empty").toOption.map
        (fun compiled => compiled.initialSymbols) =
      some ([pSymbol, qSymbol].toFinset) := by
  rfl

def validRoot : RootClaim MachineFormula Obligation := {
  id := 4
  formula := {
    name := "empty"
    role := .plain
    origin := .inferred .thm
    body := .clause []
    principalSymbols := ∅
    openAssumptions := ∅
  }
  obligation := .clause []
}

/-- This closed run is an executable qualification canary only.  Semantic
soundness is established separately from the machine's step invariant; no
later theorem may use this equality as a proof of resolution soundness. -/
def executeCompiled? : Option
    (Config MachineFormula Rule MachineEvidence Provenance Obligation MetadataState) :=
  match compileWhole? validAdmitted "empty" with
  | .ok compiled => some (execute
      (services compiled.problem compiled.initialSymbols)
      compiled.artifact.program)
  | .error _ => none

theorem compiled_stream_executes_exactly :
    executeCompiled? = some (.halted (.verified validRoot)) := by
  decide +kernel

/-- Removing `q` from the admitted problem signature rejects the first input
before any inference service can run.  This makes source-derived vocabulary
load-bearing rather than descriptive metadata. -/
def executeWithMissingInputSymbol? : Option
    (Config MachineFormula Rule MachineEvidence Provenance Obligation MetadataState) :=
  match compileWhole? validAdmitted "empty" with
  | .ok compiled => some (execute
      (services compiled.problem ([pSymbol].toFinset))
      compiled.artifact.program)
  | .error _ => none

theorem missing_input_symbol_fails_closed :
    executeWithMissingInputSymbol? =
      some (.halted (.fault (.inputRejected 0))) := by
  rfl

def undeclaredSymbolNode : AdmittedNode :=
  { inferenceNode with
    source := { inferenceNode.source with
      termView := { inferenceNode.source.termView with
        formula := TptpOfficialGroundResolutionVerifier.Canary.formula
          [TptpOfficialGroundResolutionVerifier.Canary.positive "r"] } } }

/-- Inspect the metadata transition separately from the calculus decision, so
this control cannot pass merely because ground resolution also rejects the
invented conclusion. -/
def undeclaredSymbolMetadataTransition :
    Except ProjectionFailure (Option MetadataState) := do
  let (_, evidence, conclusion) <-
    TptpOfficialStatusIndexedProjection.infer? guest undeclaredSymbolNode
  let normalized <- match normalizeMetadata? evidence.metadata with
    | none => .error .malformed
    | some normalized => .ok normalized
  .ok (metadataTransition?
    { knownSymbols := [pSymbol, qSymbol].toFinset }
    [] conclusion normalized)

theorem undeclared_inference_symbol_fails_before_calculus :
    undeclaredSymbolMetadataTransition = .ok none := by
  decide +kernel

/-- The accepted official fixture is unsatisfiable.  Computation establishes
only that the compiled stream reaches `verified`; the implication from that
machine state to unsatisfiability is the structural theorem above. -/
theorem valid_official_derivation_is_unsatisfiable :
    match compileWhole? validAdmitted "empty" with
    | .ok compiled =>
        TptpGroundResolutionCheckService.ProblemUnsatisfiable compiled.problem
    | .error _ => False := by
  generalize resultEq : compileWhole? validAdmitted "empty" = result
  cases result with
  | error failure =>
      have succeeds := valid_compilation_succeeds
      rw [resultEq] at succeeds
      cases succeeds
  | ok compiled =>
      have acceptedOption := compiled_stream_executes_exactly
      unfold executeCompiled? at acceptedOption
      rw [resultEq] at acceptedOption
      have accepted := Option.some.inj acceptedOption
      exact acceptedEmptyRoot_unsatisfiable compiled validRoot accepted rfl

end Canary

#print axioms Canary.admitted_input_signature_is_exact
#print axioms Canary.compilation_uses_source_derived_signature
#print axioms Canary.compiled_stream_executes_exactly
#print axioms Canary.missing_input_symbol_fails_closed
#print axioms Canary.undeclared_inference_symbol_fails_before_calculus
#print axioms Canary.valid_official_derivation_is_unsatisfiable
#print axioms compileWhole?_semantic_exact
#print axioms servicesSound
#print axioms acceptedArtifact_relativeTheorem
#print axioms acceptedArtifact_statusChecked
#print axioms acceptedEmptyRoot_unsatisfiable

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine
