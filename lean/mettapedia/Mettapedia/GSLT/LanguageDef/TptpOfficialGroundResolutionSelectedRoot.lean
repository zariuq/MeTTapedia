import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier
import Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
import Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

/-!
# Official ground resolution as one selected-root TSTP service

This module is the first calculus consumer of the calculus-neutral official
TSTP program compiler.  Structural admission, parent resolution, root
relevance, and dense instruction construction remain generic.  This adapter
recognizes only ground CNF leaves and `resolution` steps with `status(thm)`;
the separately proved ground-resolution service performs the sole semantic
decision while executing the generated derivation-check program.

Unsupported dialects or rules are incomplete.  Malformed carrier data,
missing or forward parents, irrelevant whole-derivation nodes, and false
resolution steps are rejected.  No proof search occurs here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo
open Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.GroundCNFAuthority

abbrev GroundArtifact :=
  TptpOfficialDerivationProgram.Artifact
    Formula Rule Evidence Provenance Obligation

def unsupported {alpha : Type} : Option alpha → Except ProjectionFailure alpha
  | none => .error .unsupported
  | some value => .ok value

def decodeFormula? (node : AdmittedNode) : Option Formula := do
  if node.source.termView.dialect != .cnf then none else
  let clause <-
    TptpOfficialGroundResolutionVerifier.decodeCnfFormula?
      node.source.termView.formula
  some (.clause clause)

def groundInputRole? : FormulaRole -> Option InputRole
  | .axiom => some .axiom
  | .hypothesis => some .hypothesis
  | .negatedConjecture => some .negatedConjecture
  | _ => none

def decodeInput? (node : AdmittedNode) : Option (Formula × Provenance) := do
  match node.source.origin with
  | .unannotated => pure ()
  | .sourced _ (.external _) _ => pure ()
  | _ => none
  let role <- groundInputRole? (← decodeFormulaRole? node.source.termView.role)
  let formula <- decodeFormula? node
  let clause <- match formula with
    | .clause literals => some literals
    | _ => none
  some (formula, {
    id := node.id
    name := node.source.name
    role
    literals := clause
  })

def decodeInference? (node : AdmittedNode) :
    Option (Rule × Evidence × Formula) := do
  let (rule, usefulInfo) <- match node.source.origin with
    | .sourced _ (.inference rule usefulInfo _) _ => some (rule, usefulInfo)
    | _ => none
  let ruleName <- decodeInferenceRule? rule
  let metadata <- decodeRuleMetadata? ruleName usefulInfo
  if metadata.status != .thm then none else
  -- Plain ground resolution neither opens/discharges assumptions nor
  -- introduces symbols.  Those records are therefore unsupported here, not
  -- ignored.  Richer calculi must consume them through their own validated
  -- projection and stateful service.
  if !metadata.assumptions.isEmpty then none else
  if !metadata.newSymbols.isEmpty then none else
  if !metadata.ruleInfo.isEmpty then none else
  if ruleName != "resolution" then none else
  let conclusion <- decodeFormula? node
  some (TptpGroundResolutionProblemAuthority.resolutionKey, (), conclusion)

def rootObligation? (node : AdmittedNode) : Option Obligation := do
  let formula <- decodeFormula? node
  if formula = .clause [] then some (.clause []) else none

def projection :
    TargetProjection Formula Rule Evidence Provenance Obligation where
  input? := fun node => unsupported (decodeInput? node)
  infer? := fun node => unsupported (decodeInference? node)
  root? := fun node => unsupported (rootObligation? node)

def collectProblemClauses? :
    List AdmittedNode → Except ProjectionFailure (List Provenance)
  | [] => .ok []
  | node :: nodes => do
      let rest <- collectProblemClauses? nodes
      match structuralMode node.source.origin with
      | .infer => .ok rest
      | .input =>
          match decodeInput? node with
          | none => .error .unsupported
          | some (_, provenance) => .ok (provenance :: rest)

structure CompiledGroundRoot where
  problem : ParsedProblem
  artifact : GroundArtifact

def compileWhole? (admitted : AdmittedDerivation) (rootName : String) :
    Except CompileFailure CompiledGroundRoot := do
  let clauses <- match collectProblemClauses? admitted.compiled.nodes with
    | .error failure => .error (.projection failure)
    | .ok clauses => .ok clauses
  let artifact <- TptpOfficialDerivationProgram.compileAdmittedWhole?
    projection admitted rootName
  .ok {
    problem := {
      sourceDigest := admitted.derivation.sourceDigest
      clauses
    }
    artifact
  }

inductive PreparationFailure where
  | admissionRejected
  | unsupported
  | structural (failure : CompileFailure)
  deriving DecidableEq, Repr

structure PreparedGroundRoot where
  admitted : AdmittedDerivation
  compiled : CompiledGroundRoot

def prepare? (source : Pattern) (rootName : String) :
    Except PreparationFailure PreparedGroundRoot :=
  match TptpOfficialDerivationAdmission.admit? source with
  | none => .error .admissionRejected
  | some admitted =>
      match compileWhole? admitted rootName with
      | .ok compiled => .ok { admitted, compiled }
      | .error (.projection .unsupported) => .error .unsupported
      | .error failure => .error (.structural failure)

inductive VerificationOutcome where
  | verified
  | incomplete
  | rejected
  deriving DecidableEq, Repr

structure VerifiedGroundRoot where
  source : Pattern
  rootName : String
  prepared : PreparedGroundRoot
  root : RootClaim Formula Obligation
  accepted :
    execute (services prepared.compiled.problem)
      prepared.compiled.artifact.program = .halted (.verified root)
  emptyRoot : root.obligation = .clause []

inductive VerificationResult where
  | verified (evidence : VerifiedGroundRoot)
  | incomplete
  | rejected

def VerificationResult.outcome : VerificationResult → VerificationOutcome
  | .verified _ => .verified
  | .incomplete => .incomplete
  | .rejected => .rejected

/-- Verify every node in a root's submitted derivation.  This whole-root mode
rejects unrelated nodes; a later public selected-root operation may expose
the omitted-node list explicitly rather than silently claiming to verify it. -/
def verifyRoot (source : Pattern) (rootName : String) : VerificationResult :=
  match prepare? source rootName with
  | .error .unsupported => .incomplete
  | .error _ => .rejected
  | .ok prepared =>
      match acceptedEq : execute (services prepared.compiled.problem)
          prepared.compiled.artifact.program with
      | .halted (.verified root) =>
          if emptyRoot : root.obligation = .clause [] then
            .verified {
              source
              rootName
              prepared
              root
              accepted := acceptedEq
              emptyRoot
            }
          else .rejected
      | _ => .rejected

theorem VerifiedGroundRoot.relativeTheorem (result : VerifiedGroundRoot) :
    RelativeTheorem result.prepared.compiled.problem result.root.obligation := by
  change (services_sound result.prepared.compiled.problem).Objective
    result.root.obligation
  exact accepted_artifact_sound
    (services result.prepared.compiled.problem)
    (services_sound result.prepared.compiled.problem)
    result.prepared.compiled.artifact result.root result.accepted

theorem VerifiedGroundRoot.unsatisfiable (result : VerifiedGroundRoot) :
    ProblemUnsatisfiable result.prepared.compiled.problem := by
  intro valuation allSatisfied
  have emptySatisfied :
      Formula.Satisfies valuation (.clause []) := by
    rw [← result.emptyRoot]
    exact result.relativeTheorem valuation allSatisfied
  rcases emptySatisfied with ⟨literal, membership, _⟩
  simp at membership

/-! ## Adapter controls -/

namespace Canary

def source : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.source

def valid : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.valid

def validDecoded : TptpOfficialDerivationAdmission.DecodedDerivation :=
  (TptpOfficialDerivationAdmission.decodeDerivation? valid).get (by rfl)

theorem valid_decoded_exact :
    TptpOfficialDerivationAdmission.decodeDerivation? valid =
      some validDecoded := by
  rfl

def validCompiled : CompiledDerivation :=
  (TptpOfficialDerivationAdmission.compileDecoded? validDecoded).get (by rfl)

theorem valid_compiled_exact :
    TptpOfficialDerivationAdmission.compileDecoded? validDecoded =
      some validCompiled := by
  rfl

def validAdmitted : AdmittedDerivation := {
  source := valid
  carrierAdmitted :=
    TptpOfficialGroundResolutionVerifier.Canary.valid_is_admitted
  derivation := validDecoded
  decoded := valid_decoded_exact
  compiled := validCompiled
  lowered := valid_compiled_exact
}

theorem valid_admission_exact :
    TptpOfficialDerivationAdmission.admit? valid = some validAdmitted := by
  have admitted :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
        Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] valid
        (.base "TptpSemantic:derivation") = true := by
    simpa [valid] using
      TptpOfficialGroundResolutionVerifier.Canary.valid_is_admitted
  unfold TptpOfficialDerivationAdmission.admit?
  rw [dif_pos admitted]
  rfl

def inferenceRule (name : String) : Pattern :=
  .apply "tptp92-ast:inference-rule:alt-1" [
    TptpOfficialGroundResolutionVerifier.Canary.atomicWord name]

def inferenceSource (ruleName : String) (parentNames : List String) : Pattern :=
  .apply "tptp92-ast:source:alt-1" [
    .apply "tptp92-ast:dag-source:alt-2" [
      .apply "tptp92-ast:inference-record:alt-1" [
        inferenceRule ruleName,
        TptpOfficialGroundResolutionVerifier.Canary.statusThm,
        TptpOfficialGroundResolutionVerifier.Canary.parents parentNames]]]

def noOptionalInfo : Pattern :=
  .apply "tptp92-ast:optional-info:alt-2" []

def leafNode : AdmittedNode := {
  id := 0
  source := {
    termView := {
      occurrence := TptpOfficialGroundResolutionVerifier.Canary.occurrence 0
      dialect := .cnf
      name := TptpOfficialGroundResolutionVerifier.Canary.name "p_or_q"
      role := TptpOfficialGroundResolutionVerifier.Canary.role "axiom"
      formula := TptpOfficialGroundResolutionVerifier.Canary.formula [
        TptpOfficialGroundResolutionVerifier.Canary.positive "p",
        TptpOfficialGroundResolutionVerifier.Canary.positive "q"]
      annotation := .absent
      span := TptpOfficialGroundResolutionVerifier.Canary.span 0
    }
    name := "p_or_q"
    role := "axiom"
    origin := .unannotated
    references := []
  }
  parents := []
  parentNames_exact := rfl
  parents_lt := by simp
}

def inferenceNode : AdmittedNode := {
  id := 2
  source := {
    termView := {
      occurrence := TptpOfficialGroundResolutionVerifier.Canary.occurrence 2
      dialect := .cnf
      name := TptpOfficialGroundResolutionVerifier.Canary.name "q"
      role := TptpOfficialGroundResolutionVerifier.Canary.role "plain"
      formula := TptpOfficialGroundResolutionVerifier.Canary.formula [
        TptpOfficialGroundResolutionVerifier.Canary.positive "q"]
      annotation := .sourced
        (inferenceSource "resolution" ["p_or_q", "not_p"])
        noOptionalInfo
      span := TptpOfficialGroundResolutionVerifier.Canary.span 2
    }
    name := "q"
    role := "plain"
    origin := .sourced
      (inferenceSource "resolution" ["p_or_q", "not_p"])
      (.inference
        (inferenceRule "resolution")
        TptpOfficialGroundResolutionVerifier.Canary.statusThm
        (TptpOfficialGroundResolutionVerifier.Canary.parents ["p_or_q", "not_p"]))
      noOptionalInfo
    references := ["p_or_q", "not_p"]
  }
  parents := [{ name := "p_or_q", id := 0 }, { name := "not_p", id := 1 }]
  parentNames_exact := rfl
  parents_lt := by simp
}

theorem leaf_projection_exact :
    projection.input? leafNode = .ok (
      .clause [
        .positive (TptpOfficialGroundResolutionVerifier.Canary.atom "p"),
        .positive (TptpOfficialGroundResolutionVerifier.Canary.atom "q")],
      { id := 0, name := "p_or_q", role := .axiom,
        literals := [
          .positive (TptpOfficialGroundResolutionVerifier.Canary.atom "p"),
          .positive (TptpOfficialGroundResolutionVerifier.Canary.atom "q")] }) := by
  rfl

theorem assumption_leaf_requires_a_richer_service :
    let changed := { leafNode with
      source := { leafNode.source with
        termView := { leafNode.source.termView with
          role := TptpOfficialRoleSemantics.Canary.role "assumption" }
        role := "assumption" } }
    projection.input? changed = .error .unsupported := by
  rfl

theorem unsupported_rule_is_incomplete_at_projection :
    let changed := { inferenceNode with
      source := { inferenceNode.source with
        origin := .sourced (.apply "source" [])
          (.inference
            (inferenceRule "magic")
            TptpOfficialGroundResolutionVerifier.Canary.statusThm
            (TptpOfficialGroundResolutionVerifier.Canary.parents
              ["p_or_q", "not_p"]))
          (.apply "optional" []) } }
    projection.infer? changed = .error .unsupported := by
  rfl

theorem assumptions_are_not_silently_ignored :
    let changed := { inferenceNode with
      source := { inferenceNode.source with
        origin := .sourced (.apply "source" [])
          (.inference
            (inferenceRule "resolution")
            TptpOfficialUsefulInfo.Canary.assumptionsAndSymbols
            (TptpOfficialGroundResolutionVerifier.Canary.parents
              ["p_or_q", "not_p"]))
          (.apply "optional" []) } }
    projection.infer? changed = .error .unsupported := by
  rfl

theorem malformed_assumption_metadata_is_not_downgraded :
    let changed := { inferenceNode with
      source := { inferenceNode.source with
        origin := .sourced (.apply "source" [])
          (.inference
            (inferenceRule "resolution")
            TptpOfficialUsefulInfo.Canary.malformedAssumptions
            (TptpOfficialGroundResolutionVerifier.Canary.parents
              ["p_or_q", "not_p"]))
          (.apply "optional" []) } }
    projection.infer? changed = .error .unsupported := by
  rfl

theorem unknown_status_is_not_erased_beside_thm :
    let changed := { inferenceNode with
      source := { inferenceNode.source with
        origin := .sourced (.apply "source" [])
          (.inference
            (inferenceRule "resolution")
            TptpOfficialUsefulInfo.Canary.validThenUnknownStatus
            (TptpOfficialGroundResolutionVerifier.Canary.parents
              ["p_or_q", "not_p"]))
          (.apply "optional" []) } }
    projection.infer? changed = .error .unsupported := by
  rfl

def resolutionRuleDetails : Pattern :=
  TptpOfficialUsefulInfo.Canary.usefulInfo [
    TptpOfficialUsefulInfo.Canary.functionTerm "status"
      [TptpOfficialUsefulInfo.Canary.atomicTerm "thm"],
    TptpOfficialUsefulInfo.Canary.functionTerm "resolution" [
      TptpOfficialUsefulInfo.Canary.atomicTerm "pivot",
      TptpOfficialUsefulInfo.Canary.listTerm [
        TptpOfficialUsefulInfo.Canary.atomicTerm "p"]]]

theorem rule_specific_information_is_not_silently_ignored :
    let changed := { inferenceNode with
      source := { inferenceNode.source with
        origin := .sourced (.apply "source" [])
          (.inference
            (inferenceRule "resolution") resolutionRuleDetails
            (TptpOfficialGroundResolutionVerifier.Canary.parents
              ["p_or_q", "not_p"]))
          (.apply "optional" []) } }
    projection.infer? changed = .error .unsupported := by
  rfl

def p : Pattern := TptpOfficialGroundResolutionVerifier.Canary.atom "p"
def q : Pattern := TptpOfficialGroundResolutionVerifier.Canary.atom "q"

def firstClause : Provenance := {
  id := 0
  name := "p_or_q"
  role := .axiom
  literals := [.positive p, .positive q]
}

def secondClause : Provenance := {
  id := 1
  name := "not_p"
  role := .axiom
  literals := [.negative p]
}

def thirdClause : Provenance := {
  id := 2
  name := "not_q"
  role := .axiom
  literals := [.negative q]
}

def problem : ParsedProblem := {
  sourceDigest := "fixture"
  clauses := [firstClause, secondClause, thirdClause]
}

theorem mismatched_input_rejected :
    (services problem).input () firstClause (.clause secondClause.literals) =
      none := by
  decide +kernel

theorem first_input_accepted :
    (services problem).input () firstClause (.clause firstClause.literals) =
      some () := by
  decide +kernel

theorem second_input_accepted :
    (services problem).input () secondClause (.clause secondClause.literals) =
      some () := by
  decide +kernel

theorem third_input_accepted :
    (services problem).input () thirdClause (.clause thirdClause.literals) =
      some () := by
  decide +kernel

theorem wrong_root_obligation_rejected :
    (services problem).root () (.clause [.positive q]) (.clause []) = false := by
  decide +kernel

theorem correct_root_obligation_accepted :
    (services problem).root () (.clause []) (.clause []) = true := by
  rfl

theorem first_inference_accepted :
    inferAccepted TptpGroundResolutionProblemAuthority.resolutionKey
      [.clause firstClause.literals, .clause secondClause.literals]
      (.clause [.positive q]) = true := by
  have pValid : argumentValidAt 0 p = true := by decide +kernel
  have qValid : argumentValidAt 0 q = true := by decide +kernel
  simpa [inferAccepted, firstClause, secondClause] using
    synthesize_binary_positive_left p q pValid qValid

theorem second_inference_accepted :
    inferAccepted TptpGroundResolutionProblemAuthority.resolutionKey
      [.clause [.positive q], .clause thirdClause.literals]
      (.clause []) = true := by
  have qValid : argumentValidAt 0 q = true := by decide +kernel
  simpa [inferAccepted, thirdClause] using
    synthesize_binary_singletons q qValid

def validProgram : TptpGroundResolutionCheckService.Program := [
  .input 0 (.clause firstClause.literals) firstClause
    { distance := 2, towardRoot := some 3 },
  .input 1 (.clause secondClause.literals) secondClause
    { distance := 2, towardRoot := some 3 },
  .input 2 (.clause thirdClause.literals) thirdClause
    { distance := 1, towardRoot := some 4 },
  .infer 3 TptpGroundResolutionProblemAuthority.resolutionKey [0, 1] ()
    (.clause [.positive q]) { distance := 1, towardRoot := some 4 },
  .infer 4 TptpGroundResolutionProblemAuthority.resolutionKey [3, 2] ()
    (.clause []) { distance := 0, towardRoot := none },
  .root 4 (.clause []),
  .finish]

def validRoot : RootClaim Formula Obligation := {
  id := 4
  formula := .clause []
  obligation := .clause []
}

def validPrefixNodes : List (DerivationCheckMachine.Node Formula) := [
  { id := 4, formula := .clause [],
    relevance := { distance := 0, towardRoot := none }, linked := false },
  { id := 3, formula := .clause [.positive q],
    relevance := { distance := 1, towardRoot := some 4 }, linked := true },
  { id := 2, formula := .clause thirdClause.literals,
    relevance := { distance := 1, towardRoot := some 4 }, linked := true },
  { id := 1, formula := .clause secondClause.literals,
    relevance := { distance := 2, towardRoot := some 3 }, linked := true },
  { id := 0, formula := .clause firstClause.literals,
    relevance := { distance := 2, towardRoot := some 3 }, linked := true }
]

def validPrefixState : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := [.finish]
  nodes := validPrefixNodes
  nextId := 5
  root? := some validRoot
  serviceState := ()
}

theorem valid_prefix_exact :
    runFuel (services problem) 6 (initial (services problem) validProgram) =
      .running validPrefixState := by
  decide +kernel

theorem valid_program_verified :
    execute (services problem) validProgram =
      .halted (.verified validRoot) := by
  decide +kernel

def validGround : CompiledGroundRoot := {
  problem := problem
  artifact := {
    rootName := "empty"
    rootOldId := 4
    rootId := 4
    selectedNames := ["p_or_q", "not_p", "not_q", "q", "empty"]
    omittedNames := []
    program := validProgram
  }
}

theorem valid_compilation_exact :
    compileWhole? validAdmitted "empty" = .ok validGround := by
  rfl

def validPrepared : PreparedGroundRoot := {
  admitted := validAdmitted
  compiled := validGround
}

theorem valid_preparation_exact :
    prepare? valid "empty" = .ok validPrepared := by
  simp [prepare?, valid_admission_exact, valid_compilation_exact,
    validPrepared]

def validEvidence : VerifiedGroundRoot := {
  source := valid
  rootName := "empty"
  prepared := validPrepared
  root := validRoot
  accepted := valid_program_verified
  emptyRoot := rfl
}

theorem valid_official_derivation_verifies_in_one_pass :
    verifyRoot valid "empty" = .verified validEvidence := by
  unfold verifyRoot
  simp only [valid_preparation_exact]
  split
  · rename_i root accepted
    have rootShape :
        root = validRoot := by
      have comparison := accepted.symm.trans
        valid_program_verified
      cases comparison
      rfl
    subst root
    split
    · rfl
    · rename_i notEmpty
      exact (notEmpty rfl).elim
  · rename_i notVerified
    exact (notVerified
      validRoot valid_program_verified).elim

theorem valid_official_derivation_is_unsatisfiable :
    ProblemUnsatisfiable validEvidence.prepared.compiled.problem :=
  validEvidence.unsatisfiable

def unknownRule : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith "unknown"

theorem unknown_rule_is_admitted :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] unknownRule
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_sound
      (by decide +kernel)
  · decide +kernel

def unknownDecoded : TptpOfficialDerivationAdmission.DecodedDerivation :=
  (TptpOfficialDerivationAdmission.decodeDerivation? unknownRule).get (by rfl)

def unknownCompiled : CompiledDerivation :=
  (TptpOfficialDerivationAdmission.compileDecoded? unknownDecoded).get (by rfl)

def unknownAdmitted : AdmittedDerivation := {
  source := unknownRule
  carrierAdmitted :=
    unknown_rule_is_admitted
  derivation := unknownDecoded
  decoded := by rfl
  compiled := unknownCompiled
  lowered := by rfl
}

theorem unknown_admission_exact :
    TptpOfficialDerivationAdmission.admit? unknownRule = some unknownAdmitted := by
  have admitted :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
        Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] unknownRule
        (.base "TptpSemantic:derivation") = true := by
    simpa [unknownRule] using unknown_rule_is_admitted
  unfold TptpOfficialDerivationAdmission.admit?
  rw [dif_pos admitted]
  rfl

theorem unknown_compilation_is_unsupported :
    compileWhole? unknownAdmitted "empty" =
      .error (.projection .unsupported) := by
  rfl

theorem unknown_rule_is_incomplete :
    (verifyRoot unknownRule "empty").outcome = .incomplete := by
  simp [verifyRoot, prepare?, unknown_admission_exact,
    unknown_compilation_is_unsupported, VerificationResult.outcome]

def missingParent : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith
    "resolution" ["missing", "not_p"]

theorem missing_parent_is_admitted :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] missingParent
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_sound
      (by decide +kernel)
  · decide +kernel

def missingParentDecoded :
    TptpOfficialDerivationAdmission.DecodedDerivation :=
  (TptpOfficialDerivationAdmission.decodeDerivation? missingParent).get (by rfl)

theorem missing_parent_structural_compilation_fails :
    TptpOfficialDerivationAdmission.compileDecoded? missingParentDecoded = none := by
  rfl

theorem missing_parent_admission_rejected :
    TptpOfficialDerivationAdmission.admit? missingParent = none := by
  have admitted :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
        Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] missingParent
        (.base "TptpSemantic:derivation") = true := by
    simpa [missingParent] using missing_parent_is_admitted
  unfold TptpOfficialDerivationAdmission.admit?
  rw [dif_pos admitted]
  rfl

theorem missing_parent_is_rejected :
    (verifyRoot missingParent "empty").outcome = .rejected := by
  simp [verifyRoot, prepare?, missing_parent_admission_rejected,
    VerificationResult.outcome]

def inventedResult : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith
    "resolution" ["p_or_q", "not_p"]
    (TptpOfficialGroundResolutionVerifier.Canary.formula
      [TptpOfficialGroundResolutionVerifier.Canary.positive "p"])

theorem invented_result_is_admitted :
    Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] inventedResult
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_sound
      (by decide +kernel)
  · decide +kernel

def inventedDecoded : TptpOfficialDerivationAdmission.DecodedDerivation :=
  (TptpOfficialDerivationAdmission.decodeDerivation? inventedResult).get (by rfl)

def inventedCompiled : CompiledDerivation :=
  (TptpOfficialDerivationAdmission.compileDecoded? inventedDecoded).get (by rfl)

def inventedAdmitted : AdmittedDerivation := {
  source := inventedResult
  carrierAdmitted :=
    invented_result_is_admitted
  derivation := inventedDecoded
  decoded := by rfl
  compiled := inventedCompiled
  lowered := by rfl
}

theorem invented_admission_exact :
    TptpOfficialDerivationAdmission.admit? inventedResult =
      some inventedAdmitted := by
  have admitted :
      Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
        Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty [] inventedResult
        (.base "TptpSemantic:derivation") = true := by
    simpa [inventedResult] using invented_result_is_admitted
  unfold TptpOfficialDerivationAdmission.admit?
  rw [dif_pos admitted]
  rfl

def inventedProgram : TptpGroundResolutionCheckService.Program := [
  .input 0 (.clause firstClause.literals) firstClause
    { distance := 2, towardRoot := some 3 },
  .input 1 (.clause secondClause.literals) secondClause
    { distance := 2, towardRoot := some 3 },
  .input 2 (.clause thirdClause.literals) thirdClause
    { distance := 1, towardRoot := some 4 },
  .infer 3 TptpGroundResolutionProblemAuthority.resolutionKey [0, 1] ()
    (.clause [.positive p]) { distance := 1, towardRoot := some 4 },
  .infer 4 TptpGroundResolutionProblemAuthority.resolutionKey [3, 2] ()
    (.clause []) { distance := 0, towardRoot := none },
  .root 4 (.clause []),
  .finish]

theorem invented_program_rejected :
    execute (services problem) inventedProgram =
      .halted (.fault (.ruleRejected 3)) := by
  decide +kernel

def inventedGround : CompiledGroundRoot := {
  problem := problem
  artifact := {
    rootName := "empty"
    rootOldId := 4
    rootId := 4
    selectedNames := ["p_or_q", "not_p", "not_q", "q", "empty"]
    omittedNames := []
    program := inventedProgram
  }
}

theorem invented_compilation_exact :
    compileWhole? inventedAdmitted "empty" = .ok inventedGround := by
  rfl

def inventedPrepared : PreparedGroundRoot := {
  admitted := inventedAdmitted
  compiled := inventedGround
}

theorem invented_preparation_exact :
    prepare? inventedResult "empty" = .ok inventedPrepared := by
  simp [prepare?, invented_admission_exact, invented_compilation_exact,
    inventedPrepared]

theorem invented_result_is_rejected :
    (verifyRoot inventedResult "empty").outcome = .rejected := by
  unfold verifyRoot
  simp only [invented_preparation_exact]
  split
  · rename_i root accepted
    have impossible := accepted.symm.trans
      invented_program_rejected
    cases impossible
  · rfl

end Canary

#print axioms VerifiedGroundRoot.relativeTheorem
#print axioms VerifiedGroundRoot.unsatisfiable
#print axioms Canary.leaf_projection_exact
#print axioms Canary.assumption_leaf_requires_a_richer_service
#print axioms Canary.unsupported_rule_is_incomplete_at_projection
#print axioms Canary.assumptions_are_not_silently_ignored
#print axioms Canary.malformed_assumption_metadata_is_not_downgraded
#print axioms Canary.unknown_status_is_not_erased_beside_thm
#print axioms Canary.rule_specific_information_is_not_silently_ignored
#print axioms Canary.mismatched_input_rejected
#print axioms Canary.first_input_accepted
#print axioms Canary.second_input_accepted
#print axioms Canary.third_input_accepted
#print axioms Canary.wrong_root_obligation_rejected
#print axioms Canary.correct_root_obligation_accepted
#print axioms Canary.first_inference_accepted
#print axioms Canary.second_inference_accepted
#print axioms Canary.valid_prefix_exact
#print axioms Canary.valid_program_verified
#print axioms Canary.valid_decoded_exact
#print axioms Canary.valid_compiled_exact
#print axioms Canary.valid_admission_exact
#print axioms Canary.valid_compilation_exact
#print axioms Canary.valid_preparation_exact
#print axioms Canary.valid_official_derivation_verifies_in_one_pass
#print axioms Canary.valid_official_derivation_is_unsatisfiable
#print axioms Canary.unknown_admission_exact
#print axioms Canary.unknown_compilation_is_unsupported
#print axioms Canary.unknown_rule_is_incomplete
#print axioms Canary.missing_parent_structural_compilation_fails
#print axioms Canary.missing_parent_admission_rejected
#print axioms Canary.missing_parent_is_rejected
#print axioms Canary.invented_admission_exact
#print axioms Canary.invented_compilation_exact
#print axioms Canary.invented_preparation_exact
#print axioms Canary.invented_result_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot
