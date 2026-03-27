import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import MeTTailCore.MeTTaIL.EffectSafety
import MeTTailCore.Crypto.SHA256

/-!
# MeTTa Search Policy Contract

Shared contract surface for search-policy metadata in the MeTTa family.

This artifact is deliberately separate from:
- runtime semantics (`RuntimeSpec`)
- operator execution ownership (`ExecutionContract`)
- local binder scope (`ScopeContract`)

Positive example:
- an ATP-facing saturation policy may use TPTP/TFF as an interchange format.

Negative example:
- this file does not redefine MeTTa semantics, and it does not require every
  oracle to use TPTP. SMT-oriented solver oracles can use SMT-LIB2 instead.
-/

namespace Mettapedia.Languages.MeTTa.SearchPolicyContract

open Mettapedia.Languages.MeTTa.ElaboratedCore
open MeTTailCore.MeTTaIL.EffectSafety

/-- Coarse search-kernel families. -/
inductive SearchKernelKind where
  | recursiveProof
  | frontierEnumeration
  | saturationATP
  | solverOracle
deriving Repr, DecidableEq, BEq

/-- How the active search frontier is scheduled. -/
inductive FrontierPolicy where
  | depthBounded
  | breadthFair
  | bestFirst
  | givenClause
deriving Repr, DecidableEq, BEq

/-- Ranking signals available to a policy. -/
inductive RankingSignal where
  | proofDepth
  | clauseWeight
  | clauseAge
  | symbolPrior
  | goalDistance
  | premiseScore
  | modelScore
deriving Repr, DecidableEq, BEq

/-- Result-order control exposed to surface consumers. -/
inductive EmissionOrder where
  | native
  | reverse
  | lex
  | shortLex
deriving Repr, DecidableEq, BEq

/-- External interchange surfaces for search/oracle collaboration. -/
inductive InterchangeSurface where
  | none
  | tptpFOF
  | tptpTFF
  | smtlib2
deriving Repr, DecidableEq, BEq

/-- What kind of artifact a search/oracle policy is trusted to return. -/
inductive SearchResultKind where
  | witnessTerm
  | answerBindings
  | proofObject
  | unsatCore
deriving Repr, DecidableEq, BEq

/-- Contract entry for one search-policy lane. -/
structure SearchPolicyEntry where
  name : String
  kernelClass : RuntimeKernelClass
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  searchKind : SearchKernelKind
  frontier : FrontierPolicy
  rankingSignals : List RankingSignal := []
  interchange : InterchangeSurface := .none
  resultKind : SearchResultKind
  defaultOrder : EmissionOrder := .native
  supportsReverseOrder : Bool := false
  supportsLexOrder : Bool := false
  supportsShortLexOrder : Bool := false
  bounded : Bool := true
  fair : Bool := true
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Exportable artifact for search-policy metadata. -/
structure SearchPolicyArtifact where
  schemaVersion : Nat := 1
  dialect : String
  entries : List SearchPolicyEntry
deriving Repr, DecidableEq, BEq

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonNat (n : Nat) : String :=
  toString n

private def renderKernelClass : RuntimeKernelClass → String
  | .ruleExec => "rule_exec"
  | .query => "query"
  | .spaceEffect => "space_effect"
  | .oracle => "oracle"
  | .metaPhase => "meta_phase"

private def renderResourceClass : RuntimeResourceClass → String
  | .defaultAtomSpace => "default_atomspace"
  | .namedAtomSpace => "named_atomspace"
  | .mapResource => "map_resource"
  | .queueResource => "queue_resource"
  | .solverResource => "solver_resource"
  | .externalResource => "external_resource"

private def renderEffectClass : EffectClass → String
  | .pureStructural => "pure_structural"
  | .readOnlyLookup => "read_only_lookup"
  | .nondeterministicReadOnly => "nondeterministic_read_only"
  | .writesState => "writes_state"
  | .oracleIO => "oracle_io"

private def renderSearchKernelKind : SearchKernelKind → String
  | .recursiveProof => "recursive_proof"
  | .frontierEnumeration => "frontier_enumeration"
  | .saturationATP => "saturation_atp"
  | .solverOracle => "solver_oracle"

private def renderFrontierPolicy : FrontierPolicy → String
  | .depthBounded => "depth_bounded"
  | .breadthFair => "breadth_fair"
  | .bestFirst => "best_first"
  | .givenClause => "given_clause"

private def renderRankingSignal : RankingSignal → String
  | .proofDepth => "proof_depth"
  | .clauseWeight => "clause_weight"
  | .clauseAge => "clause_age"
  | .symbolPrior => "symbol_prior"
  | .goalDistance => "goal_distance"
  | .premiseScore => "premise_score"
  | .modelScore => "model_score"

private def renderInterchangeSurface : InterchangeSurface → String
  | .none => "none"
  | .tptpFOF => "tptp_fof"
  | .tptpTFF => "tptp_tff"
  | .smtlib2 => "smtlib2"

private def renderSearchResultKind : SearchResultKind → String
  | .witnessTerm => "witness_term"
  | .answerBindings => "answer_bindings"
  | .proofObject => "proof_object"
  | .unsatCore => "unsat_core"

private def renderEmissionOrder : EmissionOrder → String
  | .native => "native"
  | .reverse => "reverse"
  | .lex => "lex"
  | .shortLex => "shortlex"

private def jsonStrList (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

private def renderEntry (e : SearchPolicyEntry) : String :=
  "{"
    ++ "\"name\":" ++ jsonStr e.name ++ ","
    ++ "\"kernel_class\":" ++ jsonStr (renderKernelClass e.kernelClass) ++ ","
    ++ "\"effect_class\":" ++ jsonStr (renderEffectClass e.effectClass) ++ ","
    ++ "\"resource_class\":" ++ jsonStr (renderResourceClass e.resourceClass) ++ ","
    ++ "\"search_kind\":" ++ jsonStr (renderSearchKernelKind e.searchKind) ++ ","
    ++ "\"frontier\":" ++ jsonStr (renderFrontierPolicy e.frontier) ++ ","
    ++ "\"ranking_signals\":"
        ++ jsonStrList (e.rankingSignals.map renderRankingSignal) ++ ","
    ++ "\"interchange\":" ++ jsonStr (renderInterchangeSurface e.interchange) ++ ","
    ++ "\"result_kind\":" ++ jsonStr (renderSearchResultKind e.resultKind) ++ ","
    ++ "\"default_order\":" ++ jsonStr (renderEmissionOrder e.defaultOrder) ++ ","
    ++ "\"supports_reverse_order\":" ++ jsonBool e.supportsReverseOrder ++ ","
    ++ "\"supports_lex_order\":" ++ jsonBool e.supportsLexOrder ++ ","
    ++ "\"supports_shortlex_order\":" ++ jsonBool e.supportsShortLexOrder ++ ","
    ++ "\"bounded\":" ++ jsonBool e.bounded ++ ","
    ++ "\"fair\":" ++ jsonBool e.fair ++ ","
    ++ "\"theorem_refs\":" ++ jsonStrList e.theoremRefs
  ++ "}"

def SearchPolicyArtifact.renderJson (a : SearchPolicyArtifact) : String :=
  "{"
    ++ "\"schema_version\":" ++ jsonNat a.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr a.dialect ++ ","
    ++ "\"entries\":["
    ++ String.intercalate "," (a.entries.map renderEntry)
    ++ "]}"

def SearchPolicyArtifact.checksumString (a : SearchPolicyArtifact) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex a.renderJson

/-- Small internal recursive proof-search lane, suitable for `he_prime`-style
dependent witness search inside the evaluator. -/
def recursiveProofPolicy : SearchPolicyEntry where
  name := "recursive-dependent-proof"
  kernelClass := .ruleExec
  effectClass := .pureStructural
  resourceClass := .defaultAtomSpace
  searchKind := .recursiveProof
  frontier := .depthBounded
  rankingSignals := [.proofDepth]
  interchange := .none
  resultKind := .witnessTerm
  defaultOrder := .native
  supportsReverseOrder := true
  supportsLexOrder := true
  supportsShortLexOrder := true
  theoremRefs := ["he_prime_recursive_search_conformance"]

/-- ATP-facing saturation lane: external proof search with TPTP/TFF interchange. -/
def saturationATPPolicy : SearchPolicyEntry where
  name := "atp-saturation"
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .externalResource
  searchKind := .saturationATP
  frontier := .givenClause
  rankingSignals := [.clauseWeight, .clauseAge, .symbolPrior, .premiseScore]
  interchange := .tptpTFF
  resultKind := .proofObject
  theoremRefs := ["tptp_interchange_for_atp"]

/-- Solver-facing oracle lane: external solver calls are tracked separately from ATP search. -/
def solverOraclePolicy : SearchPolicyEntry where
  name := "solver-oracle"
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .solverResource
  searchKind := .solverOracle
  frontier := .bestFirst
  rankingSignals := [.goalDistance, .modelScore]
  interchange := .smtlib2
  resultKind := .unsatCore
  theoremRefs := ["solver_oracle_contract_lane"]

/-- First-draft MeTTa-family search-policy inventory. -/
def mettaSearchPolicyArtifact : SearchPolicyArtifact where
  dialect := "metta-family"
  entries := [recursiveProofPolicy, saturationATPPolicy, solverOraclePolicy]

def exportMeTTaSearchPolicyContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := mettaSearchPolicyArtifact
  let jsonPath := outDir / "metta.search_policy_contract.json"
  let checksumPath := outDir / "metta.search_policy_contract.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
  IO.println s!"exported metta search policy contract to {outDir}"
  pure 0

def checkMeTTaSearchPolicyContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := mettaSearchPolicyArtifact
  let jsonPath := outDir / "metta.search_policy_contract.json"
  let checksumPath := outDir / "metta.search_policy_contract.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      IO.println s!"[ok] metta search policy contract matches at {outDir}"
      pure 0
    else
      if !jsonOk then
        IO.println s!"[drift] metta search policy contract json mismatch at {jsonPath}"
      if !checksumOk then
        IO.println s!"[drift] metta search policy contract checksum mismatch at {checksumPath}"
      pure 3
  catch e =>
    IO.println s!"metta search policy contract check failed: {e}"
    pure 2

/-- Internal recursive proof search stays inside the semantic lane and does not
require an external interchange format. -/
theorem recursiveProofPolicy_no_interchange :
    recursiveProofPolicy.interchange = .none := rfl

/-- ATP-facing saturation search uses TPTP/TFF as the interchange lane. -/
theorem saturationATPPolicy_uses_tptp :
    saturationATPPolicy.interchange = .tptpTFF := rfl

/-- Solver-facing oracle search uses SMT-LIB2, not TPTP. -/
theorem solverOraclePolicy_uses_smtlib2 :
    solverOraclePolicy.interchange = .smtlib2 := rfl

/-- Any TPTP-speaking policy in the first-draft artifact is an oracle-facing ATP lane. -/
theorem tptp_entries_are_oracle_facing
    (e : SearchPolicyEntry) (hmem : e ∈ mettaSearchPolicyArtifact.entries)
    (htptp : e.interchange = .tptpFOF ∨ e.interchange = .tptpTFF) :
    e.kernelClass = .oracle := by
  simp [mettaSearchPolicyArtifact, recursiveProofPolicy, saturationATPPolicy,
    solverOraclePolicy] at hmem
  rcases hmem with rfl | rfl | rfl
  · cases htptp with
    | inl h => cases h
    | inr h => cases h
  · rfl
  · cases htptp with
    | inl h => cases h
    | inr h => cases h

/-- Any SMT-LIB2-speaking policy in the first-draft artifact is a solver-resource oracle lane. -/
theorem smtlib2_entries_target_solver_resources
    (e : SearchPolicyEntry) (hmem : e ∈ mettaSearchPolicyArtifact.entries)
    (hsmt : e.interchange = .smtlib2) :
    e.kernelClass = .oracle ∧ e.resourceClass = .solverResource := by
  simp [mettaSearchPolicyArtifact, recursiveProofPolicy, saturationATPPolicy,
    solverOraclePolicy] at hmem
  rcases hmem with rfl | rfl | rfl
  · cases hsmt
  · cases hsmt
  · exact ⟨rfl, rfl⟩

section Canaries
#check @mettaSearchPolicyArtifact
#check @exportMeTTaSearchPolicyContract
#check @checkMeTTaSearchPolicyContract
end Canaries

end Mettapedia.Languages.MeTTa.SearchPolicyContract
