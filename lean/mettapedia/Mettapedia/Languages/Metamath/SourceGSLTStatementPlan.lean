import Mettapedia.Languages.Metamath.SourceGSLTOperations

/-!
# Source-derived Metamath statement plan

The streaming source machine needs fixed-token dispatch, but it must not own a
second table of Metamath spellings.  This module compiles that dispatch plan
from the operation bindings already checked against the sole authored
`SourceGSLT.sourceProductions` list.  A changed or missing production makes
the compiler fail closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTStatementPlan

open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Terminal spellings of a source production, in authored order. -/
def productionTerminals (production : GrammarRule) : List String :=
  production.syntaxPattern.filterMap fun
    | .terminal spelling => some spelling
    | _ => none

/-- Select the unique source-derived binding assigned to an operation. -/
def operationBinding? (operation : SourceOperation) : Option NodeBinding := do
  let spec ← nodeSpecs.find? fun candidate => candidate.operation == operation
  compileNodeSpec? spec

/-- The terminal row consulted by streaming dispatch for one semantic
operation. -/
def operationTerminals? (operation : SourceOperation) : Option (List String) :=
  (operationBinding? operation).map fun binding =>
    productionTerminals binding.source

/-- Every successfully selected operation row is an actual row of the sole
authored source grammar. -/
theorem operationTerminals?_source
    {operation : SourceOperation} {terminals : List String}
    (found : operationTerminals? operation = some terminals) :
    ∃ production,
      production ∈ sourceProductions ∧
      terminals = productionTerminals production := by
  unfold operationTerminals? at found
  cases hbinding : operationBinding? operation with
  | none => simp [hbinding] at found
  | some binding =>
      simp [hbinding] at found
      subst terminals
      unfold operationBinding? at hbinding
      cases hspec : nodeSpecs.find? fun candidate =>
          candidate.operation == operation with
      | none => simp [hspec] at hbinding
      | some spec =>
          simp [hspec] at hbinding
          exact ⟨binding.source,
            (compileNodeSpec?_source_derived hbinding).1, rfl⟩

/-- Select a literal token role only after its parser reference has also
compiled from the source grammar's literal table. -/
def literalRoleSpelling? (suffix : String) : Option String := do
  let spec ← tokenRoleSpecs.find? fun candidate =>
    candidate.ruleSuffix == suffix
  let _ ← compileTokenRoleSpec? spec
  match spec.origin with
  | .literal spelling => some spelling
  | .lexicalSort _ => none

/-- A fixed spelling paired with the codepoints from the same authored
literal-table row. -/
structure CompiledLiteral where
  spelling : String
  codepoints : List Nat
deriving DecidableEq, Repr

def compileLiteral? (spelling : String) : Option CompiledLiteral := do
  let codepoints ← literalCodepoints spelling
  pure { spelling, codepoints }

/-- Fixed-token and lexical-class data consumed by the one-pass statement
machine.  Every spelling is extracted from a source production or a checked
literal-role binding; codepoint classes are the authored source classes. -/
structure StatementPlan where
  constantKeyword : CompiledLiteral
  variableKeyword : CompiledLiteral
  disjointKeyword : CompiledLiteral
  floatingKeyword : CompiledLiteral
  essentialKeyword : CompiledLiteral
  axiomKeyword : CompiledLiteral
  theoremKeyword : CompiledLiteral
  proofSeparator : CompiledLiteral
  statementEnd : CompiledLiteral
  scopeOpen : CompiledLiteral
  scopeClose : CompiledLiteral
  includeOpen : CompiledLiteral
  includeClose : CompiledLiteral
  commentOpen : CompiledLiteral
  commentClose : CompiledLiteral
  parenOpen : CompiledLiteral
  parenClose : CompiledLiteral
  unknownProof : CompiledLiteral
  labelMembers : List Nat
  mathMembers : List Nat
  compressedMembers : List Nat
deriving DecidableEq, Repr

/-- Compile the exact statement shapes used by the streaming specialization.
Shared delimiters must agree across all source productions; any drift fails
the plan rather than selecting an arbitrary row. -/
def compile? : Option StatementPlan := do
  let [constantSpelling, constantEndSpelling] ←
    operationTerminals? .declareConstants | none
  let [variableSpelling, variableEndSpelling] ←
    operationTerminals? .declareVariables | none
  let [disjointSpelling, disjointEndSpelling] ←
    operationTerminals? .declareDisjoint | none
  let [floatingSpelling, floatingEndSpelling] ←
    operationTerminals? .declareFloating | none
  let [essentialSpelling, essentialEndSpelling] ←
    operationTerminals? .declareEssential | none
  let [axiomSpelling, axiomEndSpelling] ←
    operationTerminals? .declareAxiom | none
  let [normalTheoremSpelling, normalProofSeparatorSpelling,
      normalEndSpelling] ←
    operationTerminals? .checkTheoremNormal | none
  let [compressedTheoremSpelling, compressedProofSeparatorSpelling,
      parenOpenSpelling, parenCloseSpelling, compressedEndSpelling] ←
    operationTerminals? .checkTheoremCompressed | none
  let [scopeOpenSpelling, scopeCloseSpelling] ←
    operationTerminals? .completeBlock | none
  let [includeOpenSpelling, includeCloseSpelling] ←
    operationTerminals? .resolveInclude | none
  let unknownProofSpelling ← literalRoleSpelling? "unknown-proof"
  let constantKeyword ← compileLiteral? constantSpelling
  let variableKeyword ← compileLiteral? variableSpelling
  let disjointKeyword ← compileLiteral? disjointSpelling
  let floatingKeyword ← compileLiteral? floatingSpelling
  let essentialKeyword ← compileLiteral? essentialSpelling
  let axiomKeyword ← compileLiteral? axiomSpelling
  let theoremKeyword ← compileLiteral? normalTheoremSpelling
  let proofSeparator ← compileLiteral? normalProofSeparatorSpelling
  let statementEnd ← compileLiteral? constantEndSpelling
  let scopeOpen ← compileLiteral? scopeOpenSpelling
  let scopeClose ← compileLiteral? scopeCloseSpelling
  let includeOpen ← compileLiteral? includeOpenSpelling
  let includeClose ← compileLiteral? includeCloseSpelling
  let commentOpen : CompiledLiteral :=
    { spelling := String.ofList (commentOpenCodepoints.map Char.ofNat)
      codepoints := commentOpenCodepoints }
  let commentClose : CompiledLiteral :=
    { spelling := String.ofList (commentCloseCodepoints.map Char.ofNat)
      codepoints := commentCloseCodepoints }
  let parenOpen ← compileLiteral? parenOpenSpelling
  let parenClose ← compileLiteral? parenCloseSpelling
  let unknownProof ← compileLiteral? unknownProofSpelling
  guard (constantEndSpelling == variableEndSpelling)
  guard (constantEndSpelling == disjointEndSpelling)
  guard (constantEndSpelling == floatingEndSpelling)
  guard (constantEndSpelling == essentialEndSpelling)
  guard (constantEndSpelling == axiomEndSpelling)
  guard (constantEndSpelling == normalEndSpelling)
  guard (constantEndSpelling == compressedEndSpelling)
  guard (normalTheoremSpelling == compressedTheoremSpelling)
  guard (normalProofSeparatorSpelling == compressedProofSeparatorSpelling)
  pure
    { constantKeyword
      variableKeyword
      disjointKeyword
      floatingKeyword
      essentialKeyword
      axiomKeyword
      theoremKeyword
      proofSeparator
      statementEnd
      scopeOpen
      scopeClose
      includeOpen
      includeClose
      commentOpen
      commentClose
      parenOpen
      parenClose
      unknownProof
      labelMembers := labelCodepoints
      mathMembers := mathSymbolCodepoints
      compressedMembers := compressedCodepoints }

/-- The sole plan used by the streaming machine.  The accompanying theorem
prevents the `getD` fallback from becoming an unobserved authority. -/
def sourceStatementPlan : StatementPlan := compile?.getD
  { constantKeyword := ⟨"", []⟩
    variableKeyword := ⟨"", []⟩
    disjointKeyword := ⟨"", []⟩
    floatingKeyword := ⟨"", []⟩
    essentialKeyword := ⟨"", []⟩
    axiomKeyword := ⟨"", []⟩
    theoremKeyword := ⟨"", []⟩
    proofSeparator := ⟨"", []⟩
    statementEnd := ⟨"", []⟩
    scopeOpen := ⟨"", []⟩
    scopeClose := ⟨"", []⟩
    includeOpen := ⟨"", []⟩
    includeClose := ⟨"", []⟩
    commentOpen := ⟨"", []⟩
    commentClose := ⟨"", []⟩
    parenOpen := ⟨"", []⟩
    parenClose := ⟨"", []⟩
    unknownProof := ⟨"", []⟩
    labelMembers := []
    mathMembers := []
    compressedMembers := [] }

theorem sourceStatementPlan_compiles :
    compile? = some sourceStatementPlan := by
  rfl

/-- Each operation-to-terminal association used by dispatch is pinned to the
exact source-derived row selected by the compiler. -/
theorem sourceStatementPlan_operation_rows :
    operationTerminals? .declareConstants =
        some [sourceStatementPlan.constantKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .declareVariables =
        some [sourceStatementPlan.variableKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .declareDisjoint =
        some [sourceStatementPlan.disjointKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .declareFloating =
        some [sourceStatementPlan.floatingKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .declareEssential =
        some [sourceStatementPlan.essentialKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .declareAxiom =
        some [sourceStatementPlan.axiomKeyword.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .checkTheoremNormal =
        some [sourceStatementPlan.theoremKeyword.spelling,
          sourceStatementPlan.proofSeparator.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .checkTheoremCompressed =
        some [sourceStatementPlan.theoremKeyword.spelling,
          sourceStatementPlan.proofSeparator.spelling,
          sourceStatementPlan.parenOpen.spelling,
          sourceStatementPlan.parenClose.spelling,
          sourceStatementPlan.statementEnd.spelling] ∧
    operationTerminals? .completeBlock =
        some [sourceStatementPlan.scopeOpen.spelling,
          sourceStatementPlan.scopeClose.spelling] ∧
    operationTerminals? .resolveInclude =
        some [sourceStatementPlan.includeOpen.spelling,
          sourceStatementPlan.includeClose.spelling] := by
  decide

theorem sourceStatementPlan_unknown_role :
    literalRoleSpelling? "unknown-proof" =
      some sourceStatementPlan.unknownProof.spelling := by
  decide

/-- Positive and negative compiler calibration. -/
example : sourceStatementPlan.theoremKeyword.spelling = "$p" := by decide
example : sourceStatementPlan.theoremKeyword.codepoints = [36, 112] := by decide
example : sourceStatementPlan.scopeOpen.spelling = "${" := by decide
example : sourceStatementPlan.commentOpen.codepoints = [36, 40] := by decide

private def missingConstantSpec : List NodeSpec :=
  nodeSpecs.filter fun spec => spec.operation != .declareConstants

private def operationBindingFrom? (specs : List NodeSpec)
    (operation : SourceOperation) : Option NodeBinding := do
  let spec ← specs.find? fun candidate => candidate.operation == operation
  compileNodeSpec? spec

/-- Removing the constant production's semantic binding makes that dispatch
row unavailable; the selection does not fall back to a literal. -/
example : operationBindingFrom? missingConstantSpec .declareConstants = none := by
  decide

end Mettapedia.Languages.Metamath.SourceGSLTStatementPlan
