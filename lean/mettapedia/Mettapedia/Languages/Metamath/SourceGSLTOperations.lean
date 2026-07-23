import Mettapedia.Languages.Metamath.SourceGSLT

/-!
# Source-derived Metamath operation presentations

This module is the single authored bridge from the Metamath source grammar to
the streaming fold and indexed-checker operations consumed by native staging
and MeTTa inference.  Node contracts are computed from the parameter sorts of
`SourceGSLT.sourceProductions`; lexical references are resolved through the
same literal and lexical tables that generate the parser.

The exporter fails closed if a production, token reference, operation, or
policy is missing or duplicated.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTOperations

open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Proof-relevant values carried by source occurrences -/

inductive FoldRole where
  | label
  | symbol
  | proofStep
  | compressedWord
  | includePath
  | scopeOpen
  | scopeClose
deriving Repr, DecidableEq, BEq

namespace FoldRole

def atom : FoldRole → String
  | .label => "mm-label"
  | .symbol => "mm-symbol"
  | .proofStep => "mm-proof-step"
  | .compressedWord => "mm-compressed-word"
  | .includePath => "mm-include-path"
  | .scopeOpen => "mm-scope-open"
  | .scopeClose => "mm-scope-close"

def ruleSuffix : FoldRole → String
  | .label => "label"
  | .symbol => "symbol"
  | .proofStep => "proof-step"
  | .compressedWord => "compressed-word"
  | .includePath => "include-path"
  | .scopeOpen => "scope-open"
  | .scopeClose => "scope-close"

end FoldRole

inductive FoldContract where
  | none
  | one (role : FoldRole)
  | plus (role : FoldRole)
  | star (role : FoldRole)
  | seq (first second : FoldContract)
deriving Repr, DecidableEq, BEq

namespace FoldContract

/-- Right-associated ordered composition, with database-only parameters
erased from the value receipt rather than represented by a dummy value. -/
def ordered : List FoldContract → FoldContract
  | [] => .none
  | .none :: rest => ordered rest
  | first :: rest =>
      match ordered rest with
      | .none => first
      | second => .seq first second

def render : FoldContract → String
  | .none => "fold-none"
  | .one role => s!"(fold-one {role.atom})"
  | .plus role => s!"(fold-plus {role.atom})"
  | .star role => s!"(fold-star {role.atom})"
  | .seq first second => s!"(fold-seq {first.render} {second.render})"

end FoldContract

/-! ## Authored semantic operation identities -/

inductive SourceOperation where
  | openScope
  | closeScope
  | declareConstants
  | declareVariables
  | declareDisjoint
  | declareFloating
  | declareEssential
  | declareAxiom
  | checkTheoremNormal
  | checkTheoremCompressed
  | resolveInclude
  | completeBlock
deriving Repr, DecidableEq, BEq

namespace SourceOperation

def atom : SourceOperation → String
  | .openScope => "mm-open-scope"
  | .closeScope => "mm-close-scope"
  | .declareConstants => "mm-declare-constants"
  | .declareVariables => "mm-declare-variables"
  | .declareDisjoint => "mm-declare-disjoint"
  | .declareFloating => "mm-declare-floating"
  | .declareEssential => "mm-declare-essential"
  | .declareAxiom => "mm-declare-axiom"
  | .checkTheoremNormal => "mm-check-theorem-normal"
  | .checkTheoremCompressed => "mm-check-theorem-compressed"
  | .resolveInclude => "mm-resolve-include"
  | .completeBlock => "mm-complete-block"

def checkerEffect : SourceOperation → String
  | .openScope => "checker-open-scope"
  | .closeScope => "checker-close-scope"
  | .declareConstants => "checker-declare-constants"
  | .declareVariables => "checker-declare-variables"
  | .declareDisjoint => "checker-declare-distinct"
  | .declareFloating => "checker-declare-floating"
  | .declareEssential => "checker-declare-essential"
  | .declareAxiom => "checker-declare-rule"
  | .checkTheoremNormal => "checker-check-normal"
  | .checkTheoremCompressed => "checker-check-compressed"
  | .resolveInclude => "checker-resolve-source"
  | .completeBlock => "checker-complete-scope"

def ruleSuffix : SourceOperation → String
  | .openScope => "open-scope"
  | .closeScope => "close-scope"
  | .declareConstants => "declare-constants"
  | .declareVariables => "declare-variables"
  | .declareDisjoint => "declare-distinct"
  | .declareFloating => "declare-floating"
  | .declareEssential => "declare-essential"
  | .declareAxiom => "declare-axiom"
  | .checkTheoremNormal => "theorem-normal"
  | .checkTheoremCompressed => "theorem-compressed"
  | .resolveInclude => "resolve-include"
  | .completeBlock => "complete-block"

def foldRuleSuffix : SourceOperation → String
  | .openScope => "open-scope"
  | .closeScope => "close-scope"
  | .declareConstants => "constant"
  | .declareVariables => "variable"
  | .declareDisjoint => "disjoint"
  | .declareFloating => "floating"
  | .declareEssential => "essential"
  | .declareAxiom => "axiom"
  | .checkTheoremNormal => "theorem-normal"
  | .checkTheoremCompressed => "theorem-compressed"
  | .resolveInclude => "include"
  | .completeBlock => "block"

end SourceOperation

def allSourceOperations : List SourceOperation :=
  [.openScope, .closeScope, .declareConstants, .declareVariables,
   .declareDisjoint, .declareFloating, .declareEssential, .declareAxiom,
   .checkTheoremNormal, .checkTheoremCompressed, .resolveInclude,
   .completeBlock]

/-! ## Contracts derived from the sole source grammar -/

def contractForSort? (sort : String) : Option FoldContract :=
  if sort == labelTokenSort then
    some (.one .label)
  else if sort == symbolTokenSort then
    some (.one .symbol)
  else if sort == proofLabelTokenSort then
    some (.one .proofStep)
  else if sort == compressedWordTokenSort then
    some (.one .compressedWord)
  else if sort == includePathTokenSort then
    some (.one .includePath)
  else if sort == symbolListSort then
    some (.plus .symbol)
  else if sort == disjointSymbolListSort then
    some (.seq (.one .symbol) (.plus .symbol))
  else if sort == proofListSort then
    some (.plus .proofStep)
  else if sort == proofHeaderListSort then
    some (.star .proofStep)
  else if sort == compressedWordListSort then
    some (.plus .compressedWord)
  else if sort == databaseSort then
    some .none
  else
    none

def contractForParameter? (parameter : TermParam) : Option FoldContract :=
  match parameter.typeExpr with
  | .base sort => contractForSort? sort
  | _ => none

def contractForParameters? (parameters : List TermParam) :
    Option FoldContract :=
  return FoldContract.ordered (← parameters.mapM contractForParameter?)

structure NodeSpec where
  productionLabel : String
  operation : SourceOperation
deriving Repr, DecidableEq, BEq

def nodeSpecs : List NodeSpec :=
  [{ productionLabel := "statement_const",
     operation := .declareConstants },
   { productionLabel := "statement_var",
     operation := .declareVariables },
   { productionLabel := "statement_disjoint",
     operation := .declareDisjoint },
   { productionLabel := "statement_float",
     operation := .declareFloating },
   { productionLabel := "statement_essential",
     operation := .declareEssential },
   { productionLabel := "statement_axiom",
     operation := .declareAxiom },
   { productionLabel := "statement_theorem_normal",
     operation := .checkTheoremNormal },
   { productionLabel := "statement_theorem_compressed",
     operation := .checkTheoremCompressed },
   { productionLabel := "statement_include",
     operation := .resolveInclude },
   { productionLabel := "statement_block",
     operation := .completeBlock }]

structure NodeBinding where
  source : GrammarRule
  operation : SourceOperation
  contract : FoldContract
deriving Repr, DecidableEq, BEq

def sourceProduction? (label : String) : Option GrammarRule :=
  sourceProductions.find? fun production => production.label == label

def compileNodeSpec? (spec : NodeSpec) : Option NodeBinding := do
  let source ← sourceProduction? spec.productionLabel
  let contract ← contractForParameters? source.params
  pure { source, operation := spec.operation, contract }

/-- Successful node compilation exposes the exact source production lookup
and the exact contract computation used to construct the binding. -/
theorem compileNodeSpec?_exact
    {spec : NodeSpec} {binding : NodeBinding}
    (compiled : compileNodeSpec? spec = some binding) :
    ∃ source contract,
      sourceProduction? spec.productionLabel = some source ∧
      contractForParameters? source.params = some contract ∧
      binding =
        { source := source
          operation := spec.operation
          contract := contract } := by
  cases sourceResult : sourceProduction? spec.productionLabel with
  | none =>
      simp [compileNodeSpec?, sourceResult] at compiled
  | some source =>
      cases contractResult : contractForParameters? source.params with
      | none =>
          simp [compileNodeSpec?, sourceResult, contractResult] at compiled
      | some contract =>
          simp [compileNodeSpec?, sourceResult, contractResult] at compiled
          subst binding
          exact ⟨source, contract, rfl, contractResult, rfl⟩

/-- A production returned by the source lookup is a member of the sole source
grammar's ordered production list. -/
theorem sourceProduction?_member
    {label : String} {source : GrammarRule}
    (found : sourceProduction? label = some source) :
    source ∈ sourceProductions := by
  exact List.mem_of_find?_eq_some found

/-- Every successful binding is sourced from the sole grammar and carries a
contract computed from that exact production's parameters. -/
theorem compileNodeSpec?_source_derived
    {spec : NodeSpec} {binding : NodeBinding}
    (compiled : compileNodeSpec? spec = some binding) :
    binding.source ∈ sourceProductions ∧
      contractForParameters? binding.source.params = some binding.contract := by
  obtain ⟨source, contract, found, contractFound, rfl⟩ :=
    compileNodeSpec?_exact compiled
  exact ⟨sourceProduction?_member found, contractFound⟩

def compiledNodeBindings : List NodeBinding :=
  (nodeSpecs.mapM compileNodeSpec?).getD []

/-! ## Lexical roles and streaming scope boundaries -/

inductive TokenOrigin where
  | lexicalSort (sort : String)
  | literal (spelling : String)
deriving Repr, DecidableEq, BEq

structure TokenRoleSpec where
  ruleSuffix : String
  origin : TokenOrigin
  role : FoldRole
deriving Repr, DecidableEq, BEq

structure TokenRoleBinding where
  ruleSuffix : String
  lexemeReference : String
  role : FoldRole
deriving Repr, DecidableEq, BEq

def tokenRoleSpecs : List TokenRoleSpec :=
  [{ ruleSuffix := "label",
     origin := .lexicalSort labelTokenSort,
     role := .label },
   { ruleSuffix := "proof-label",
     origin := .lexicalSort proofLabelTokenSort,
     role := .proofStep },
   { ruleSuffix := "unknown-proof",
     origin := .literal "?",
     role := .proofStep },
   { ruleSuffix := "symbol",
     origin := .lexicalSort symbolTokenSort,
     role := .symbol },
   { ruleSuffix := "compressed",
     origin := .lexicalSort compressedWordTokenSort,
     role := .compressedWord },
   { ruleSuffix := "include",
     origin := .lexicalSort includePathTokenSort,
     role := .includePath },
   { ruleSuffix := "scope-open",
     origin := .literal "${",
     role := .scopeOpen },
   { ruleSuffix := "scope-close",
     origin := .literal "$}",
     role := .scopeClose }]

def resolveTokenOrigin? : TokenOrigin → Option String
  | .lexicalSort sort => (lexicalReference sort).map (· ++ "-lexeme")
  | .literal spelling => (literalReference spelling).map (· ++ "-lexeme")

def compileTokenRoleSpec? (spec : TokenRoleSpec) : Option TokenRoleBinding := do
  let lexemeReference ← resolveTokenOrigin? spec.origin
  pure { ruleSuffix := spec.ruleSuffix, lexemeReference, role := spec.role }

def compiledTokenRoleBindings : List TokenRoleBinding :=
  (tokenRoleSpecs.mapM compileTokenRoleSpec?).getD []

structure ShiftBinding where
  role : FoldRole
  operation : SourceOperation
deriving Repr, DecidableEq, BEq

def shiftBindings : List ShiftBinding :=
  [{ role := .scopeOpen, operation := .openScope },
   { role := .scopeClose, operation := .closeScope }]

/-! ## Checker conformance policies -/

inductive CheckerPolicy where
  | allowInnerConstants
  | allowDuplicateFloating
  | allowToplevelEssential
  | rejectUnknownSteps
  | skipCompletedSources
  | rejectActiveSourceCycles
deriving Repr, DecidableEq, BEq

namespace CheckerPolicy

def ruleSuffix : CheckerPolicy → String
  | .allowInnerConstants => "inner-constants"
  | .allowDuplicateFloating => "duplicate-floating"
  | .allowToplevelEssential => "toplevel-essential"
  | .rejectUnknownSteps => "unknown-steps"
  | .skipCompletedSources => "completed-sources"
  | .rejectActiveSourceCycles => "active-source-cycles"

def checkerAtom : CheckerPolicy → String
  | .allowInnerConstants => "checker-allow-inner-constants"
  | .allowDuplicateFloating => "checker-allow-duplicate-floating"
  | .allowToplevelEssential => "checker-allow-toplevel-essential"
  | .rejectUnknownSteps => "checker-reject-unknown-steps"
  | .skipCompletedSources => "checker-skip-completed-sources"
  | .rejectActiveSourceCycles => "checker-reject-active-source-cycles"

def value : CheckerPolicy → Bool
  | .allowInnerConstants => false
  | .allowDuplicateFloating => false
  | .allowToplevelEssential => true
  | .rejectUnknownSteps => false
  | .skipCompletedSources => true
  | .rejectActiveSourceCycles => true

def valueAtom (policy : CheckerPolicy) : String :=
  if policy.value then "policy-true" else "policy-false"

end CheckerPolicy

def allCheckerPolicies : List CheckerPolicy :=
  [.allowInnerConstants, .allowDuplicateFloating, .allowToplevelEssential,
   .rejectUnknownSteps, .skipCompletedSources, .rejectActiveSourceCycles]

/-! ## Fail-closed composition audit -/

private def duplicateFree [BEq α] (values : List α) : Bool :=
  values.eraseDups == values

def validateNodeSpecs (specs : List NodeSpec) : Bool :=
  match specs.mapM compileNodeSpec? with
  | none => false
  | some bindings =>
      duplicateFree (specs.map (·.productionLabel)) &&
      duplicateFree (bindings.map (·.operation)) &&
      (shiftBindings.map (·.operation) ++ bindings.map (·.operation) ==
        allSourceOperations)

def validateSourceOperationPresentation : Bool :=
  sourceGrammar.validate.isEmpty &&
    validateNodeSpecs nodeSpecs &&
    (tokenRoleSpecs.mapM compileTokenRoleSpec?).isSome &&
    duplicateFree (tokenRoleSpecs.map (·.ruleSuffix)) &&
    duplicateFree (tokenRoleSpecs.map fun spec => (spec.role, spec.origin)) &&
    duplicateFree allCheckerPolicies

theorem sourceOperationPresentation_valid :
    validateSourceOperationPresentation = true := by
  simp only [validateSourceOperationPresentation, sourceGrammar_valid,
    List.isEmpty_nil, Bool.true_and]
  decide

theorem sourceOperation_count :
    allSourceOperations.length = 12 := by
  decide

theorem nodeBinding_count :
    compiledNodeBindings.length = 10 := by
  decide

theorem tokenRoleBinding_count :
    compiledTokenRoleBindings.length = 8 := by
  decide

theorem checkerPolicy_count :
    allCheckerPolicies.length = 6 := by
  decide

/-- All semantic operations are selected exactly once by either a streaming
scope shift or a completed source node. -/
theorem sourceOperations_selected_once :
    shiftBindings.map (·.operation) ++
        compiledNodeBindings.map (·.operation) =
      allSourceOperations := by
  decide

private def missingProductionSpec : NodeSpec :=
  { productionLabel := "statement_invented"
    operation := .declareConstants }

/-- Negative witness: an operation cannot be attached to a nonexistent source
production. -/
theorem missingProduction_rejected :
    compileNodeSpec? missingProductionSpec = none := by
  decide

private def duplicateOperationSpecs : List NodeSpec :=
  nodeSpecs.dropLast ++
    [{ productionLabel := "statement_block",
       operation := .declareConstants }]

/-- Negative witness: a source operation cannot silently be selected twice
while another operation disappears. -/
theorem duplicateOperation_rejected :
    validateNodeSpecs duplicateOperationSpecs = false := by
  decide

/-! ## MeTTa GSLT rendering -/

private def renderRule (name head : String) : String :=
  s!"    (rule {name}\n      (head {head})\n      (body))"

private def renderRole (role : FoldRole) : String :=
  renderRule ("mm-fold-role-" ++ role.ruleSuffix)
    s!"(source-fold-role {role.atom})"

private def renderTokenRole (binding : TokenRoleBinding) : String :=
  renderRule ("mm-fold-token-" ++ binding.ruleSuffix)
    s!"(source-fold-token {binding.lexemeReference} {binding.role.atom})"

private def renderShift (binding : ShiftBinding) : String :=
  renderRule ("mm-fold-shift-" ++ binding.role.ruleSuffix)
    s!"(source-fold-shift {binding.role.atom} {binding.operation.atom})"

private def renderNode (binding : NodeBinding) : String :=
  renderRule ("mm-fold-node-" ++ binding.operation.foldRuleSuffix) <|
    s!"(source-fold-node {binding.source.label} {binding.operation.atom} " ++
      s!"{binding.contract.render})"

private def renderCheckerEffect (operation : SourceOperation) : String :=
  renderRule ("mm-checker-" ++ operation.ruleSuffix)
    s!"(source-checker-effect {operation.atom} {operation.checkerEffect})"

private def renderCheckerPolicy (policy : CheckerPolicy) : String :=
  renderRule ("mm-checker-policy-" ++ policy.ruleSuffix)
    s!"(source-checker-policy {policy.checkerAtom} {policy.valueAtom})"

private def renderPresentation
    (name : String) (rules : List String) : String :=
  s!"(gslt-presentation-v1 {name}\n" ++
    "  (signature)\n" ++
    "  (equations)\n" ++
    "  (rewrites\n" ++
    String.intercalate "\n" rules ++
    "\n  ))\n"

def renderedSourceFold : String :=
  "; Generated from the Metamath source grammar and operation algebra.\n" ++
  "; Node contracts are derived from source-production parameter sorts.\n\n" ++
    renderPresentation "MetamathSourceFoldV1" (
      ([.label, .symbol, .proofStep, .compressedWord, .includePath,
        .scopeOpen, .scopeClose].map renderRole) ++
      (compiledTokenRoleBindings.map renderTokenRole) ++
      (shiftBindings.map renderShift) ++
      (compiledNodeBindings.map renderNode))

def renderedSourceChecker : String :=
  "; Generated from the Metamath source operation algebra.\n" ++
  "; This is the explicit composition into generic indexed-checker effects.\n\n" ++
    renderPresentation "MetamathSourceCheckerV1" (
      (allSourceOperations.map renderCheckerEffect) ++
      (allCheckerPolicies.map renderCheckerPolicy))

end Mettapedia.Languages.Metamath.SourceGSLTOperations
