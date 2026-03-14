import MeTTailCore.MeTTaIL.RewriteIRV2

namespace MeTTailCore.MeTTaIL.RewriteIR

open MeTTailCore.MeTTaIL.RewriteIRV2

inductive RewriteIRRuleMode where
  | ordinaryForward
  | compatHead
  | symbolicOutput
deriving Repr, DecidableEq, BEq

structure RewriteIRRule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  leftRepr : String
  rightRepr : String
  premiseRelations : List String := []
  lhsJson : Option String := none
  rhsJson : Option String := none
  premisesJson : Option String := none
  lhsVars : List String := []
  premiseVarFlow : List PremiseVarFlow := []
  rhsVars : List String := []
  rhsFreshVars : List String := []
  rhsEvalRequires : List String := []
  ruleMode : RewriteIRRuleMode := .ordinaryForward
  rootUpdate : Option RootUpdateHint := none
deriving Repr, DecidableEq, BEq

structure RewriteIRArtifact where
  schemaVersion : Nat := 2
  dialect : String
  rules : List RewriteIRRule
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def orderedUniqNat (xs : List Nat) : List Nat :=
  xs.eraseDups

private def normalizeFlow (f : PremiseVarFlow) : PremiseVarFlow :=
  { f with
    premiseVars := orderedUniq f.premiseVars
    introducedVars := orderedUniq f.introducedVars }

private def normalizeRootUpdate (h : RootUpdateHint) : RootUpdateHint :=
  { h with
    preservedArgPositions := orderedUniqNat h.preservedArgPositions
    changedArgPositions := orderedUniqNat h.changedArgPositions }

private def normalizeRule (r : RewriteIRRule) : RewriteIRRule :=
  { r with
    sourceLabel := if r.sourceLabel.isEmpty then r.sourceInstr else r.sourceLabel
    premiseRelations := (sortListByKey r.premiseRelations id).eraseDups
    lhsVars := orderedUniq r.lhsVars
    premiseVarFlow := r.premiseVarFlow.map normalizeFlow
    rhsVars := orderedUniq r.rhsVars
    rhsFreshVars := orderedUniq r.rhsFreshVars
    rhsEvalRequires := orderedUniq r.rhsEvalRequires
    rootUpdate := r.rootUpdate.map normalizeRootUpdate }

private def normalizeArtifact (a : RewriteIRArtifact) : RewriteIRArtifact :=
  { a with
    rules := sortListByKey (a.rules.map normalizeRule)
      (fun r => s!"{r.sourceInstr}:{r.priority}:{r.ruleId}:{r.ruleName}") }

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

private def jsonNat (n : Nat) : String :=
  toString n

private def renderStringList (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map jsonNat) ++ "]"

private def renderRuleMode : RewriteIRRuleMode → String
  | .ordinaryForward => "\"ordinary_forward\""
  | .compatHead => "\"compat_head\""
  | .symbolicOutput => "\"symbolic_output\""

private def renderPremiseVarFlow (f : PremiseVarFlow) : String :=
  "{"
    ++ "\"premise_index\":" ++ jsonNat f.premiseIndex ++ ","
    ++ "\"premise_vars\":" ++ renderStringList f.premiseVars ++ ","
    ++ "\"introduced_vars\":" ++ renderStringList f.introducedVars
  ++ "}"

private def renderRootUpdateHint (h : RootUpdateHint) : String :=
  "{"
    ++ "\"lhs_root_ctor\":" ++ jsonStr h.lhsRootCtor ++ ","
    ++ "\"rhs_root_ctor\":" ++ jsonStr h.rhsRootCtor ++ ","
    ++ "\"lhs_arity\":" ++ jsonNat h.lhsArity ++ ","
    ++ "\"rhs_arity\":" ++ jsonNat h.rhsArity ++ ","
    ++ "\"preserved_arg_positions\":" ++ renderNatList h.preservedArgPositions ++ ","
    ++ "\"changed_arg_positions\":" ++ renderNatList h.changedArgPositions
  ++ "}"

private def renderRule (r : RewriteIRRule) : String :=
  "{"
    ++ "\"rule_id\":" ++ jsonStr r.ruleId ++ ","
    ++ "\"rule_name\":" ++ jsonStr r.ruleName ++ ","
    ++ "\"source_instr\":" ++ jsonStr r.sourceInstr ++ ","
    ++ "\"source_label\":" ++ jsonStr r.sourceLabel ++ ","
    ++ "\"priority\":" ++ jsonNat r.priority ++ ","
    ++ "\"left_repr\":" ++ jsonStr r.leftRepr ++ ","
    ++ "\"right_repr\":" ++ jsonStr r.rightRepr ++ ","
    ++ "\"premise_relations\":["
    ++ String.intercalate "," (r.premiseRelations.map jsonStr)
    ++ "],"
    ++ "\"lhs\":" ++ (r.lhsJson.getD "null") ++ ","
    ++ "\"rhs\":" ++ (r.rhsJson.getD "null") ++ ","
    ++ "\"premises\":" ++ (r.premisesJson.getD "[]") ++ ","
    ++ "\"lhs_vars\":" ++ renderStringList r.lhsVars ++ ","
    ++ "\"premise_var_flow\":["
    ++ String.intercalate "," (r.premiseVarFlow.map renderPremiseVarFlow)
    ++ "],"
    ++ "\"rhs_vars\":" ++ renderStringList r.rhsVars ++ ","
    ++ "\"rhs_fresh_vars\":" ++ renderStringList r.rhsFreshVars ++ ","
    ++ "\"rhs_eval_requires\":" ++ renderStringList r.rhsEvalRequires ++ ","
    ++ "\"rule_mode\":" ++ renderRuleMode r.ruleMode ++ ","
    ++ "\"root_update\":"
    ++ (match r.rootUpdate with
      | some h => renderRootUpdateHint h
      | none => "null")
  ++ "}"

def RewriteIRArtifact.renderJson (a : RewriteIRArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"rules\":[" ++ String.intercalate "," (norm.rules.map renderRule) ++ "]"
  ++ "}"

private def isRuleId (rule : String) : Bool :=
  if !rule.startsWith "R" then
    false
  else
    let tail := (rule.drop 1).toString
    !tail.isEmpty && tail.toList.all Char.isDigit

private def lintRule (r : RewriteIRRule) : List String :=
  let idErrs :=
    if isRuleId r.ruleId then
      []
    else
      [s!"invalid rule_id '{r.ruleId}'"]
  let nameErrs :=
    if r.ruleName.isEmpty then
      [s!"{r.ruleId}: rule_name must be non-empty"]
    else
      []
  let sourceErrs :=
    if r.sourceInstr.isEmpty then
      [s!"{r.ruleId}: source_instr must be non-empty"]
    else if !r.sourceInstr.startsWith "C_" then
      [s!"{r.ruleId}: source_instr must start with C_, got '{r.sourceInstr}'"]
    else
      []
  let reprErrs :=
    if r.leftRepr.isEmpty || r.rightRepr.isEmpty then
      [s!"{r.ruleId}: left_repr/right_repr must be non-empty"]
    else
      []
  let premErrs :=
    let dup := r.premiseRelations.length != r.premiseRelations.eraseDups.length
    let empties := r.premiseRelations.any String.isEmpty
    (if dup then [s!"{r.ruleId}: premise_relations contains duplicates"] else [])
      ++ (if empties then [s!"{r.ruleId}: premise_relations cannot contain empty strings"] else [])
  let flowErrs :=
    r.premiseVarFlow.filterMap fun f =>
      if f.introducedVars.all (fun x => f.premiseVars.contains x) then
        none
      else
        some s!"{r.ruleId}: premise flow {f.premiseIndex} introduces vars not present in premise_vars"
  let rhsErrs :=
    let freshOutside :=
      r.rhsFreshVars.filter (fun x => !(r.rhsVars.contains x))
    let evalOutside :=
      r.rhsEvalRequires.filter (fun x => !(r.rhsVars.contains x))
    (if freshOutside.isEmpty then [] else
      [s!"{r.ruleId}: rhs_fresh_vars must be a subset of rhs_vars"])
    ++
    (if evalOutside.isEmpty then [] else
      [s!"{r.ruleId}: rhs_eval_requires must be a subset of rhs_vars"])
  idErrs ++ nameErrs ++ sourceErrs ++ reprErrs ++ premErrs ++ flowErrs ++ rhsErrs

def RewriteIRArtifact.lintErrors (a : RewriteIRArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 1 then
      [s!"schema_version must be >= 1, got {norm.schemaVersion}"]
    else
      []
  let dialectErrs :=
    if norm.dialect.isEmpty then
      ["dialect must be non-empty"]
    else
      []
  let dupRuleIds :=
    let ids := norm.rules.map (·.ruleId)
    if ids.length == ids.eraseDups.length then
      []
    else
      ["rule_id values must be unique"]
  schemaErrs ++ dialectErrs ++ dupRuleIds
    ++ (norm.rules.map lintRule).foldl (· ++ ·) []

def RewriteIRArtifact.isLintClean (a : RewriteIRArtifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def RewriteIRArtifact.checksum (a : RewriteIRArtifact) : UInt64 :=
  checksumText a.renderJson

def RewriteIRArtifact.checksumString (a : RewriteIRArtifact) : String :=
  toString a.checksum

end MeTTailCore.MeTTaIL.RewriteIR
