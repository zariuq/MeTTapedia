namespace MeTTailCore.MeTTaIL.RewriteIR

structure RewriteIRRule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  leftRepr : String
  rightRepr : String
  premiseRelations : List String := []
deriving Repr, DecidableEq, BEq

structure RewriteIRArtifact where
  schemaVersion : Nat := 1
  dialect : String
  rules : List RewriteIRRule
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def normalizeRule (r : RewriteIRRule) : RewriteIRRule :=
  { r with
    sourceLabel := if r.sourceLabel.isEmpty then r.sourceInstr else r.sourceLabel
    premiseRelations := (sortListByKey r.premiseRelations id).eraseDups }

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
    ++ "]"
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
  idErrs ++ nameErrs ++ sourceErrs ++ reprErrs ++ premErrs

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
  let ruleErrs :=
    if norm.rules.isEmpty then
      ["rules cannot be empty"]
    else
      []
  let dupRuleIds :=
    let ids := norm.rules.map (·.ruleId)
    if ids.length == ids.eraseDups.length then
      []
    else
      ["rule_id values must be unique"]
  schemaErrs ++ dialectErrs ++ ruleErrs ++ dupRuleIds
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
