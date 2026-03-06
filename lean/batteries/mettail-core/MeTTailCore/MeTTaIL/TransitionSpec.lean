namespace MeTTailCore.MeTTaIL.TransitionSpec

inductive TransitionContract where
  | deterministicReduction
  | memoizationSafe
  | specializationSafe
  | coreGroundEvalSafe
  | orderSensitive
  | nondeterministic
deriving Repr, DecidableEq, BEq

private def renderContract : TransitionContract → String
  | .deterministicReduction => "deterministic_reduction"
  | .memoizationSafe => "memoization_safe"
  | .specializationSafe => "specialization_safe"
  | .coreGroundEvalSafe => "core_ground_eval_safe"
  | .orderSensitive => "order_sensitive"
  | .nondeterministic => "nondeterministic"

structure TransitionSemanticKey where
  sourceInstrClass : String
  transitionKind : String
  guardFamily : String
  effectKind : String
  dialectExt : Option String := none
  contracts : List TransitionContract := []
deriving Repr, DecidableEq, BEq

structure TransitionRule where
  logicalTransitionId : String
  sourceInstr : String
  sourceLabel : String := ""
  ruleId : String
  semKey : TransitionSemanticKey
  priority : Nat
deriving Repr, DecidableEq, BEq

structure TransitionSource where
  sourceInstr : String
  sourceLabel : String := ""
  orderedRules : List String
deriving Repr, DecidableEq, BEq

structure TransitionSpecArtifact where
  schemaVersion : Nat := 2
  dialect : String
  sources : List TransitionSource
  rules : List TransitionRule
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def normalizeSource (s : TransitionSource) : TransitionSource :=
  { s with
    sourceLabel := if s.sourceLabel.isEmpty then s.sourceInstr else s.sourceLabel }

private def normalizeContracts (xs : List TransitionContract) : List TransitionContract :=
  let sorted := sortListByKey xs renderContract
  sorted.eraseDups

private def normalizeSemKey (k : TransitionSemanticKey) : TransitionSemanticKey :=
  { k with contracts := normalizeContracts k.contracts }

private def normalizeRule (r : TransitionRule) : TransitionRule :=
  { r with
    sourceLabel := if r.sourceLabel.isEmpty then r.sourceInstr else r.sourceLabel
    semKey := normalizeSemKey r.semKey }

private def normalizeArtifact (a : TransitionSpecArtifact) : TransitionSpecArtifact :=
  { a with
    sources := sortListByKey (a.sources.map normalizeSource)
      (fun s => s.sourceInstr)
    rules := sortListByKey (a.rules.map normalizeRule)
      (fun r => s!"{r.sourceInstr}:{r.priority}:{r.ruleId}:{r.logicalTransitionId}") }

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

private def jsonOptStr : Option String → String
  | some s => jsonStr s
  | none => "null"

private def renderSource (s : TransitionSource) : String :=
  "{"
    ++ "\"source_instr\":" ++ jsonStr s.sourceInstr ++ ","
    ++ "\"source_label\":" ++ jsonStr s.sourceLabel ++ ","
    ++ "\"ordered_rules\":[" ++ String.intercalate "," (s.orderedRules.map jsonStr) ++ "]"
  ++ "}"

private def renderSemKey (k : TransitionSemanticKey) : String :=
  "{"
    ++ "\"source_instr_class\":" ++ jsonStr k.sourceInstrClass ++ ","
    ++ "\"transition_kind\":" ++ jsonStr k.transitionKind ++ ","
    ++ "\"guard_family\":" ++ jsonStr k.guardFamily ++ ","
    ++ "\"effect_kind\":" ++ jsonStr k.effectKind ++ ","
    ++ "\"dialect_ext\":" ++ jsonOptStr k.dialectExt ++ ","
    ++ "\"contracts\":[" ++ String.intercalate "," (k.contracts.map (fun c => jsonStr (renderContract c))) ++ "]"
  ++ "}"

private def renderRule (r : TransitionRule) : String :=
  "{"
    ++ "\"logical_transition_id\":" ++ jsonStr r.logicalTransitionId ++ ","
    ++ "\"source_instr\":" ++ jsonStr r.sourceInstr ++ ","
    ++ "\"source_label\":" ++ jsonStr r.sourceLabel ++ ","
    ++ "\"rule_id\":" ++ jsonStr r.ruleId ++ ","
    ++ "\"sem_key\":" ++ renderSemKey r.semKey ++ ","
    ++ "\"priority\":" ++ jsonNat r.priority
  ++ "}"

def TransitionSpecArtifact.renderJson (a : TransitionSpecArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"sources\":[" ++ String.intercalate "," (norm.sources.map renderSource) ++ "],"
    ++ "\"rules\":[" ++ String.intercalate "," (norm.rules.map renderRule) ++ "]"
  ++ "}"

private def isRuleId (rule : String) : Bool :=
  if !rule.startsWith "R" then
    false
  else
    let tail := (rule.drop 1).toString
    !tail.isEmpty && tail.toList.all Char.isDigit

private def lintSource (s : TransitionSource) : List String :=
  let sourceErrs :=
    if s.sourceInstr.isEmpty then
      ["source_instr must be non-empty"]
    else if !(s.sourceInstr.startsWith "C_") then
      [s!"source_instr must start with C_, got: {s.sourceInstr}"]
    else
      []
  let orderErrs :=
    if s.orderedRules.isEmpty then
      [s!"{s.sourceInstr}: ordered_rules cannot be empty"]
    else
      []
  let badRuleErrs := s.orderedRules.filterMap fun r =>
    if isRuleId r then none else some s!"{s.sourceInstr}: invalid rule id '{r}'"
  let dupRuleErrs :=
    if s.orderedRules.length == s.orderedRules.eraseDups.length then
      []
    else
      [s!"{s.sourceInstr}: ordered_rules contains duplicates"]
  sourceErrs ++ orderErrs ++ badRuleErrs ++ dupRuleErrs

private def lintSemKey (tid : String) (k : TransitionSemanticKey) : List String :=
  let classErrs :=
    if k.sourceInstrClass.isEmpty then
      [s!"{tid}: sem_key.source_instr_class must be non-empty"]
    else []
  let kindErrs :=
    if k.transitionKind.isEmpty then
      [s!"{tid}: sem_key.transition_kind must be non-empty"]
    else []
  let guardErrs :=
    if k.guardFamily.isEmpty then
      [s!"{tid}: sem_key.guard_family must be non-empty"]
    else []
  let effectErrs :=
    if k.effectKind.isEmpty then
      [s!"{tid}: sem_key.effect_kind must be non-empty"]
    else []
  let contractsErrs :=
    if k.contracts.isEmpty then
      [s!"{tid}: sem_key.contracts cannot be empty"]
    else
      let rendered := k.contracts.map renderContract
      if rendered.length == rendered.eraseDups.length then
        []
      else
        [s!"{tid}: sem_key.contracts contains duplicates"]
  classErrs ++ kindErrs ++ guardErrs ++ effectErrs ++ contractsErrs

private def lintRule (r : TransitionRule) : List String :=
  let idErrs :=
    if r.logicalTransitionId.isEmpty then
      ["logical_transition_id must be non-empty"]
    else []
  let sourceErrs :=
    if r.sourceInstr.isEmpty then
      [s!"{r.logicalTransitionId}: source_instr must be non-empty"]
    else if !(r.sourceInstr.startsWith "C_") then
      [s!"{r.logicalTransitionId}: source_instr must start with C_, got: {r.sourceInstr}"]
    else []
  let ruleErrs :=
    if isRuleId r.ruleId then
      []
    else
      [s!"{r.logicalTransitionId}: invalid rule_id '{r.ruleId}'"]
  idErrs ++ sourceErrs ++ ruleErrs ++ lintSemKey r.logicalTransitionId r.semKey

def TransitionSpecArtifact.lintErrors (a : TransitionSpecArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 2 then
      [s!"schema_version must be >= 2, got {norm.schemaVersion}"]
    else []
  let dialectErrs :=
    if norm.dialect.isEmpty then
      ["dialect must be non-empty"]
    else []
  let sourceErrs :=
    if norm.sources.isEmpty then
      ["sources cannot be empty"]
    else
      []
  let rulesErrs :=
    if norm.rules.isEmpty then
      ["rules cannot be empty"]
    else
      []
  let dupSourceErrs :=
    let ids := norm.sources.map (·.sourceInstr)
    if ids.length == ids.eraseDups.length then
      []
    else
      ["source_instr values must be unique"]
  let dupTransitionErrs :=
    let ids := norm.rules.map (·.logicalTransitionId)
    if ids.length == ids.eraseDups.length then
      []
    else
      ["logical_transition_id values must be unique"]
  let coverageErrs :=
    let ruleIds := norm.rules.map (·.ruleId)
    norm.sources.foldl (fun acc src =>
      let miss := src.orderedRules.filter (fun rid => !ruleIds.contains rid)
      if miss.isEmpty then acc
      else acc ++ [s!"{src.sourceInstr}: ordered_rules missing semantic rule entries: {String.intercalate ", " miss}"]) []
  schemaErrs ++ dialectErrs ++ sourceErrs ++ rulesErrs ++ dupSourceErrs ++ dupTransitionErrs ++ coverageErrs
    ++ (norm.sources.map lintSource).foldl (· ++ ·) []
    ++ (norm.rules.map lintRule).foldl (· ++ ·) []

def TransitionSpecArtifact.isLintClean (a : TransitionSpecArtifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def TransitionSpecArtifact.checksum (a : TransitionSpecArtifact) : UInt64 :=
  checksumText a.renderJson

def TransitionSpecArtifact.checksumString (a : TransitionSpecArtifact) : String :=
  toString a.checksum

end MeTTailCore.MeTTaIL.TransitionSpec
