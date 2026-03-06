namespace MeTTailCore.MeTTaIL.TransitionPlan

inductive TransitionContract where
  | deterministicReduction
  | memoizationSafe
  | specializationSafe
  | coreGroundEvalSafe
  | orderSensitive
  | nondeterministic
deriving Repr, DecidableEq, BEq

structure TransitionSemanticKey where
  sourceInstrClass : String
  transitionKind : String
  guardFamily : String
  effectKind : String
  dialectExt : Option String := none
  contracts : List TransitionContract := []
deriving Repr, DecidableEq, BEq

structure TransitionPlanEntry where
  logicalTransitionId : String
  sourceInstr : String
  sourceLabel : String := ""
  semKey : TransitionSemanticKey
  priority : Nat
  legacyRuleId : Option String := none
deriving Repr, DecidableEq, BEq

structure TransitionPlanArtifact where
  schemaVersion : Nat := 1
  dialect : String
  transitions : List TransitionPlanEntry
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def renderContract : TransitionContract → String
  | .deterministicReduction => "deterministic_reduction"
  | .memoizationSafe => "memoization_safe"
  | .specializationSafe => "specialization_safe"
  | .coreGroundEvalSafe => "core_ground_eval_safe"
  | .orderSensitive => "order_sensitive"
  | .nondeterministic => "nondeterministic"

private def normalizeContracts (xs : List TransitionContract) : List TransitionContract :=
  let sorted := sortListByKey xs renderContract
  sorted.eraseDups

private def normalizeSemKey (k : TransitionSemanticKey) : TransitionSemanticKey :=
  { k with contracts := normalizeContracts k.contracts }

private def normalizeEntry (e : TransitionPlanEntry) : TransitionPlanEntry :=
  { e with
    sourceLabel := if e.sourceLabel.isEmpty then e.sourceInstr else e.sourceLabel
    semKey := normalizeSemKey e.semKey
  }

private def normalizeArtifact (a : TransitionPlanArtifact) : TransitionPlanArtifact :=
  { a with
    transitions := sortListByKey (a.transitions.map normalizeEntry)
      (fun e => s!"{e.logicalTransitionId}:{e.sourceInstr}:{e.priority}") }

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

private def jsonOptStr : Option String → String
  | some s => jsonStr s
  | none => "null"

private def renderSemKey (k : TransitionSemanticKey) : String :=
  "{"
    ++ "\"source_instr_class\":" ++ jsonStr k.sourceInstrClass ++ ","
    ++ "\"transition_kind\":" ++ jsonStr k.transitionKind ++ ","
    ++ "\"guard_family\":" ++ jsonStr k.guardFamily ++ ","
    ++ "\"effect_kind\":" ++ jsonStr k.effectKind ++ ","
    ++ "\"dialect_ext\":" ++ jsonOptStr k.dialectExt ++ ","
    ++ "\"contracts\":[" ++ String.intercalate "," (k.contracts.map (fun c => jsonStr (renderContract c))) ++ "]"
  ++ "}"

private def renderEntry (e : TransitionPlanEntry) : String :=
  "{"
    ++ "\"logical_transition_id\":" ++ jsonStr e.logicalTransitionId ++ ","
    ++ "\"source_instr\":" ++ jsonStr e.sourceInstr ++ ","
    ++ "\"source_label\":" ++ jsonStr e.sourceLabel ++ ","
    ++ "\"sem_key\":" ++ renderSemKey e.semKey ++ ","
    ++ "\"priority\":" ++ jsonNat e.priority ++ ","
    ++ "\"legacy_rule_id\":" ++ jsonOptStr e.legacyRuleId
  ++ "}"

def TransitionPlanArtifact.renderJson (a : TransitionPlanArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"transitions\":[" ++ String.intercalate "," (norm.transitions.map renderEntry) ++ "]"
  ++ "}"

private def isRuleId (rule : String) : Bool :=
  if !rule.startsWith "R" then
    false
  else
    let tail := (rule.drop 1).toString
    !tail.isEmpty && tail.toList.all Char.isDigit

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
    let rendered := k.contracts.map renderContract
    if rendered.length == rendered.eraseDups.length then
      []
    else
      [s!"{tid}: sem_key.contracts contains duplicates"]
  classErrs ++ kindErrs ++ guardErrs ++ effectErrs ++ contractsErrs

private def lintEntry (e : TransitionPlanEntry) : List String :=
  let idErrs :=
    if e.logicalTransitionId.isEmpty then
      ["logical_transition_id must be non-empty"]
    else []
  let sourceErrs :=
    if e.sourceInstr.isEmpty then
      [s!"{e.logicalTransitionId}: source_instr must be non-empty"]
    else if !(e.sourceInstr.startsWith "C_") then
      [s!"{e.logicalTransitionId}: source_instr must start with C_, got: {e.sourceInstr}"]
    else []
  let legacyErrs :=
    match e.legacyRuleId with
    | some rid =>
        if isRuleId rid then [] else [s!"{e.logicalTransitionId}: invalid legacy_rule_id '{rid}'"]
    | none => []
  idErrs ++ sourceErrs ++ legacyErrs ++ lintSemKey e.logicalTransitionId e.semKey

def TransitionPlanArtifact.lintErrors (a : TransitionPlanArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 1 then
      [s!"schema_version must be >= 1, got {norm.schemaVersion}"]
    else []
  let dialectErrs :=
    if norm.dialect.isEmpty then
      ["dialect must be non-empty"]
    else []
  let transitionErrs :=
    if norm.transitions.isEmpty then
      ["transitions cannot be empty"]
    else []
  let dupIdErrs :=
    let ids := norm.transitions.map (·.logicalTransitionId)
    if ids.length == ids.eraseDups.length then
      []
    else
      ["logical_transition_id values must be unique"]
  schemaErrs ++ dialectErrs ++ transitionErrs ++ dupIdErrs
    ++ (norm.transitions.map lintEntry).foldl (· ++ ·) []

def TransitionPlanArtifact.isLintClean (a : TransitionPlanArtifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def TransitionPlanArtifact.checksum (a : TransitionPlanArtifact) : UInt64 :=
  checksumText a.renderJson

def TransitionPlanArtifact.checksumString (a : TransitionPlanArtifact) : String :=
  toString a.checksum

def TransitionPlanArtifact.hasContract
    (a : TransitionPlanArtifact)
    (logicalTransitionId : String)
    (contract : TransitionContract) : Bool :=
  match (normalizeArtifact a).transitions.find? (fun t => t.logicalTransitionId == logicalTransitionId) with
  | some t => t.semKey.contracts.contains contract
  | none => false

def TransitionPlanArtifact.forSourceInstr (a : TransitionPlanArtifact) (sourceInstr : String) :
    List TransitionPlanEntry :=
  (normalizeArtifact a).transitions.filter (fun t => t.sourceInstr == sourceInstr)

def TransitionPlanArtifact.onlyLegacyRuleIds? (a : TransitionPlanArtifact) :
    Option (List String) :=
  let rec go (xs : List TransitionPlanEntry) (acc : List String) : Option (List String) :=
    match xs with
    | [] => some (acc.reverse)
    | x :: rest =>
        match x.legacyRuleId with
        | some rid => go rest (rid :: acc)
        | none => none
  go (normalizeArtifact a).transitions []

end MeTTailCore.MeTTaIL.TransitionPlan
