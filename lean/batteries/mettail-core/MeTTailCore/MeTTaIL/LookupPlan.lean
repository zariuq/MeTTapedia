namespace MeTTailCore.MeTTaIL.LookupPlan

inductive UsageKind where
  | enumerate
  | exists
  | negatedExists
  | aggregateInput
deriving Repr, DecidableEq, BEq

inductive BindingMode where
  | bound
  | free
deriving Repr, DecidableEq, BEq

structure SignatureArg where
  position : Nat
  mode : BindingMode
deriving Repr, DecidableEq, BEq

structure DemandSignature where
  relation : String
  logicalRelationId : String := ""
  scopeSignature : String := ""
  arity : Nat
  args : List SignatureArg
  usageKind : UsageKind
  negatedTarget : Option String := none
  inRecursiveScc : Bool := false
  hotPath : Bool := false
deriving Repr, DecidableEq, BEq

structure LookupContract where
  noFalseNegatives : Bool := true
  exactResult : Bool := false
  stratifiedNegationSafe : Bool := true
deriving Repr, DecidableEq, BEq

structure LookupFamilyPlan where
  family : String
  logicalRelationId : String := ""
  factRelation : String
  rawRelation : String
  hasRelation : String
  resultRelation : Option String := none
  queryArity : Nat
  payloadArity : Nat := 1
  keyPositions : List Nat := []
  demand : List DemandSignature := []
  contracts : LookupContract := {}
deriving Repr, DecidableEq, BEq

structure LookupPlanArtifact where
  schemaVersion : Nat := 2
  dialect : String
  families : List LookupFamilyPlan
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def sortNatList (xs : List Nat) : List Nat :=
  (xs.toArray.qsort (fun a b => a < b)).toList

private def SignatureArg.sortKey (arg : SignatureArg) : String :=
  s!"{arg.position}:{match arg.mode with | .bound => "b" | .free => "f"}"

private def normalizeSignatureArgs (xs : List SignatureArg) : List SignatureArg :=
  sortListByKey xs SignatureArg.sortKey

private def defaultScopeSignature (sig : DemandSignature) : String :=
  let args := normalizeSignatureArgs sig.args
  if args.isEmpty then
    "all_free"
  else
    let parts := args.map fun a =>
      let mode :=
        match a.mode with
        | .bound => "b"
        | .free => "f"
      s!"{mode}{a.position}"
    String.intercalate "+" parts

private def normalizeDemandSignature (sig : DemandSignature) : DemandSignature :=
  let logicalId :=
    if sig.logicalRelationId.isEmpty then sig.relation else sig.logicalRelationId
  let scopeSig :=
    if sig.scopeSignature.isEmpty then defaultScopeSignature sig else sig.scopeSignature
  { sig with
    logicalRelationId := logicalId
    scopeSignature := scopeSig
    args := normalizeSignatureArgs sig.args
  }

private def normalizeFamily (f : LookupFamilyPlan) : LookupFamilyPlan :=
  let logicalId :=
    if f.logicalRelationId.isEmpty then f.family else f.logicalRelationId
  let demand := sortListByKey (f.demand.map normalizeDemandSignature)
    (fun d => s!"{d.logicalRelationId}:{d.scopeSignature}:{d.relation}")
  { f with
    logicalRelationId := logicalId
    keyPositions := sortNatList f.keyPositions
    demand := demand
  }

private def normalizeArtifact (a : LookupPlanArtifact) : LookupPlanArtifact :=
  { a with
    families := sortListByKey (a.families.map normalizeFamily)
      (fun f => s!"{f.logicalRelationId}:{f.family}") }

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

private def renderBindingMode : BindingMode → String
  | .bound => "bound"
  | .free => "free"

private def renderUsageKind : UsageKind → String
  | .enumerate => "enumerate"
  | .exists => "exists"
  | .negatedExists => "negated_exists"
  | .aggregateInput => "aggregate_input"

private def renderSignatureArg (arg : SignatureArg) : String :=
  "{"
    ++ "\"position\":" ++ jsonNat arg.position ++ ","
    ++ "\"mode\":" ++ jsonStr (renderBindingMode arg.mode)
  ++ "}"

private def renderDemandSignature (sig : DemandSignature) : String :=
  "{"
    ++ "\"relation\":" ++ jsonStr sig.relation ++ ","
    ++ "\"logical_relation_id\":" ++ jsonStr sig.logicalRelationId ++ ","
    ++ "\"scope_signature\":" ++ jsonStr sig.scopeSignature ++ ","
    ++ "\"arity\":" ++ jsonNat sig.arity ++ ","
    ++ "\"args\":[" ++ String.intercalate "," (sig.args.map renderSignatureArg) ++ "],"
    ++ "\"usage_kind\":" ++ jsonStr (renderUsageKind sig.usageKind) ++ ","
    ++ "\"negated_target\":" ++ jsonOptStr sig.negatedTarget ++ ","
    ++ "\"in_recursive_scc\":" ++ jsonBool sig.inRecursiveScc ++ ","
    ++ "\"hot_path\":" ++ jsonBool sig.hotPath
  ++ "}"

private def renderContract (c : LookupContract) : String :=
  "{"
    ++ "\"no_false_negatives\":" ++ jsonBool c.noFalseNegatives ++ ","
    ++ "\"exact_result\":" ++ jsonBool c.exactResult ++ ","
    ++ "\"stratified_negation_safe\":" ++ jsonBool c.stratifiedNegationSafe
  ++ "}"

private def renderFamily (f : LookupFamilyPlan) : String :=
  "{"
    ++ "\"family\":" ++ jsonStr f.family ++ ","
    ++ "\"logical_relation_id\":" ++ jsonStr f.logicalRelationId ++ ","
    ++ "\"fact_relation\":" ++ jsonStr f.factRelation ++ ","
    ++ "\"raw_relation\":" ++ jsonStr f.rawRelation ++ ","
    ++ "\"has_relation\":" ++ jsonStr f.hasRelation ++ ","
    ++ "\"result_relation\":" ++ jsonOptStr f.resultRelation ++ ","
    ++ "\"query_arity\":" ++ jsonNat f.queryArity ++ ","
    ++ "\"payload_arity\":" ++ jsonNat f.payloadArity ++ ","
    ++ "\"key_positions\":[" ++ String.intercalate "," (f.keyPositions.map jsonNat) ++ "],"
    ++ "\"demand\":[" ++ String.intercalate "," (f.demand.map renderDemandSignature) ++ "],"
    ++ "\"contracts\":" ++ renderContract f.contracts
  ++ "}"

def LookupPlanArtifact.renderJson (a : LookupPlanArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"families\":[" ++ String.intercalate "," (norm.families.map renderFamily) ++ "]"
  ++ "}"

private def lintNegatedDemand (fam : LookupFamilyPlan) (sig : DemandSignature) : List String :=
  match sig.usageKind with
  | .negatedExists =>
      match sig.negatedTarget with
      | none =>
          [s!"{fam.family}/{sig.logicalRelationId}: negated_exists requires negated_target={fam.hasRelation}"]
      | some target =>
          let wrongTarget :=
            if target == fam.hasRelation then [] else
              [s!"{fam.family}/{sig.logicalRelationId}: negated target must be has_relation ({fam.hasRelation}), got {target}"]
          let resultTarget :=
            match fam.resultRelation with
            | some resultRel =>
                if target == resultRel then
                  [s!"{fam.family}/{sig.logicalRelationId}: negation over result relation is forbidden ({resultRel}); negate has relation ({fam.hasRelation})"]
                else []
            | none => []
          wrongTarget ++ resultTarget
  | _ => []

private def lintFamily (fam : LookupFamilyPlan) : List String :=
  let idErrs :=
    if fam.logicalRelationId.isEmpty then
      [s!"{fam.family}: logical_relation_id must be non-empty"]
    else []
  let hasErrs :=
    if fam.hasRelation.isEmpty then
      [s!"{fam.family}: has_relation must be non-empty"]
    else []
  let familyErrs :=
    match fam.resultRelation with
    | some resultRel =>
        if resultRel == fam.hasRelation then
          [s!"{fam.family}: result_relation must differ from has_relation"]
        else []
    | none => []
  let demandErrs := (fam.demand.map (lintNegatedDemand fam)).foldl (· ++ ·) []
  idErrs ++ hasErrs ++ familyErrs ++ demandErrs

def LookupPlanArtifact.lintErrors (a : LookupPlanArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 2 then
      [s!"schema_version must be >= 2, got {norm.schemaVersion}"]
    else []
  schemaErrs ++ (norm.families.map lintFamily).foldl (· ++ ·) []

def LookupPlanArtifact.isLintClean (a : LookupPlanArtifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def LookupPlanArtifact.checksum (a : LookupPlanArtifact) : UInt64 :=
  checksumText a.renderJson

def LookupPlanArtifact.checksumString (a : LookupPlanArtifact) : String :=
  toString a.checksum

end MeTTailCore.MeTTaIL.LookupPlan
