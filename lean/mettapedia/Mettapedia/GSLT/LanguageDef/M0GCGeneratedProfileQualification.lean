import Lean.Data.Json.Parser
import MeTTailCore.Crypto.SHA256
import Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy

/-!
# Qualification of one generated M0GC profile

This module independently parses an authored applicative rule profile and the
physical tables emitted for the current M0GC C checker.  Qualification checks
that the two artifacts name the same semantic coordinates, recomputes their
SHA-256 identities, validates the authored calculus, and requires every
physical rule index to decode to the independently compiled source rule.

Maturity boundary: this is a fully connected qualification proof of concept
for the selected 62-rule semantic-softtype profile.  The parser/theorem seam is
intended to survive replacement, but the JSON envelope, flat node/child
arrays, numeric widths, FNV rule fingerprints, and bounded applicative rule
fragment are not claimed to be an endgame-optimal or universal NIK format.
In particular, this module qualifies a custom M0GC artifact, not official MM0
MMB bytes and not a terminal NIK host.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification

open Lean
open MeTTailCore.Crypto.SHA256
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat

def sourceFormat : String := "softtypes-ir-v1"

def physicalFormat : String := "mm0-gslt-profile-v1"

/-! ## Authored applicative source -/

structure SourceJudgment where
  head : String
  arguments : List Pattern
deriving DecidableEq, Repr

structure SourceRule where
  id : String
  formals : List String
  premises : List SourceJudgment
  conclusion : SourceJudgment
deriving DecidableEq, Repr

def SourceJudgment.toPattern (judgment : SourceJudgment) : Pattern :=
  .apply judgment.head judgment.arguments

def SourceRule.toRuleSchema (rule : SourceRule) : RuleSchema where
  id := ⟨rule.id⟩
  metavariables := rule.formals.map fun name => (name, 0)
  premises := rule.premises.map SourceJudgment.toPattern
  conclusion := rule.conclusion.toPattern

private def quoteJsonString (value : String) : String :=
  (Json.str value).compress

mutual

private def canonicalTermJson : Pattern → String
  | .fvar name =>
      "{\"var\":" ++ quoteJsonString name ++ "}"
  | .apply head arguments =>
      "{\"app\":" ++ quoteJsonString head ++
        ",\"args\":[" ++
        String.intercalate "," (canonicalTermJsonList arguments) ++
        "]}"
  | _ => "null"
termination_by pattern => sizeOf pattern

private def canonicalTermJsonList : List Pattern → List String
  | [] => []
  | pattern :: patterns =>
      canonicalTermJson pattern :: canonicalTermJsonList patterns
termination_by patterns => sizeOf patterns

end

def SourceJudgment.canonicalJson (judgment : SourceJudgment) : String :=
  "{\"args\":[" ++
    String.intercalate "," (judgment.arguments.map canonicalTermJson) ++
    "],\"head\":" ++ quoteJsonString judgment.head ++ "}"

def SourceRule.canonicalJson (rule : SourceRule) : String :=
  "{\"conclusion\":" ++ rule.conclusion.canonicalJson ++
    ",\"formals\":[" ++
    String.intercalate "," (rule.formals.map quoteJsonString) ++
    "],\"id\":" ++ quoteJsonString rule.id ++
    ",\"premises\":[" ++
    String.intercalate "," (rule.premises.map SourceJudgment.canonicalJson) ++
    "]}"

/-- Exact rule fingerprint consumed by the current generated C table. -/
def SourceRule.fingerprint (rule : SourceRule) : UInt64 :=
  fnv1a64 rule.canonicalJson.toUTF8.toList

private def constructorDeclaration (entry : String × Nat) : GrammarRule where
  label := entry.1
  category := "Datum"
  params := (List.range entry.2).map fun index =>
    .simple s!"argument{index}" (.base "Datum")
  syntaxPattern := []

structure SourceArtifact where
  format : String
  constructors : List (String × Nat)
  judgments : List (String × Nat)
  rules : List SourceRule
  coordinatesCanonical : String
deriving DecidableEq, Repr

def SourceArtifact.expectedSymbols (source : SourceArtifact) :
    List SymbolProfile :=
  (source.constructors ++ source.judgments).mergeSort
      (fun first second => first.1 <= second.1) |>.map fun entry =>
    { name := entry.1, arity := UInt16.ofNat entry.2 }

def SourceArtifact.definition (source : SourceArtifact) :
    CalculusLanguageDef where
  toLanguageDef :=
    { name := "M0GC semantic-softtype source profile"
      types := [TypeDecl.plain "Datum"]
      terms := source.constructors.map constructorDeclaration
      equations := []
      rewrites := [] }
  judgments := source.judgments.map fun entry =>
    { head := entry.1, arity := entry.2 }
  rules := source.rules.map SourceRule.toRuleSchema

/-! ## Exact physical artifact -/

structure PhysicalArtifact where
  format : String
  coordinatesCanonical : String
  recordedProfileDigest : String
  computedProfileDigest : String
  recordedSourceDigest : String
  computedSourceDigest : String
  profile : RuntimeProfile
  tables : RuleTables
deriving DecidableEq, Repr

private def templateLayoutCanonicalLoop (profile : RuntimeProfile)
    (children : List UInt32) : List TemplateNode → Nat → Nat → Bool
  | [], _, childOffset => childOffset == children.length
  | node :: nodes, nodeIndex, childOffset =>
      let startsHere := node.childStart.toNat == childOffset
      if node.kind = variableKind then
        startsHere && node.arity.toNat == 0 &&
          templateLayoutCanonicalLoop profile children nodes
            (nodeIndex + 1) childOffset
      else if node.kind = applicationKind then
        match profile.symbols[node.value.toNat]?,
            checkedSlice? children childOffset node.arity.toNat with
        | some symbol, some roots =>
            startsHere && node.arity = symbol.arity &&
              roots.all (fun root => root.toNat < nodeIndex) &&
              templateLayoutCanonicalLoop profile children nodes
                (nodeIndex + 1) (childOffset + node.arity.toNat)
        | _, _ => false
      else false

/-- The present flat template arrays are chronological, exactly sliced, and
free of unused trailing child cells.  This is a qualification property of the
current connected PoC layout, not a requirement on future optimized layouts. -/
def PhysicalArtifact.templateLayoutCanonical
    (physical : PhysicalArtifact) : Bool :=
  templateLayoutCanonicalLoop physical.profile
    physical.tables.templates.children physical.tables.templates.nodes.toList 0 0

private def ruleLayoutCanonicalLoop (premiseRootCount : Nat) :
    List RuleProfile → List RuleLayout → Nat → Bool
  | [], [], offset => offset == premiseRootCount
  | rule :: rules, layout :: layouts, offset =>
      layout.premiseStart.toNat == offset &&
        ruleLayoutCanonicalLoop premiseRootCount rules layouts
          (offset + rule.premiseCount.toNat)
  | _, _, _ => false

/-- The current separate rule-layout and premise-root tables form one exact
contiguous walk.  A future layout may discharge the decoder theorem by a
different organization. -/
def PhysicalArtifact.ruleLayoutCanonical
    (physical : PhysicalArtifact) : Bool :=
  ruleLayoutCanonicalLoop physical.tables.premiseRoots.length
    physical.profile.rules.toList physical.tables.layouts.toList 0

structure Candidate where
  source : SourceArtifact
  physical : PhysicalArtifact
deriving DecidableEq, Repr

def Candidate.decodeFuel (_candidate : Candidate) : Nat :=
  nativeMatcherFuel

/-- One source rule and one physical rule index agree in identity, arities,
fingerprint, and complete logical template. -/
def ExactRuleAgreement (candidate : Candidate) (index : Nat) : Prop :=
  match candidate.source.rules[index]?,
      candidate.physical.profile.rules[index]? with
  | some sourceRule, some physicalRule =>
      physicalRule.ruleId = sourceRule.toRuleSchema.id ∧
        physicalRule.argumentCount = UInt16.ofNat sourceRule.formals.length ∧
        physicalRule.premiseCount = UInt16.ofNat sourceRule.premises.length ∧
        physicalRule.fingerprint = sourceRule.fingerprint ∧
        (compileRuleTemplate? sourceRule.toRuleSchema).isSome = true ∧
        decodeRuleTemplate? candidate.physical.profile
            candidate.physical.tables candidate.decodeFuel
            (UInt16.ofNat index) =
          compileRuleTemplate? sourceRule.toRuleSchema
  | _, _ => False

instance (candidate : Candidate) (index : Nat) :
    Decidable (ExactRuleAgreement candidate index) := by
  unfold ExactRuleAgreement
  cases candidate.source.rules[index]? <;>
    cases candidate.physical.profile.rules[index]? <;>
      infer_instance

def Candidate.allRulesAgree (candidate : Candidate) : Bool :=
  (List.range candidate.source.rules.length).all fun index =>
    decide (ExactRuleAgreement candidate index)

/-- Executable conjunction behind the proof-carrying qualification boundary.
The per-rule decision is placed first so its theorem can project it without
depending on the diagnostic ordering of the other gates. -/
def Candidate.connected (candidate : Candidate) : Bool :=
  candidate.allRulesAgree && (
    decide (candidate.source.format = sourceFormat) &&
    decide (candidate.physical.format = physicalFormat) &&
    decide (candidate.source.coordinatesCanonical =
      candidate.physical.coordinatesCanonical) &&
    decide (candidate.physical.recordedProfileDigest =
      candidate.physical.computedProfileDigest) &&
    decide (candidate.physical.recordedSourceDigest =
      candidate.physical.computedSourceDigest) &&
    candidate.source.definition.isValid &&
    decide (candidate.physical.profile.symbols.toList =
      candidate.source.expectedSymbols) &&
    decide (candidate.physical.profile.rules.size =
      candidate.source.rules.length) &&
    decide (candidate.physical.tables.layouts.size =
      candidate.source.rules.length) &&
    decide (candidate.source.rules.length < UInt16.size) &&
    candidate.physical.templateLayoutCanonical &&
    candidate.physical.ruleLayoutCanonical)

/-- Complete proof-carrying qualification boundary. -/
def Candidate.Connected (candidate : Candidate) : Prop :=
  candidate.connected = true

instance (candidate : Candidate) : Decidable candidate.Connected := by
  unfold Candidate.Connected
  infer_instance

/-- A connected qualification entails the full source/physical agreement at
every selected rule index, not merely agreement on the examples replayed by C. -/
theorem exactRuleAgreement_of_connected
    {candidate : Candidate} (connected : candidate.Connected)
    {index : Nat} (inRange : index < candidate.source.rules.length) :
    ExactRuleAgreement candidate index := by
  have everyRule : candidate.allRulesAgree = true := by
    unfold Candidate.Connected Candidate.connected at connected
    exact (Bool.and_eq_true_iff.mp connected).1
  have member : index ∈ List.range candidate.source.rules.length :=
    List.mem_range.mpr inRange
  have checked :=
    (List.all_eq_true.mp everyRule) index member
  exact of_decide_eq_true checked

/-- Qualification validates the independently reconstructed source calculus,
not merely the generated physical tables. -/
theorem sourceDefinition_valid_of_connected
    {candidate : Candidate} (connected : candidate.Connected) :
    candidate.source.definition.isValid = true := by
  unfold Candidate.Connected Candidate.connected at connected
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at connected
  aesop

/-- A physical rule lookup accepted by a connected profile is necessarily in
range for the independently parsed source rule list. -/
theorem physical_rule_index_lt_source_of_lookup
    {candidate : Candidate} (connected : candidate.Connected)
    {index : Nat} {physicalRule : RuleProfile}
    (physicalAtIndex :
      candidate.physical.profile.rules[index]? = some physicalRule) :
    index < candidate.source.rules.length := by
  have inPhysicalRange : index < candidate.physical.profile.rules.size :=
    (Array.getElem?_eq_some_iff.mp physicalAtIndex).choose
  have sameSize : candidate.physical.profile.rules.size =
      candidate.source.rules.length := by
    unfold Candidate.Connected Candidate.connected at connected
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at connected
    aesop
  simpa [sameSize] using inPhysicalRange

def Candidate.validatedSource (candidate : Candidate)
    (connected : candidate.Connected) : ValidatedCalculusLanguageDef :=
  ⟨candidate.source.definition,
    sourceDefinition_valid_of_connected connected⟩

/-- Every selected physical rule has an authored source rule at the same
index, compiles successfully, decodes to that exact compiled template, and is
the rule returned by the validated source calculus. -/
theorem selected_rule_decodes_to_validated_source
    {candidate : Candidate} (connected : candidate.Connected)
    {index : Nat} (inRange : index < candidate.source.rules.length) :
    ∃ sourceRule template,
      candidate.source.rules[index]? = some sourceRule ∧
      compileRuleTemplate? sourceRule.toRuleSchema = some template ∧
      decodeRuleTemplate? candidate.physical.profile
          candidate.physical.tables candidate.decodeFuel
          (UInt16.ofNat index) = some template ∧
      (candidate.validatedSource connected).1.lookupRule?
          sourceRule.toRuleSchema.id = some sourceRule.toRuleSchema := by
  let sourceRule := candidate.source.rules[index]
  have sourceAtIndex : candidate.source.rules[index]? = some sourceRule :=
    List.getElem?_eq_getElem inRange
  have agreement := exactRuleAgreement_of_connected connected inRange
  unfold ExactRuleAgreement at agreement
  rw [sourceAtIndex] at agreement
  cases physicalAtIndex : candidate.physical.profile.rules[index]? with
  | none =>
      simp [physicalAtIndex] at agreement
  | some physicalRule =>
      simp only [physicalAtIndex] at agreement
      rcases agreement with
        ⟨_, _, _, _, compiledSome, decodedEqualsCompiled⟩
      cases compiled : compileRuleTemplate? sourceRule.toRuleSchema with
      | none => simp [compiled] at compiledSome
      | some template =>
          have decoded :
              decodeRuleTemplate? candidate.physical.profile
                  candidate.physical.tables candidate.decodeFuel
                  (UInt16.ofNat index) = some template := by
            simpa [compiled] using decodedEqualsCompiled
          have sourceMembership : sourceRule ∈ candidate.source.rules :=
            List.getElem_mem inRange
          have schemaMembership :
              sourceRule.toRuleSchema ∈
                (candidate.validatedSource connected).1.rules := by
            exact List.mem_map_of_mem sourceMembership
          have lookup := lookupRule?_eq_some_of_mem
            (candidate.validatedSource connected) schemaMembership
          exact
            ⟨sourceRule, template, sourceAtIndex, compiled, decoded, lookup⟩

/-- A selected physical rule exposes all metadata needed by the raw replay
simulation, together with the exact compiled source template and validated
source lookup. -/
theorem selected_physical_rule_qualifies
    {candidate : Candidate} (connected : candidate.Connected)
    {index : Nat} {physicalRule : RuleProfile}
    (physicalAtIndex :
      candidate.physical.profile.rules[index]? = some physicalRule) :
    ∃ sourceRule template,
      candidate.source.rules[index]? = some sourceRule ∧
      physicalRule.ruleId = sourceRule.toRuleSchema.id ∧
      physicalRule.argumentCount =
        UInt16.ofNat sourceRule.formals.length ∧
      physicalRule.premiseCount =
        UInt16.ofNat sourceRule.premises.length ∧
      physicalRule.fingerprint = sourceRule.fingerprint ∧
      compileRuleTemplate? sourceRule.toRuleSchema = some template ∧
      decodeRuleTemplate? candidate.physical.profile
          candidate.physical.tables candidate.decodeFuel
          (UInt16.ofNat index) = some template ∧
      (candidate.validatedSource connected).1.lookupRule?
          sourceRule.toRuleSchema.id = some sourceRule.toRuleSchema := by
  have inRange := physical_rule_index_lt_source_of_lookup connected physicalAtIndex
  obtain ⟨sourceRule, template, sourceAtIndex, compiled, decoded, lookup⟩ :=
    selected_rule_decodes_to_validated_source connected inRange
  have agreement := exactRuleAgreement_of_connected connected inRange
  unfold ExactRuleAgreement at agreement
  rw [sourceAtIndex, physicalAtIndex] at agreement
  simp only at agreement
  rcases agreement with
    ⟨ruleIdEq, argumentCountEq, premiseCountEq, fingerprintEq, _, _⟩
  exact ⟨sourceRule, template, sourceAtIndex, ruleIdEq, argumentCountEq,
    premiseCountEq, fingerprintEq, compiled, decoded, lookup⟩

/-! ## JSON parsers -/

private def parseStringField (json : Json) (field : String) :
    Except String String :=
  json.getObjVal? field >>= Json.getStr?

private def parseNatField (json : Json) (field : String) :
    Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def parseArrayField (json : Json) (field : String) :
    Except String (Array Json) :=
  json.getObjVal? field >>= Json.getArr?

private def parseStringArrayField (json : Json) (field : String) :
    Except String (List String) := do
  let values ← parseArrayField json field
  values.toList.mapM Json.getStr?

private def parseNatArrayField (json : Json) (field : String) :
    Except String (List Nat) := do
  let values ← parseArrayField json field
  values.toList.mapM Json.getNat?

private def toUInt8Checked (context : String) (value : Nat) :
    Except String UInt8 :=
  if value < UInt8.size then pure (UInt8.ofNat value)
  else throw s!"{context} exceeds UInt8"

private def toUInt16Checked (context : String) (value : Nat) :
    Except String UInt16 :=
  if value < UInt16.size then pure (UInt16.ofNat value)
  else throw s!"{context} exceeds UInt16"

private def toUInt32Checked (context : String) (value : Nat) :
    Except String UInt32 :=
  if value < UInt32.size then pure (UInt32.ofNat value)
  else throw s!"{context} exceeds UInt32"

private def toUInt64Checked (context : String) (value : Nat) :
    Except String UInt64 :=
  if value < UInt64.size then pure (UInt64.ofNat value)
  else throw s!"{context} exceeds UInt64"

private def parseArityObject (json : Json) :
    Except String (List (String × Nat)) := do
  let entries ← json.getObj?
  entries.toList.mapM fun entry => do
    let arity ← entry.2.getNat?
    if arity < UInt16.size then pure (entry.1, arity)
    else throw s!"arity for {entry.1} exceeds UInt16"

private def parseSourceTermWithFuel : Nat → Json → Except String Pattern
  | 0, _ => throw "source term nesting exceeds JSON size bound"
  | fuel + 1, json => do
      match json.getObjVal? "var", json.getObjVal? "app" with
      | .ok variableJson, .error _ =>
          pure (.fvar (← variableJson.getStr?))
      | .error _, .ok applicationJson =>
          let head ← applicationJson.getStr?
          let arguments ← parseArrayField json "args"
          pure (.apply head
            (← arguments.toList.mapM (parseSourceTermWithFuel fuel)))
      | .ok _, .ok _ => throw "source term cannot be both variable and application"
      | .error _, .error _ => throw "source term requires var or app"

private def parseSourceTerm (json : Json) : Except String Pattern :=
  -- Qualification-path bound: JSON nesting is strictly smaller than its
  -- compressed textual length.  This deliberately favors a simple total
  -- parser over endgame parser efficiency; a production streaming reader may
  -- replace it while preserving `Candidate.Connected`.
  parseSourceTermWithFuel (json.compress.length + 1) json

private def parseSourceJudgment (json : Json) :
    Except String SourceJudgment := do
  let head ← parseStringField json "head"
  let arguments ← parseArrayField json "args"
  pure { head, arguments := ← arguments.toList.mapM parseSourceTerm }

private def parseSourceRule (json : Json) : Except String SourceRule := do
  let id ← parseStringField json "id"
  let formals ← parseStringArrayField json "formals"
  let premises ← parseArrayField json "premises"
  let conclusion ← json.getObjVal? "conclusion" >>= parseSourceJudgment
  pure
    { id
      formals
      premises := ← premises.toList.mapM parseSourceJudgment
      conclusion }

private def semanticCoordinatesCanonical (json : Json) :
    Except String String := do
  let constructors ← json.getObjVal? "constructors"
  let judgments ← json.getObjVal? "judgments"
  let rules ← json.getObjVal? "rules"
  pure <| (Json.mkObj
    [("constructors", constructors), ("judgments", judgments),
     ("rules", rules)]).compress

def parseSourceArtifactJson (json : Json) : Except String SourceArtifact := do
  let format ← parseStringField json "format"
  let constructorJson ← json.getObjVal? "constructors"
  let judgmentJson ← json.getObjVal? "judgments"
  let ruleJson ← parseArrayField json "rules"
  let constructors ← parseArityObject constructorJson
  let judgments ← parseArityObject judgmentJson
  let constructorNames := constructors.map Prod.fst
  let judgmentNames := judgments.map Prod.fst
  if (constructorNames ++ judgmentNames).eraseDups.length !=
      constructorNames.length + judgmentNames.length then
    throw "constructor and judgment names must be globally distinct"
  pure
    { format
      constructors
      judgments
      rules := ← ruleJson.toList.mapM parseSourceRule
      coordinatesCanonical := ← semanticCoordinatesCanonical json }

private structure ParsedRuleRecord where
  name : String
  argumentCount : UInt16
  premiseCount : UInt16
  premiseStart : UInt32
  conclusion : UInt32
  fingerprint : UInt64

private def parseRuleRecord (json : Json) :
    Except String ParsedRuleRecord := do
  pure
    { name := ← parseStringField json "name"
      argumentCount := ← toUInt16Checked "rule arg_count"
        (← parseNatField json "arg_count")
      premiseCount := ← toUInt16Checked "rule prem_count"
        (← parseNatField json "prem_count")
      premiseStart := ← toUInt32Checked "rule prem_start"
        (← parseNatField json "prem_start")
      conclusion := ← toUInt32Checked "rule conclusion"
        (← parseNatField json "conclusion")
      fingerprint := ← toUInt64Checked "rule fingerprint"
        (← parseNatField json "fingerprint") }

private def parseTemplateRecord (json : Json) :
    Except String TemplateNode := do
  pure
    { kind := ← toUInt8Checked "template kind"
        (← parseNatField json "kind")
      value := ← toUInt16Checked "template value"
        (← parseNatField json "value")
      arity := ← toUInt16Checked "template arity"
        (← parseNatField json "arity")
      childStart := ← toUInt32Checked "template child_start"
        (← parseNatField json "child_start") }

private def zipSymbols (names : List String) (arities : List Nat) :
    Except String (List SymbolProfile) :=
  match names, arities with
  | [], [] => pure []
  | name :: names, arity :: arities => do
      let tail ← zipSymbols names arities
      pure ({ name, arity := ← toUInt16Checked "symbol arity" arity } :: tail)
  | _, _ => throw "symbol name and arity arrays have different lengths"

private def hexNibble? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' | 'A' => some 10
  | 'b' | 'B' => some 11 | 'c' | 'C' => some 12
  | 'd' | 'D' => some 13 | 'e' | 'E' => some 14
  | 'f' | 'F' => some 15 | _ => none

private def parseHexBytesAux : List Char → Except String (List UInt8)
  | [] => pure []
  | high :: low :: characters => do
      let highValue ← highNibble? high
      let lowValue ← highNibble? low
      let tail ← parseHexBytesAux characters
      pure (UInt8.ofNat (16 * highValue + lowValue) :: tail)
  | [_] => throw "hex digest has odd length"
where
  highNibble? (character : Char) : Except String Nat :=
    match hexNibble? character with
    | some value => pure value
    | none => throw s!"invalid hex digit: {character}"

private def parseDigest (value : String) : Except String (List UInt8) := do
  let bytes ← parseHexBytesAux value.toList
  if bytes.length = 32 then pure bytes
  else throw "digest must contain exactly 32 bytes"

private def profileObjectCanonical (json : Json) : Except String String := do
  let format ← json.getObjVal? "format"
  let hostPackage ← json.getObjVal? "host_package"
  let componentSha256 ← json.getObjVal? "component_sha256"
  let constructors ← json.getObjVal? "constructors"
  let judgments ← json.getObjVal? "judgments"
  let rules ← json.getObjVal? "rules"
  pure <| (Json.mkObj
    [("format", format), ("host_package", hostPackage),
     ("component_sha256", componentSha256),
     ("constructors", constructors), ("judgments", judgments),
     ("rules", rules)]).compress

def parsePhysicalArtifactJson (sourceBytes : ByteArray) (json : Json) :
    Except String PhysicalArtifact := do
  let format ← parseStringField json "format"
  let recordedProfileDigest ← parseStringField json "profile_sha256"
  let recordedSourceDigest ← parseStringField json "source_sha256"
  let profileCanonical ← profileObjectCanonical json
  let computedProfileDigest :=
    toHexString (sha256Bytes profileCanonical.toUTF8)
  let computedSourceDigest := toHexString (sha256Bytes sourceBytes)
  let symbols ← zipSymbols
    (← parseStringArrayField json "symbols")
    (← parseNatArrayField json "symbol_arities")
  let templateJson ← parseArrayField json "template_records"
  let templateNodes ← templateJson.toList.mapM parseTemplateRecord
  let templateChildren ←
    (← parseNatArrayField json "template_children").mapM fun value =>
      toUInt32Checked "template child" value
  let rulePremises ←
    (← parseNatArrayField json "rule_premises").mapM fun value =>
      toUInt32Checked "rule premise root" value
  let ruleJson ← parseArrayField json "rule_records"
  let ruleRecords ← ruleJson.toList.mapM parseRuleRecord
  let profileDigest ← parseDigest recordedProfileDigest
  let sourceDigest ← parseDigest recordedSourceDigest
  let profile : RuntimeProfile :=
    { profileDigest
      sourceDigest
      symbols := symbols.toArray
      rules := (ruleRecords.map fun rule =>
        { ruleId := ⟨rule.name⟩
          argumentCount := rule.argumentCount
          premiseCount := rule.premiseCount
          fingerprint := rule.fingerprint }).toArray }
  let tables : RuleTables :=
    { templates :=
        { nodes := templateNodes.toArray
          children := templateChildren }
      premiseRoots := rulePremises
      layouts := (ruleRecords.map fun rule =>
        { premiseStart := rule.premiseStart
          conclusion := rule.conclusion }).toArray }
  pure
    { format
      coordinatesCanonical := ← semanticCoordinatesCanonical json
      recordedProfileDigest
      computedProfileDigest
      recordedSourceDigest
      computedSourceDigest
      profile
      tables }

def parseCandidate (sourceText physicalText : String)
    (sourceBytes : ByteArray) : Except String Candidate := do
  let sourceJson ← Json.parse sourceText
  let physicalJson ← Json.parse physicalText
  pure
    { source := ← parseSourceArtifactJson sourceJson
      physical := ← parsePhysicalArtifactJson sourceBytes physicalJson }

def Candidate.failures (candidate : Candidate) : List String :=
  [ if candidate.source.format = sourceFormat then none
      else some "source format"
  , if candidate.physical.format = physicalFormat then none
      else some "physical format"
  , if candidate.source.coordinatesCanonical =
        candidate.physical.coordinatesCanonical then none
      else some "semantic coordinates"
  , if candidate.physical.recordedProfileDigest =
        candidate.physical.computedProfileDigest then none
      else some "profile digest"
  , if candidate.physical.recordedSourceDigest =
        candidate.physical.computedSourceDigest then none
      else some "source digest"
  , if candidate.source.definition.isValid = true then none
      else some "source calculus validation"
  , if candidate.physical.profile.symbols.toList =
        candidate.source.expectedSymbols then none
      else some "symbol table"
  , if candidate.physical.profile.rules.size = candidate.source.rules.length
      then none else some "rule count"
  , if candidate.physical.tables.layouts.size = candidate.source.rules.length
      then none else some "layout count"
  , if candidate.source.rules.length < UInt16.size then none
      else some "rule index width"
  , if candidate.physical.templateLayoutCanonical = true then none
      else some "template layout"
  , if candidate.physical.ruleLayoutCanonical = true then none
      else some "rule layout"
  , if candidate.allRulesAgree = true then none
      else some "source/physical rule agreement" ].filterMap id

/-- Parse both authorities and return their conjunction only after every
identity, validation, layout, and rule-decoding obligation computes true. -/
def qualify (sourceText physicalText : String) (sourceBytes : ByteArray) :
    Except String { candidate : Candidate // candidate.Connected } := do
  let candidate ← parseCandidate sourceText physicalText sourceBytes
  if connected : candidate.Connected then pure ⟨candidate, connected⟩
  else
    throw <| "M0GC profile qualification failed: " ++
      String.intercalate ", " candidate.failures

/-! ## Executable negative mutation -/

private def flipFirstRuleFingerprint : List RuleProfile → List RuleProfile
  | [] => []
  | rule :: rules =>
      { rule with fingerprint := rule.fingerprint ^^^ 1 } :: rules

/-- Change only the first physical rule fingerprint.  The qualification tool
uses this as a negative canary after accepting the exact artifact. -/
def Candidate.mutateFirstRuleFingerprint (candidate : Candidate) : Candidate :=
  { candidate with
    physical :=
      { candidate.physical with
        profile :=
          { candidate.physical.profile with
            rules :=
              (flipFirstRuleFingerprint
                candidate.physical.profile.rules.toList).toArray } } }

#print axioms exactRuleAgreement_of_connected
#print axioms sourceDefinition_valid_of_connected
#print axioms selected_rule_decodes_to_validated_source
#print axioms physical_rule_index_lt_source_of_lookup
#print axioms selected_physical_rule_qualifies

end Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
