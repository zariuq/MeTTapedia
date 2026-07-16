import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.OSLF.MeTTaIL.LogicSemantics

namespace Mettapedia.GSLT.LanguageDef.InferenceExtraction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LogicSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker

structure EvidenceProfile where
  checkHead : String
  okHead : String
  proofCategory : String
  evidenceCategory : String
  derivedHead : String := "$ld.derived"
  relationHeadPrefix : String := "$ld.rel."
deriving Repr, DecidableEq

def EvidenceProfile.derived (profile : EvidenceProfile) (evidence : Pattern) : Pattern :=
  .apply profile.derivedHead [evidence]

def EvidenceProfile.relationHead (profile : EvidenceProfile) (relation : String) : String :=
  profile.relationHeadPrefix ++ relation

def EvidenceProfile.relationJudgment (profile : EvidenceProfile)
    (relation : String) (arguments : List Pattern) : Pattern :=
  .apply (profile.relationHead relation) arguments

def findConstructor? (language : LanguageDef) (head : String) : Option GrammarRule :=
  language.terms.find? fun declaration => declaration.label == head

def evidenceArguments? (profile : EvidenceProfile) (language : LanguageDef) :
    Pattern → Option (List Pattern)
  | .apply head arguments => do
      let declaration ← findConstructor? language head
      guard (declaration.category == profile.proofCategory)
      guard (declaration.params.length == arguments.length)
      pure <| (arguments.zip declaration.params).filterMap fun (argument, parameter) =>
        if TermParam.typeExpr parameter == .base profile.evidenceCategory then
          some argument
        else
          none
  | _ => none

def sidePremiseJudgment? (profile : EvidenceProfile) : Premise → Option Pattern
  | .relationQuery relation arguments =>
      some (profile.relationJudgment relation arguments)
  | _ => none

/-- Proof-erased recognition used by presentation generation.  Keeping this
computational path separate from the dependent recognition certificate below
prevents proof terms from becoming part of generated presentation data. -/
def checkedInputProof? (profile : EvidenceProfile) : Pattern → Option Pattern
  | .apply head [proof] =>
      if head == profile.checkHead then some proof else none
  | _ => none

/-- Proof-erased successful-output recognition for presentation generation. -/
def checkedOutputResult? (profile : EvidenceProfile) : Pattern → Option Pattern
  | .apply head [result] =>
      if head == profile.okHead then some result else none
  | _ => none

@[simp] def metavariableOccurrenceEq (left right : String × Nat) : Bool :=
  left.1 == right.1 && left.2 == right.2

@[simp] def occurrenceContains (values : List (String × Nat))
    (value : String × Nat) : Bool :=
  match values with
  | [] => false
  | head :: tail =>
      metavariableOccurrenceEq value head || occurrenceContains tail value

@[simp] def occurrenceEraseDupsAux (seen : List (String × Nat)) :
    List (String × Nat) → List (String × Nat)
  | [] => []
  | head :: tail =>
      match occurrenceContains seen head with
      | true => occurrenceEraseDupsAux seen tail
      | false => head :: occurrenceEraseDupsAux (head :: seen) tail

@[simp] def occurrenceEraseDups (values : List (String × Nat)) :
    List (String × Nat) :=
  occurrenceEraseDupsAux [] values

@[simp] def occurrenceKeepIn (allowed : List (String × Nat)) :
    List (String × Nat) → List (String × Nat)
  | [] => []
  | head :: tail =>
      match occurrenceContains allowed head with
      | true => head :: occurrenceKeepIn allowed tail
      | false => occurrenceKeepIn allowed tail

@[simp] def occurrenceKeepOut (excluded : List (String × Nat)) :
    List (String × Nat) → List (String × Nat)
  | [] => []
  | head :: tail =>
      match occurrenceContains excluded head with
      | true => occurrenceKeepOut excluded tail
      | false => head :: occurrenceKeepOut excluded tail

/-- The single computational constructor for a generated inference schema. -/
def extractedSchema (profile : EvidenceProfile) (rule : RewriteRule)
    (evidencePremises sidePremises : List Pattern)
    (result : Pattern) : RuleSchema :=
  let conclusion := profile.derived result
  let draft : RuleSchema :=
    { id := { value := rule.name }
      metavariables := []
      premises := evidencePremises ++ sidePremises
      conclusion }
  let usedOccurrences := occurrenceEraseDups draft.occurrences
  let authoredOccurrences :=
    occurrenceEraseDups
      (patternMetavariableOccurrencesAt 0 rule.left ++
        patternMetavariableOccurrencesAt 0 rule.right)
  let authoredUsed := occurrenceKeepIn usedOccurrences authoredOccurrences
  let remaining := occurrenceKeepOut authoredUsed usedOccurrences
  { draft with metavariables := authoredUsed ++ remaining }

/-- Proof-erased rule extraction used by the generated presentation.  It has
the same recognizers and the same `extractedSchema` constructor as the
proof-producing `extractRule?` boundary below. -/
def extractRuleSchema? (profile : EvidenceProfile) (language : LanguageDef)
    (rule : RewriteRule) : Option RuleSchema := do
  let proof ← checkedInputProof? profile rule.left
  let result ← checkedOutputResult? profile rule.right
  let evidenceArguments ← evidenceArguments? profile language proof
  let evidencePremises := evidenceArguments.map profile.derived
  let sidePremises ← rule.premises.mapM (sidePremiseJudgment? profile)
  pure (extractedSchema profile rule evidencePremises sidePremises result)

structure RuleExtraction (profile : EvidenceProfile) where
  source : RewriteRule
  proof : Pattern
  result : Pattern
  evidencePremises : List Pattern
  sidePremises : List Pattern
  conclusion : Pattern
  schema : RuleSchema
  sourceLeftShape : source.left = .apply profile.checkHead [proof]
  sourceRightShape : source.right = .apply profile.okHead [result]
  premiseOrder : schema.premises = evidencePremises ++ sidePremises
  conclusionDefinition : conclusion = profile.derived result
  conclusionPreserved : schema.conclusion = conclusion
  ruleIdPreserved : schema.id.value = source.name

structure CheckedInput (profile : EvidenceProfile) (input : Pattern) where
  proof : Pattern
  shape : input = .apply profile.checkHead [proof]

def checkedInput? (profile : EvidenceProfile) (input : Pattern) :
    Option (CheckedInput profile input) :=
  match input with
  | .apply head [proof] =>
      if hhead : head == profile.checkHead then
        some
          { proof
            shape := by
              have : head = profile.checkHead := beq_iff_eq.mp hhead
              subst head
              rfl }
      else none
  | _ => none

structure CheckedOutput (profile : EvidenceProfile) (output : Pattern) where
  result : Pattern
  shape : output = .apply profile.okHead [result]

def checkedOutput? (profile : EvidenceProfile) (output : Pattern) :
    Option (CheckedOutput profile output) :=
  match output with
  | .apply head [result] =>
      if hhead : head == profile.okHead then
        some
          { result
            shape := by
              have : head = profile.okHead := beq_iff_eq.mp hhead
              subst head
              rfl }
      else none
  | _ => none

theorem checkedInputProof?_eq_checkedInput?_map
    (profile : EvidenceProfile) (input : Pattern) :
    checkedInputProof? profile input =
      (checkedInput? profile input).map (·.proof) := by
  cases input with
  | apply head arguments =>
      cases arguments with
      | nil => rfl
      | cons proof tail =>
          cases tail with
          | nil => simp [checkedInputProof?, checkedInput?]
          | cons second rest => rfl
  | bvar index => rfl
  | fvar name => rfl
  | lambda name body => rfl
  | multiLambda arity names body => rfl
  | subst body replacement => rfl
  | collection kind elements rest => rfl

theorem checkedOutputResult?_eq_checkedOutput?_map
    (profile : EvidenceProfile) (output : Pattern) :
    checkedOutputResult? profile output =
      (checkedOutput? profile output).map (·.result) := by
  cases output with
  | apply head arguments =>
      cases arguments with
      | nil => rfl
      | cons result tail =>
          cases tail with
          | nil => simp [checkedOutputResult?, checkedOutput?]
          | cons second rest => rfl
  | bvar index => rfl
  | fvar name => rfl
  | lambda name body => rfl
  | multiLambda arity names body => rfl
  | subst body replacement => rfl
  | collection kind elements rest => rfl

def extractRule? (profile : EvidenceProfile) (language : LanguageDef)
    (rule : RewriteRule) : Option (RuleExtraction profile) := do
  let input ← checkedInput? profile rule.left
  let output ← checkedOutput? profile rule.right
  let proof := input.proof
  let result := output.result
  let evidenceArguments ← evidenceArguments? profile language proof
  let evidencePremises := evidenceArguments.map profile.derived
  let sidePremises ← rule.premises.mapM (sidePremiseJudgment? profile)
  let conclusion := profile.derived result
  let schema :=
    extractedSchema profile rule evidencePremises sidePremises result
  pure
    { source := rule
      proof
      result
      evidencePremises
      sidePremises
      conclusion
      schema
      sourceLeftShape := input.shape
      sourceRightShape := output.shape
      premiseOrder := rfl
      conclusionDefinition := rfl
      conclusionPreserved := rfl
      ruleIdPreserved := rfl }

/-- Proof erasure commutes with rule extraction: the schema placed in a
generated presentation is exactly the schema carried by the corresponding
proof-producing extraction certificate. -/
theorem extractRuleSchema?_eq_extractRule?_schema
    (profile : EvidenceProfile) (language : LanguageDef)
    (rule : RewriteRule) :
    extractRuleSchema? profile language rule =
      (extractRule? profile language rule).map (·.schema) := by
  rw [extractRuleSchema?]
  rw [checkedInputProof?_eq_checkedInput?_map,
    checkedOutputResult?_eq_checkedOutput?_map]
  cases hinput : checkedInput? profile rule.left with
  | none => simp [hinput, extractRule?]
  | some input =>
      cases houtput : checkedOutput? profile rule.right with
      | none => simp [hinput, houtput, extractRule?]
      | some output =>
          simp [hinput, houtput, extractRule?, extractedSchema]

/-- Interpret the successful output of an authored checker rewrite as the
proof-relevant judgment generated for it. -/
def sourceOutputJudgment? (profile : EvidenceProfile) : Pattern → Option Pattern
  | .apply head [result] =>
      if head == profile.okHead then some (profile.derived result) else none
  | _ => none

/-- Generated conclusions commute exactly with source binding application.
This statement is independent of the schema-instantiation fragment because it
only exposes the authored checker's output wrapper. -/
theorem RuleExtraction.sourceOutputJudgment?_applyBindings
    {profile : EvidenceProfile} (extraction : RuleExtraction profile)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    sourceOutputJudgment? profile
        (Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings
          extraction.source.right) =
      some (Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings
        extraction.schema.conclusion) := by
  rw [extraction.sourceRightShape, extraction.conclusionPreserved,
    extraction.conclusionDefinition]
  simp [sourceOutputJudgment?, EvidenceProfile.derived,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

def relationJudgmentDecls (profile : EvidenceProfile)
    (language : LanguageDef) : List JudgmentDecl :=
  language.rewrites.flatMap fun rule =>
    rule.premises.filterMap fun premise =>
      match premise with
      | .relationQuery relation arguments =>
          some { head := profile.relationHead relation, arity := arguments.length }
      | _ => none

def referencedRelations (language : LanguageDef) : List String :=
  language.rewrites.flatMap fun rule =>
    rule.premises.filterMap fun premise =>
      match premise with
      | .relationQuery relation _ => some relation
      | _ => none

def relationFactRules (profile : EvidenceProfile)
    (language : LanguageDef) : List RuleSchema :=
  let referenced := referencedRelations language
  let facts := (datalogClosureTuples language).filter fun fact =>
    referenced.contains fact.1
  facts.zipIdx.map fun (fact, index) =>
    { id := { value := s!"$ld.fact.{fact.1}.{index}" }
      metavariables := []
      premises := []
      conclusion := profile.relationJudgment fact.1 fact.2 }

def rawPresentation? (profile : EvidenceProfile)
    (language : LanguageDef) : Option Presentation := do
  let rules ← language.rewrites.mapM (extractRuleSchema? profile language)
  pure
    { language
      judgments :=
        { head := profile.derivedHead, arity := 1 } ::
          (relationJudgmentDecls profile language).eraseDups
      rules := relationFactRules profile language ++ rules }

/-- Structurally recursive specification of generated presentation assembly.
It is convenient for kernel reasoning; `rawPresentation?` remains the
tail-recursive executable implementation. -/
def rawPresentationStructural? (profile : EvidenceProfile)
    (language : LanguageDef) : Option Presentation := do
  let rules ← language.rewrites.mapM'
    (extractRuleSchema? profile language)
  pure
    { language
      judgments :=
        { head := profile.derivedHead, arity := 1 } ::
          (relationJudgmentDecls profile language).eraseDups
      rules := relationFactRules profile language ++ rules }

/-- Executable and structurally recursive presentation assembly agree
exactly. -/
theorem rawPresentation?_eq_structural (profile : EvidenceProfile)
    (language : LanguageDef) :
    rawPresentation? profile language =
      rawPresentationStructural? profile language := by
  rw [rawPresentationStructural?]
  rw [rawPresentation?]
  rw [List.mapM'_eq_mapM]

def validatedPresentation? (profile : EvidenceProfile)
    (language : LanguageDef) : Option ValidatedPresentation := do
  let presentation ← rawPresentation? profile language
  presentation.validateV2?

end Mettapedia.GSLT.LanguageDef.InferenceExtraction
