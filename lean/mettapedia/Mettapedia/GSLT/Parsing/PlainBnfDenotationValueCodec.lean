import Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
import Mathlib.Tactic

/-!
# Physical result of plain-BNF denotation

The authored plain-BNF denotation GSLT emits ordinary CeTTa values.  This
module states the exact physical fold independently of the typed denotation,
then decodes those values into the existing `LanguageDef`, parser-profile, and
origin types.

The fold mirrors the authored accumulator discipline: grammar types are
prepended to lexical types, alternatives are flattened in source order, empty
literals denote epsilon, and reference indices advance independently of
literals.  This is the physical side of the denotation correspondence.  A
separate operational theorem must still connect execution of the authored
GSLT presentation to this fold.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfDenotationValueCodec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
open Mettapedia.GSLT.LanguageDef.CettaWire

/-! ## Exact fragment decoders -/

def decodeAstType : Term -> Option TypeDecl
  | .application "TypeDecl" [.string name, .symbol "CarrierAst"] =>
      some { name, carrier := .ast }
  | _ => none

def decodeBaseParameter : Term -> Option TermParam
  | .application "TermSimple"
      [.string name, .application "TBase" [.string typeName]] =>
      some (.simple name (.base typeName))
  | _ => none

def decodePlainSyntaxItem : Term -> Option SyntaxItem
  | .application "SyntaxTerminal" [.string text] => some (.terminal text)
  | .application "SyntaxNonTerminal" [.string parameter] =>
      some (.nonTerminal parameter)
  | _ => none

def decodePlainGrammarRule : Term -> Option GrammarRule
  | .application "GrammarRule"
      [.string label, .string category, parameters, syntaxTerm,
        .symbol "EvalNone"] => do
      let decodedParameters <- decodeList decodeBaseParameter parameters
      let decodedSyntax <- decodeList decodePlainSyntaxItem syntaxTerm
      some {
        label
        category
        params := decodedParameters
        syntaxPattern := decodedSyntax }
  | _ => none

def decodePlainLanguage : Term -> Option LanguageDef
  | .application "GSLTLanguageDefWireV1"
      [.string name, types, rules, .symbol "LNil", .symbol "LNil"] => do
      let decodedTypes <- decodeList decodeAstType types
      let decodedRules <- decodeList decodePlainGrammarRule rules
      some {
        name
        types := decodedTypes
        terms := decodedRules
        equations := []
        rewrites := [] }
  | _ => none

def decodeNat : Term -> Option Nat
  | .natural value => some value
  | _ => none

def decodeLexicalClass : Term -> Option LexicalClassDecl
  | .application "LexicalClassPoints" [.string name, scalars] => do
      let decodedScalars <- decodeList decodeNat scalars
      some { name, kind := .points decodedScalars }
  | .application "LexicalClassExcept" [.string name, scalars] => do
      let decodedScalars <- decodeList decodeNat scalars
      some { name, kind := .except decodedScalars }
  | _ => none

def decodeLexicalState : Term -> Option LexicalStateDecl
  | .application "LexicalState"
      [.string resultSort, .string className, .string ruleLabel] =>
      some { resultSort, className, ruleLabel }
  | _ => none

def decodeProfile : Term -> Option ParserProfileLayer
  | .application "GSLTParserProfileLayerV1"
      [.string name, .string startSort, classes, states] => do
      let decodedClasses <- decodeList decodeLexicalClass classes
      let decodedStates <- decodeList decodeLexicalState states
      some {
        name
        startSort
        classes := decodedClasses
        states := decodedStates }
  | _ => none

def decodeRuleOrigin : Term -> Option GeneratedRuleOrigin
  | .application "BNF:GeneratedRuleOrigin"
      [.string label, .string category, ruleSpan, alternativeSpan] => do
      let decodedRuleSpan <- decodeSourceSpan ruleSpan
      let decodedAlternativeSpan <- decodeSourceSpan alternativeSpan
      some {
        label
        category
        ruleSpan := decodedRuleSpan
        alternativeSpan := decodedAlternativeSpan }
  | _ => none

def decodeLexicalOriginResult : Term -> Option GeneratedLexicalOrigin
  | .application "BNF:GeneratedLexicalOrigin"
      [.string resultSort, .string className, .string ruleLabel,
        matcher, source] => do
      let decodedMatcher <- decodeLexicalMatcher matcher
      let decodedSource <- decodeLexicalOrigin source
      some {
        resultSort
        className
        ruleLabel
        matcher := decodedMatcher
        source := decodedSource }
  | _ => none

def decodeOrigins : Term -> Option DenotationOrigins
  | .application "BNF:DenotationOriginsV1" [rules, lexical] => do
      let decodedRules <- decodeList decodeRuleOrigin rules
      let decodedLexical <- decodeList decodeLexicalOriginResult lexical
      some { rules := decodedRules, lexical := decodedLexical }
  | _ => none

def decodeCandidate : Term -> Option Candidate
  | .application "BNF:DenotationCandidate" [language, profile, origins] => do
      let decodedLanguage <- decodePlainLanguage language
      let decodedProfile <- decodeProfile profile
      let decodedOrigins <- decodeOrigins origins
      some {
        language := decodedLanguage
        profile := decodedProfile
        origins := decodedOrigins }
  | _ => none

/-! ## Direct physical fold -/

/-- The GSLT constructs `#`, `#x`, `#xx`, ... by repeatedly appending one
`x`.  This definition is intentionally separate from the typed denotation's
closed-form occurrence suffix. -/
def physicalOccurrenceSuffix : Nat -> String
  | 0 => "#"
  | index + 1 => physicalOccurrenceSuffix index ++ "x"

theorem physicalOccurrenceSuffix_eq (index : Nat) :
    physicalOccurrenceSuffix index = occurrenceSuffix index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp [physicalOccurrenceSuffix, occurrenceSuffix,
        List.replicate_succ', String.ofList_append, ih,
        String.append_assoc]

def physicalRuleLabel (category : String) (index : Nat) : String :=
  category ++ physicalOccurrenceSuffix index

def physicalParameterName (index : Nat) : String :=
  "p" ++ physicalOccurrenceSuffix index

@[simp] theorem physicalRuleLabel_eq (category : String) (index : Nat) :
    physicalRuleLabel category index = generatedRuleLabel category index := by
  simp [physicalRuleLabel, generatedRuleLabel, physicalOccurrenceSuffix_eq]

@[simp] theorem physicalParameterName_eq (index : Nat) :
    physicalParameterName index = generatedParameterName index := by
  simp [physicalParameterName, generatedParameterName,
    physicalOccurrenceSuffix_eq]

def physicalType (name : String) : Term :=
  .application "TypeDecl" [.string name, .symbol "CarrierAst"]

def physicalLexicalTypes : List LexicalDeclaration -> Term
  | [] => .symbol "LNil"
  | declaration :: rest =>
      .application "LCons"
        [physicalType declaration.referenceName, physicalLexicalTypes rest]

/-- Source grammar types are accumulated in front of the already produced
lexical tail, exactly as in the denotation GSLT. -/
def physicalRuleTypes : List Entry -> Term -> Term
  | [], tail => tail
  | .rule name _ _ :: rest, tail =>
      .application "LCons"
        [physicalType name, physicalRuleTypes rest tail]
  | .comment _ _ :: rest, tail => physicalRuleTypes rest tail
  | .blank _ :: rest, tail => physicalRuleTypes rest tail

def physicalParameters : List Element -> Nat -> Term
  | [], _ => .symbol "LNil"
  | .reference typeName _ :: rest, index =>
      .application "LCons"
        [.application "TermSimple"
          [.string (physicalParameterName index),
            .application "TBase" [.string typeName]],
          physicalParameters rest (index + 1)]
  | .literal _ _ :: rest, index => physicalParameters rest index

def physicalSyntax : List Element -> Nat -> Term
  | [], _ => .symbol "LNil"
  | .reference _ _ :: rest, index =>
      .application "LCons"
        [.application "SyntaxNonTerminal"
          [.string (physicalParameterName index)],
          physicalSyntax rest (index + 1)]
  | .literal text _ :: rest, index =>
      if text.isEmpty then physicalSyntax rest index
      else
        .application "LCons"
          [.application "SyntaxTerminal" [.string text],
            physicalSyntax rest index]

def physicalRule (category : String) (index : Nat)
    (alternative : Alternative) : Term :=
  .application "GrammarRule"
    [.string (physicalRuleLabel category index),
      .string category,
      physicalParameters alternative.elements 0,
      physicalSyntax alternative.elements 0,
      .symbol "EvalNone"]

def physicalAlternatives :
    String -> List Alternative -> Nat -> Term -> Term
  | _, [], _, tail => tail
  | category, alternative :: rest, index, tail =>
      .application "LCons"
        [physicalRule category index alternative,
          physicalAlternatives category rest (index + 1) tail]

def physicalRules : List Entry -> Term
  | [] => .symbol "LNil"
  | .rule category expression _ :: rest =>
      physicalAlternatives category expression.alternatives 0
        (physicalRules rest)
  | .comment _ _ :: rest => physicalRules rest
  | .blank _ :: rest => physicalRules rest

def physicalRuleOrigin (category : String) (ruleSpan : SourceSpan)
    (index : Nat) (alternative : Alternative) : Term :=
  .application "BNF:GeneratedRuleOrigin"
    [.string (physicalRuleLabel category index),
      .string category,
      encodeSourceSpan ruleSpan,
      encodeSourceSpan alternative.span]

def physicalAlternativeOrigins :
    String -> SourceSpan -> List Alternative -> Nat -> Term -> Term
  | _, _, [], _, tail => tail
  | category, ruleSpan, alternative :: rest, index, tail =>
      .application "LCons"
        [physicalRuleOrigin category ruleSpan index alternative,
          physicalAlternativeOrigins category ruleSpan rest (index + 1) tail]

def physicalRuleOrigins : List Entry -> Term
  | [] => .symbol "LNil"
  | .rule category expression ruleSpan :: rest =>
      physicalAlternativeOrigins category ruleSpan
        expression.alternatives 0 (physicalRuleOrigins rest)
  | .comment _ _ :: rest => physicalRuleOrigins rest
  | .blank _ :: rest => physicalRuleOrigins rest

def physicalScalars (scalars : List Nat) : Term :=
  encodeList Term.natural scalars

def physicalLexicalClass (declaration : LexicalDeclaration) : Term :=
  match declaration.matcher with
  | .points scalars =>
      .application "LexicalClassPoints"
        [.string declaration.className, physicalScalars scalars]
  | .except excluded =>
      .application "LexicalClassExcept"
        [.string declaration.className, physicalScalars excluded]

def physicalLexicalClasses (declarations : List LexicalDeclaration) : Term :=
  encodeList physicalLexicalClass declarations

def physicalLexicalState (declaration : LexicalDeclaration) : Term :=
  .application "LexicalState"
    [.string declaration.referenceName,
      .string declaration.className,
      .string declaration.ruleLabel]

def physicalLexicalStates (declarations : List LexicalDeclaration) : Term :=
  encodeList physicalLexicalState declarations

def physicalLexicalOriginResult (declaration : LexicalDeclaration) : Term :=
  .application "BNF:GeneratedLexicalOrigin"
    [.string declaration.referenceName,
      .string declaration.className,
      .string declaration.ruleLabel,
      encodeLexicalMatcher declaration.matcher,
      encodeLexicalOrigin declaration.origin]

def physicalLexicalOrigins (declarations : List LexicalDeclaration) : Term :=
  encodeList physicalLexicalOriginResult declarations

/-- Exact physical candidate expected from successful execution of the
authored denotation presentation.  Admission evidence is intentionally absent:
the denotation rules inspect only the accepted document, explicit start, and
typed lexical environment. -/
def physicalDenote (document : Document) (authority : GrammarAuthority) : Term :=
  .application "BNF:DenotationCandidate"
    [.application "GSLTLanguageDefWireV1"
      [.string "PlainBnfDenotedSyntaxV1",
        physicalRuleTypes document.entries
          (physicalLexicalTypes authority.lexicalDeclarations),
        physicalRules document.entries,
        .symbol "LNil",
        .symbol "LNil"],
      .application "GSLTParserProfileLayerV1"
        [.string "PlainBnfDenotedParserV1",
          .string authority.startName,
          physicalLexicalClasses authority.lexicalDeclarations,
          physicalLexicalStates authority.lexicalDeclarations],
      .application "BNF:DenotationOriginsV1"
        [physicalRuleOrigins document.entries,
          physicalLexicalOrigins authority.lexicalDeclarations]]

/-! ## Physical-to-typed correspondence -/

@[simp] theorem decodeAstType_physicalType (name : String) :
    decodeAstType (physicalType name) =
      some { name := name, carrier := .ast } := by
  rfl

@[simp] theorem decodeLexicalTypes_physicalLexicalTypes
    (declarations : List LexicalDeclaration) :
    decodeList decodeAstType (physicalLexicalTypes declarations) =
      some (denoteLexicalTypes declarations) := by
  induction declarations with
  | nil => simp [physicalLexicalTypes, denoteLexicalTypes, decodeList]
  | cons declaration rest ih =>
      simp [physicalLexicalTypes, denoteLexicalTypes, decodeList, ih]

theorem decodeRuleTypes_physicalRuleTypes
    (entries : List Entry) (tail : Term) (decodedTail : List TypeDecl)
    (tailExact : decodeList decodeAstType tail = some decodedTail) :
    decodeList decodeAstType (physicalRuleTypes entries tail) =
      some (denoteRuleTypes entries ++ decodedTail) := by
  induction entries generalizing tail decodedTail with
  | nil => simpa [physicalRuleTypes, denoteRuleTypes] using tailExact
  | cons entry rest ih =>
      cases entry with
      | rule name expression span =>
          simp [physicalRuleTypes, denoteRuleTypes, decodeList,
            ih _ _ tailExact]
      | comment text span =>
          simpa [physicalRuleTypes, denoteRuleTypes] using
            ih tail decodedTail tailExact
      | blank span =>
          simpa [physicalRuleTypes, denoteRuleTypes] using
            ih tail decodedTail tailExact

@[simp] theorem decodeBaseParameters_physicalParameters
    (elements : List Element) (index : Nat) :
    decodeList decodeBaseParameter (physicalParameters elements index) =
      some (denoteParameters elements index) := by
  induction elements generalizing index with
  | nil => simp [physicalParameters, denoteParameters,
      denoteReferenceBindings, decodeList]
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp [physicalParameters, denoteParameters, decodeList,
            decodeBaseParameter,
            denoteReferenceBindings, ih]
      | literal text span =>
          simpa [physicalParameters, denoteParameters,
            denoteReferenceBindings] using ih index

@[simp] theorem decodePlainSyntax_physicalSyntax
    (elements : List Element) (index : Nat) :
    decodeList decodePlainSyntaxItem (physicalSyntax elements index) =
      some (denoteSyntax elements index) := by
  induction elements generalizing index with
  | nil => simp [physicalSyntax, denoteSyntax, decodeList]
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp [physicalSyntax, denoteSyntax, decodeList,
            decodePlainSyntaxItem, ih]
      | literal text span =>
          by_cases empty : text.isEmpty
          · simp [physicalSyntax, denoteSyntax, empty, ih]
          · simp [physicalSyntax, denoteSyntax, decodeList,
              decodePlainSyntaxItem, empty, ih]

@[simp] theorem decodePlainGrammarRule_physicalRule
    (category : String) (index : Nat) (alternative : Alternative) :
    decodePlainGrammarRule (physicalRule category index alternative) =
      some (denoteAlternative category index alternative) := by
  cases alternative
  simp [physicalRule, decodePlainGrammarRule, denoteAlternative,
    denoteElements]

theorem decodeAlternatives_physicalAlternatives
    (category : String) (alternatives : List Alternative) (index : Nat)
    (tail : Term) (decodedTail : List GrammarRule)
    (tailExact : decodeList decodePlainGrammarRule tail = some decodedTail) :
    decodeList decodePlainGrammarRule
        (physicalAlternatives category alternatives index tail) =
      some (denoteAlternatives category alternatives index ++ decodedTail) := by
  induction alternatives generalizing index tail decodedTail with
  | nil => simpa [physicalAlternatives, denoteAlternatives] using tailExact
  | cons alternative rest ih =>
      simp [physicalAlternatives, denoteAlternatives, decodeList,
        ih _ _ _ tailExact]

@[simp] theorem decodeRules_physicalRules (entries : List Entry) :
    decodeList decodePlainGrammarRule (physicalRules entries) =
      some (denoteRules entries) := by
  induction entries with
  | nil => simp [physicalRules, denoteRules, decodeList]
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simpa [physicalRules, denoteRules] using
            decodeAlternatives_physicalAlternatives category
              expression.alternatives 0 (physicalRules rest)
              (denoteRules rest) ih
      | comment text span =>
          simpa [physicalRules, denoteRules] using ih
      | blank span =>
          simpa [physicalRules, denoteRules] using ih

@[simp] theorem decodeRuleOrigin_physicalRuleOrigin
    (category : String) (ruleSpan : SourceSpan) (index : Nat)
    (alternative : Alternative) :
    decodeRuleOrigin
        (physicalRuleOrigin category ruleSpan index alternative) =
      some {
        label := generatedRuleLabel category index
        category
        ruleSpan
        alternativeSpan := alternative.span } := by
  simp [physicalRuleOrigin, decodeRuleOrigin]

theorem decodeAlternativeOrigins_physicalAlternativeOrigins
    (category : String) (ruleSpan : SourceSpan)
    (alternatives : List Alternative) (index : Nat)
    (tail : Term) (decodedTail : List GeneratedRuleOrigin)
    (tailExact : decodeList decodeRuleOrigin tail = some decodedTail) :
    decodeList decodeRuleOrigin
        (physicalAlternativeOrigins category ruleSpan alternatives index tail) =
      some (denoteAlternativeOrigins category ruleSpan alternatives index ++
        decodedTail) := by
  induction alternatives generalizing index tail decodedTail with
  | nil =>
      simpa [physicalAlternativeOrigins, denoteAlternativeOrigins] using
        tailExact
  | cons alternative rest ih =>
      simp [physicalAlternativeOrigins, denoteAlternativeOrigins, decodeList,
        ih _ _ _ tailExact]

@[simp] theorem decodeRuleOrigins_physicalRuleOrigins (entries : List Entry) :
    decodeList decodeRuleOrigin (physicalRuleOrigins entries) =
      some (denoteRuleOrigins entries) := by
  induction entries with
  | nil => simp [physicalRuleOrigins, denoteRuleOrigins, decodeList]
  | cons entry rest ih =>
      cases entry with
      | rule category expression ruleSpan =>
          simpa [physicalRuleOrigins, denoteRuleOrigins] using
            decodeAlternativeOrigins_physicalAlternativeOrigins category
              ruleSpan expression.alternatives 0 (physicalRuleOrigins rest)
              (denoteRuleOrigins rest) ih
      | comment text span =>
          simpa [physicalRuleOrigins, denoteRuleOrigins] using ih
      | blank span =>
          simpa [physicalRuleOrigins, denoteRuleOrigins] using ih

@[simp] theorem decodeNatList_physicalScalars (scalars : List Nat) :
    decodeList decodeNat (physicalScalars scalars) = some scalars := by
  exact decodeList_encodeList decodeNat Term.natural (fun _ => rfl) scalars

@[simp] theorem decodeLexicalClass_physicalLexicalClass
    (declaration : LexicalDeclaration) :
    decodeLexicalClass (physicalLexicalClass declaration) =
      some (denoteLexicalClass declaration) := by
  cases declaration with
  | mk referenceName className matcher ruleLabel origin =>
      cases matcher <;>
        simp [physicalLexicalClass, decodeLexicalClass, denoteLexicalClass]

@[simp] theorem decodeLexicalClasses_physicalLexicalClasses
    (declarations : List LexicalDeclaration) :
    decodeList decodeLexicalClass (physicalLexicalClasses declarations) =
      some (declarations.map denoteLexicalClass) := by
  exact decodeList_encodeList_map decodeLexicalClass
    physicalLexicalClass denoteLexicalClass
    decodeLexicalClass_physicalLexicalClass declarations

@[simp] theorem decodeLexicalState_physicalLexicalState
    (declaration : LexicalDeclaration) :
    decodeLexicalState (physicalLexicalState declaration) =
      some (denoteLexicalState declaration) := by
  cases declaration
  rfl

@[simp] theorem decodeLexicalStates_physicalLexicalStates
    (declarations : List LexicalDeclaration) :
    decodeList decodeLexicalState (physicalLexicalStates declarations) =
      some (declarations.map denoteLexicalState) := by
  exact decodeList_encodeList_map decodeLexicalState
    physicalLexicalState denoteLexicalState
    decodeLexicalState_physicalLexicalState declarations

@[simp] theorem decodeLexicalOriginResult_physicalLexicalOriginResult
    (declaration : LexicalDeclaration) :
    decodeLexicalOriginResult (physicalLexicalOriginResult declaration) =
      some (denoteLexicalOrigin declaration) := by
  cases declaration
  simp [physicalLexicalOriginResult, decodeLexicalOriginResult,
    denoteLexicalOrigin]

@[simp] theorem decodeLexicalOrigins_physicalLexicalOrigins
    (declarations : List LexicalDeclaration) :
    decodeList decodeLexicalOriginResult
        (physicalLexicalOrigins declarations) =
      some (declarations.map denoteLexicalOrigin) := by
  exact decodeList_encodeList_map decodeLexicalOriginResult
    physicalLexicalOriginResult denoteLexicalOrigin
    decodeLexicalOriginResult_physicalLexicalOriginResult declarations

/-- The direct physical fold has exactly the independently stated typed
denotation.  No parser, runtime hook, or handwritten expected candidate occurs
in the theorem statement. -/
theorem decodeCandidate_physicalDenote
    (document : Document) (authority : GrammarAuthority) :
    decodeCandidate (physicalDenote document authority) =
      some (denote document authority) := by
  simp [physicalDenote, decodeCandidate, decodePlainLanguage, decodeProfile,
    decodeOrigins, denote,
    decodeRuleTypes_physicalRuleTypes document.entries
      (physicalLexicalTypes authority.lexicalDeclarations)
      (denoteLexicalTypes authority.lexicalDeclarations)]

/-! ## Discriminating physical controls -/

theorem candidate_rejects_wrong_equation_tail :
    decodeCandidate
      (.application "BNF:DenotationCandidate"
        [.application "GSLTLanguageDefWireV1"
          [.string "Broken", .symbol "LNil", .symbol "LNil",
            .application "LCons" [.symbol "unexpected", .symbol "LNil"],
            .symbol "LNil"],
          .application "GSLTParserProfileLayerV1"
            [.string "Profile", .string "S", .symbol "LNil",
              .symbol "LNil"],
          .application "BNF:DenotationOriginsV1"
            [.symbol "LNil", .symbol "LNil"]]) = none := by
  rfl

theorem grammar_rule_rejects_implicit_eval_policy :
    decodePlainGrammarRule
      (.application "GrammarRule"
        [.string "r", .string "S", .symbol "LNil", .symbol "LNil"]) =
      none := by
  rfl

#print axioms decodeCandidate_physicalDenote
#print axioms physicalOccurrenceSuffix_eq
#print axioms candidate_rejects_wrong_equation_tail
#print axioms grammar_rule_rejects_implicit_eval_policy

end Mettapedia.GSLT.Parsing.PlainBnfDenotationValueCodec
