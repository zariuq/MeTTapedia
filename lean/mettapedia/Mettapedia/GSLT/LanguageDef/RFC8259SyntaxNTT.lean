import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.Parsing.PresentationExprSemantics
import Mettapedia.GSLT.Parsing.ClassAwarePackedForest
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

/-!
# RFC 8259 syntax native-type diagnostics

This module records the complete in-memory syntax rows of the authored JSON
presentation so that NTT can inspect its structural crossings and the generic
syntax compiler can consume its terminals and nonterminals.  The lexical
profile remains a separate authored input.  A byte-level wire-decoding theorem
is still required before Lean can authenticate the external source file.
-/

namespace Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

private def ctor (label category : String)
    (parameters : List (String × String))
    (syntaxPattern : List SyntaxItem := []) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := syntaxPattern
}

private def terminal (token : String) : SyntaxItem := .terminal token
private def nonterminal (parameter : String) : SyntaxItem := .nonTerminal parameter

/-- Complete in-memory RFC 8259 lossless syntax language.  Terminals and
nonterminals are retained in authored order; lexical class meanings remain in
the separate parser profile. -/
def rfc8259Syntax : LanguageDef := {
  name := "RFC8259JsonSyntaxV1"
  types := [
    "JsonText", "JsonWs", "JsonWsChar", "JsonValue", "JsonObject",
    "JsonMembersOpt", "JsonMembers", "JsonMember", "JsonMemberTail",
    "JsonArray", "JsonElementsOpt", "JsonElements", "JsonElementTail",
    "JsonString", "JsonStringChars", "JsonStringChar", "JsonUnescaped",
    "JsonEscape", "JsonSimpleEscape", "JsonHexDigit", "JsonNumber",
    "JsonMinusOpt", "JsonInt", "JsonDigits", "JsonDigit", "JsonDigit19",
    "JsonFracOpt", "JsonFrac", "JsonExpOpt", "JsonExp", "JsonExpMark",
    "JsonSignOpt", "JsonSign"]
  terms := [
    ctor "json:text" "JsonText"
      [("leading", "JsonWs"), ("value", "JsonValue"), ("trailing", "JsonWs")]
      [nonterminal "leading", nonterminal "value", nonterminal "trailing"],
    ctor "json:ws-empty" "JsonWs" [],
    ctor "json:ws-cons" "JsonWs"
      [("head", "JsonWsChar"), ("tail", "JsonWs")]
      [nonterminal "head", nonterminal "tail"],
    ctor "json:value-false" "JsonValue" [] [terminal "false"],
    ctor "json:value-null" "JsonValue" [] [terminal "null"],
    ctor "json:value-true" "JsonValue" [] [terminal "true"],
    ctor "json:value-object" "JsonValue" [("object", "JsonObject")]
      [nonterminal "object"],
    ctor "json:value-array" "JsonValue" [("array", "JsonArray")]
      [nonterminal "array"],
    ctor "json:value-number" "JsonValue" [("number", "JsonNumber")]
      [nonterminal "number"],
    ctor "json:value-string" "JsonValue" [("string", "JsonString")]
      [nonterminal "string"],
    ctor "json:object" "JsonObject"
      [("leftWs", "JsonWs"), ("members", "JsonMembersOpt"),
       ("rightWs", "JsonWs")]
      [terminal "{", nonterminal "leftWs", nonterminal "members",
       nonterminal "rightWs", terminal "}"],
    ctor "json:members-none" "JsonMembersOpt" [],
    ctor "json:members-some" "JsonMembersOpt" [("members", "JsonMembers")]
      [nonterminal "members"],
    ctor "json:members" "JsonMembers"
      [("member", "JsonMember"), ("tail", "JsonMemberTail")]
      [nonterminal "member", nonterminal "tail"],
    ctor "json:member-tail-empty" "JsonMemberTail" [],
    ctor "json:member-tail-cons" "JsonMemberTail"
      [("leftWs", "JsonWs"), ("rightWs", "JsonWs"),
       ("member", "JsonMember"), ("tail", "JsonMemberTail")]
      [nonterminal "leftWs", terminal ",", nonterminal "rightWs",
       nonterminal "member", nonterminal "tail"],
    ctor "json:member" "JsonMember"
      [("name", "JsonString"), ("leftWs", "JsonWs"),
       ("rightWs", "JsonWs"), ("value", "JsonValue")]
      [nonterminal "name", nonterminal "leftWs", terminal ":",
       nonterminal "rightWs", nonterminal "value"],
    ctor "json:array" "JsonArray"
      [("leftWs", "JsonWs"), ("elements", "JsonElementsOpt"),
       ("rightWs", "JsonWs")]
      [terminal "[", nonterminal "leftWs", nonterminal "elements",
       nonterminal "rightWs", terminal "]"],
    ctor "json:elements-none" "JsonElementsOpt" [],
    ctor "json:elements-some" "JsonElementsOpt" [("elements", "JsonElements")]
      [nonterminal "elements"],
    ctor "json:elements" "JsonElements"
      [("value", "JsonValue"), ("tail", "JsonElementTail")]
      [nonterminal "value", nonterminal "tail"],
    ctor "json:element-tail-empty" "JsonElementTail" [],
    ctor "json:element-tail-cons" "JsonElementTail"
      [("leftWs", "JsonWs"), ("rightWs", "JsonWs"),
       ("value", "JsonValue"), ("tail", "JsonElementTail")]
      [nonterminal "leftWs", terminal ",", nonterminal "rightWs",
       nonterminal "value", nonterminal "tail"],
    ctor "json:string" "JsonString" [("characters", "JsonStringChars")]
      [terminal "\"", nonterminal "characters", terminal "\""],
    ctor "json:string-chars-empty" "JsonStringChars" [],
    ctor "json:string-chars-cons" "JsonStringChars"
      [("head", "JsonStringChar"), ("tail", "JsonStringChars")]
      [nonterminal "head", nonterminal "tail"],
    ctor "json:string-char-plain" "JsonStringChar"
      [("scalar", "JsonUnescaped")] [nonterminal "scalar"],
    ctor "json:string-char-escape" "JsonStringChar"
      [("escape", "JsonEscape")] [nonterminal "escape"],
    ctor "json:escape-simple" "JsonEscape" [("code", "JsonSimpleEscape")]
      [terminal "\\", nonterminal "code"],
    ctor "json:escape-unicode" "JsonEscape"
      [("h0", "JsonHexDigit"), ("h1", "JsonHexDigit"),
       ("h2", "JsonHexDigit"), ("h3", "JsonHexDigit")]
      [terminal "\\u", nonterminal "h0", nonterminal "h1",
       nonterminal "h2", nonterminal "h3"],
    ctor "json:number" "JsonNumber"
      [("minus", "JsonMinusOpt"), ("integer", "JsonInt"),
       ("fraction", "JsonFracOpt"), ("exponent", "JsonExpOpt")]
      [nonterminal "minus", nonterminal "integer", nonterminal "fraction",
       nonterminal "exponent"],
    ctor "json:minus-none" "JsonMinusOpt" [],
    ctor "json:minus-some" "JsonMinusOpt" [] [terminal "-"],
    ctor "json:int-zero" "JsonInt" [] [terminal "0"],
    ctor "json:int-nonzero" "JsonInt"
      [("head", "JsonDigit19"), ("tail", "JsonDigits")]
      [nonterminal "head", nonterminal "tail"],
    ctor "json:digits-empty" "JsonDigits" [],
    ctor "json:digits-cons" "JsonDigits"
      [("head", "JsonDigit"), ("tail", "JsonDigits")]
      [nonterminal "head", nonterminal "tail"],
    ctor "json:frac-none" "JsonFracOpt" [],
    ctor "json:frac-some" "JsonFracOpt" [("fraction", "JsonFrac")]
      [nonterminal "fraction"],
    ctor "json:frac" "JsonFrac"
      [("head", "JsonDigit"), ("tail", "JsonDigits")]
      [terminal ".", nonterminal "head", nonterminal "tail"],
    ctor "json:exp-none" "JsonExpOpt" [],
    ctor "json:exp-some" "JsonExpOpt" [("exponent", "JsonExp")]
      [nonterminal "exponent"],
    ctor "json:exp" "JsonExp"
      [("mark", "JsonExpMark"), ("sign", "JsonSignOpt"),
       ("head", "JsonDigit"), ("tail", "JsonDigits")]
      [nonterminal "mark", nonterminal "sign", nonterminal "head",
       nonterminal "tail"],
    ctor "json:sign-none" "JsonSignOpt" [],
    ctor "json:sign-some" "JsonSignOpt" [("sign", "JsonSign")]
      [nonterminal "sign"]
  ]
  equations := []
  rewrites := []
}

theorem rfc8259Syntax_inventory :
    rfc8259Syntax.types.length = 33 ∧
    rfc8259Syntax.terms.length = 45 ∧
    rfc8259Syntax.rewrites = [] := by
  decide

theorem object_value_crossing :
    ("json:value-object", "JsonObject", "JsonValue") ∈
      unaryCrossings rfc8259Syntax := by
  decide

theorem number_value_crossing :
    ("json:value-number", "JsonNumber", "JsonValue") ∈
      unaryCrossings rfc8259Syntax := by
  decide

theorem members_option_crossing :
    ("json:members-some", "JsonMembers", "JsonMembersOpt") ∈
      unaryCrossings rfc8259Syntax := by
  decide

/-- A member occurrence cannot become a JSON value without passing through
the ordered members and object constructors. -/
theorem no_member_value_crossing :
    ("json:invented-member-value", "JsonMember", "JsonValue") ∉
      unaryCrossings rfc8259Syntax := by
  decide

/-! ## Presentation-sensitive structural compilation -/

/-- Binding of the RFC 8259 structural rows to scannerless parser names.  It
is deliberately a function of the supplied syntax rows, not a source-file
name or digest. -/
def jsonSyntaxBinding : Binding where
  literalRef := fun token =>
    match token with
    | "false" => some "json:literal:false"
    | "null" => some "json:literal:null"
    | "true" => some "json:literal:true"
    | "{" => some "json:literal:left-brace"
    | "}" => some "json:literal:right-brace"
    | "," => some "json:literal:comma"
    | ":" => some "json:literal:colon"
    | "[" => some "json:literal:left-bracket"
    | "]" => some "json:literal:right-bracket"
    | "\"" => some "json:literal:quotation-mark"
    | "\\" => some "json:literal:reverse-solidus"
    | "\\u" => some "json:literal:unicode-escape-prefix"
    | "-" => some "json:literal:minus"
    | "0" => some "json:literal:zero"
    | "." => some "json:literal:decimal-point"
    | _ => none
  lexicalSortRef := rfc8259ParserProfile.lexicalRule?
  categoryRef := fun category => s!"json:category:{category}"
  ruleRef := fun label => s!"json:rule:{label}"

/-- The concrete compiled structural rules.  The following theorem prevents
the fallback value from carrying authority. -/
def compiledSyntaxRules : List CompiledRule :=
  (compileRules? jsonSyntaxBinding rfc8259Syntax).getD []

theorem compile_rfc8259Syntax_exact :
    compileRules? jsonSyntaxBinding rfc8259Syntax =
      some compiledSyntaxRules := by
  decide +kernel

theorem parser_profile_start_sort_is_authored_syntax_sort :
    rfc8259ParserProfile.startSort = "JsonText" ∧
      rfc8259Syntax.types.any (fun declaration =>
        declaration.name == rfc8259ParserProfile.startSort) = true := by
  decide

/-! ## Class-aware ParserPack lexical target -/

/-- The target lexical pack is compiled from the supplied profile itself.
Its class clauses remain part of the artifact, rather than being replaced by
a fixed JSON callback. -/
def rfc8259LexicalPack : CompiledLexicalPack :=
  compileLexicalPack rfc8259ParserProfile

theorem rfc8259LexicalPack_inventory :
    rfc8259LexicalPack.classes.length = 8 ∧
      rfc8259LexicalPack.productions.length = 8 := by
  decide

/-- Semantic profile mutation changes the compiled artifact even though the
lexical production labels and result sorts are unchanged. -/
theorem quotation_mutation_changes_compiled_lexical_pack :
    compileLexicalPack quotationAdmittingMutation ≠ rfc8259LexicalPack := by
  decide

/-- The generic proof-relevant lexical compiler theorem instantiated at the
actual RFC 8259 profile. -/
def rfc8259LexicalDerivationEquiv
    (input : List Nat) (resultSort : String)
    (start stop : Nat) (output : List CST) :
    SourceLexicalDerivesAt rfc8259ParserProfile input resultSort
        start stop output ≃
      CompiledLexicalDerivesAt rfc8259ParserProfile input resultSort
        start stop output :=
  lexicalDerivationEquiv rfc8259ParserProfile input resultSort
    start stop output

/-! ## Complete scannerless presentation with authored class semantics -/

private def literalDefinitions : List Definition := [
  { name := "json:literal:false", body := .literal [102, 97, 108, 115, 101] },
  { name := "json:literal:null", body := .literal [110, 117, 108, 108] },
  { name := "json:literal:true", body := .literal [116, 114, 117, 101] },
  { name := "json:literal:left-brace", body := .char 123 },
  { name := "json:literal:right-brace", body := .char 125 },
  { name := "json:literal:comma", body := .char 44 },
  { name := "json:literal:colon", body := .char 58 },
  { name := "json:literal:left-bracket", body := .char 91 },
  { name := "json:literal:right-bracket", body := .char 93 },
  { name := "json:literal:quotation-mark", body := .char 34 },
  { name := "json:literal:reverse-solidus", body := .char 92 },
  { name := "json:literal:unicode-escape-prefix", body := .literal [92, 117] },
  { name := "json:literal:minus", body := .char 45 },
  { name := "json:literal:zero", body := .char 48 },
  { name := "json:literal:decimal-point", body := .char 46 }]

private def lexicalDefinitions : List Definition := [
  { name := "json:lex-ws",
    body := .node "json:lex-ws" (.class "JsonWsClass") },
  { name := "json:lex-unescaped",
    body := .node "json:lex-unescaped" (.class "JsonUnescapedClass") },
  { name := "json:lex-digit",
    body := .node "json:lex-digit" (.class "JsonDigitClass") },
  { name := "json:lex-digit19",
    body := .node "json:lex-digit19" (.class "JsonDigit19Class") },
  { name := "json:lex-hexdigit",
    body := .node "json:lex-hexdigit" (.class "JsonHexDigitClass") },
  { name := "json:lex-simple-escape",
    body := .node "json:lex-simple-escape" (.class "JsonSimpleEscapeClass") },
  { name := "json:lex-exp-mark",
    body := .node "json:lex-exp-mark" (.class "JsonExpMarkClass") },
  { name := "json:lex-sign",
    body := .node "json:lex-sign" (.class "JsonSignClass") }]

def compiledCategoryDefinitions : List Definition :=
  (compileCategoryDefinitions? jsonSyntaxBinding rfc8259Syntax
    compiledSyntaxRules).getD []

theorem compile_rfc8259_categories_exact :
    compileCategoryDefinitions? jsonSyntaxBinding rfc8259Syntax
        compiledSyntaxRules =
      some compiledCategoryDefinitions := by
  decide +kernel

/-- The complete scannerless definition environment generated from the exact
syntax rows and parser profile.  Character classes are interpreted by
`rfc8259ClassEvidence`, not by the legacy finite `members` field. -/
def rfc8259ScannerlessPresentation : Presentation := {
  name := "RFC8259JsonScannerlessV1"
  definitions := literalDefinitions ++ lexicalDefinitions ++
    compiledSyntaxRules.map (CompiledRule.definition jsonSyntaxBinding) ++
    compiledCategoryDefinitions
  members := []
}

/-! ## Full presentation-sensitive ParserPack plan -/

/-- Resolve a source terminal by following the supplied syntax binding into
an explicitly supplied scannerless presentation. -/
def jsonTerminalScalarsFrom?
    (presentation : Presentation) (token : String) : Option (List Nat) := do
  let parserRef ← jsonSyntaxBinding.literalRef token
  presentation.literalCodepoints? parserRef

/-- The RFC instance contains no second JSON spelling table. -/
def jsonTerminalScalars? : String → Option (List Nat) :=
  jsonTerminalScalarsFrom? rfc8259ScannerlessPresentation

/-- The exact lexical and structural ParserPack artifact option compiled from
the authored profile, syntax rows, binding, and scannerless presentation. -/
def rfc8259ParserPackPlanOption : Option CompiledParserPackPlan :=
  compileParserPackPlan? jsonTerminalScalars? rfc8259ParserProfile
    compiledSyntaxRules

/-- The concrete plan is extracted only after the kernel checks successful
compilation. -/
def rfc8259ParserPackPlan : CompiledParserPackPlan :=
  rfc8259ParserPackPlanOption.get (by decide)

theorem compile_rfc8259_parser_pack_exact :
    rfc8259ParserPackPlanOption = some rfc8259ParserPackPlan := by
  decide +kernel

/-- The executable plan remains tied to the exact profile, literal resolver,
and ordered structural rules used to compile it. -/
def rfc8259ParserPackAgreement :
    ParserPackPlanAgreement jsonTerminalScalars? rfc8259ParserProfile
      compiledSyntaxRules rfc8259ParserPackPlan :=
  ParserPackPlanAgreement.of_compilation compile_rfc8259_parser_pack_exact

theorem rfc8259_parser_pack_start_sort_agrees :
    rfc8259ParserPackPlan.lexical.startSort =
      rfc8259ParserProfile.startSort :=
  rfc8259ParserPackAgreement.startSort_eq

/-- All 45 ordered structural occurrences have pointwise compiler evidence. -/
def rfc8259StructuralCompilation :
    StructuralRulesCompile jsonTerminalScalars?
      rfc8259ParserProfile.startSort compiledSyntaxRules
      rfc8259ParserPackPlan.structural :=
  rfc8259ParserPackAgreement.structuralCompilation

/-- Selecting any source row position and compiling it produces exactly the
target production at the corresponding target position. -/
theorem rfc8259_structural_occurrence_compiles_exactly
    (occurrence : ListOccurrence compiledSyntaxRules) :
    compileStructuralRule? jsonTerminalScalars?
        rfc8259ParserProfile.startSort
        (compiledSyntaxRules.get occurrence) =
      some (rfc8259ParserPackPlan.structural.get
        (rfc8259StructuralCompilation.mapOccurrence occurrence)) :=
  rfc8259StructuralCompilation.get_compiled occurrence

theorem rfc8259_structural_occurrence_map_injective :
    Function.Injective rfc8259StructuralCompilation.mapOccurrence :=
  rfc8259StructuralCompilation.mapOccurrence_injective

theorem rfc8259_parser_pack_inventory :
    rfc8259ParserPackPlan.lexical.classes.length = 8 ∧
      rfc8259ParserPackPlan.lexical.productions.length = 8 ∧
      rfc8259ParserPackPlan.structural.length = 45 := by
  decide +kernel

/-- Concrete positive control: the authored start production retains its
three nonterminal children at slots 0, 1, and 2.  EOF belongs only to the
separate whole-input entry. -/
theorem rfc8259_text_parserpack_shape :
    rfc8259ParserPackPlan.structural.head?.map (fun production =>
      (production.label, production.resultSort,
        production.items, production.childSlots)) =
      some ("json:text", "JsonText",
        [.nonterminal "JsonWs", .nonterminal "JsonValue",
         .nonterminal "JsonWs"],
        [0, 1, 2]) := by
  decide +kernel

/-- Semantic lexical mutation changes the full ParserPack plan, rather than
being hidden behind the same fixed matcher callback. -/
theorem quotation_mutation_changes_full_parser_pack_plan :
    compileParserPackPlan? jsonTerminalScalars? quotationAdmittingMutation
        compiledSyntaxRules ≠
      rfc8259ParserPackPlanOption := by
  decide +kernel

private def duplicateNullLiteralMutation : Presentation :=
  { rfc8259ScannerlessPresentation with
    definitions :=
      { name := "json:literal:null", body := .literal [0] } ::
        rfc8259ScannerlessPresentation.definitions }

/-- Negative control: if the supplied presentation gives the same literal
reference two meanings, whole-plan compilation fails.  The first list entry
cannot silently win. -/
theorem duplicate_literal_definition_rejects_full_parser_pack_plan :
    compileParserPackPlan?
        (jsonTerminalScalarsFrom? duplicateNullLiteralMutation)
        rfc8259ParserProfile compiledSyntaxRules = none := by
  decide +kernel

/-- Proposition-valued evidence supplied by the exact authored lexical
profile, including exclusion classes and the Unicode-scalar boundary. -/
def rfc8259ClassEvidence (className : String) (codepoint : Nat) : Prop :=
  rfc8259ParserProfile.classAccepts? className codepoint = some true

abbrev RFC8259RecognizesAt (input : List Nat) : Expr → Nat → Nat → Type :=
  RecognizesAtUsing rfc8259ClassEvidence rfc8259ScannerlessPresentation input

/-- Exact single-codepoint lexical adequacy: a scannerless class derivation
exists precisely when the supplied parser profile admits that scalar. -/
theorem rfc8259_class_recognizes_singleton_iff
    (className : String) (codepoint : Nat) :
    Nonempty (RFC8259RecognizesAt [codepoint]
      (.class className) 0 1) ↔
      rfc8259ParserProfile.classAccepts? className codepoint = some true := by
  constructor
  · rintro ⟨derivation⟩
    cases derivation with
    | classMember lookup evidence =>
        simp at lookup
        subst_vars
        simpa [rfc8259ClassEvidence] using evidence
  · intro evidence
    exact ⟨.classMember (by rfl) (by
      simpa [rfc8259ClassEvidence] using evidence)⟩

theorem rfc8259_unescaped_letter_positive :
    Nonempty (RFC8259RecognizesAt [65]
      (.class "JsonUnescapedClass") 0 1) := by
  rw [rfc8259_class_recognizes_singleton_iff]
  decide

private def unescapedLexicalDefinition : Definition := {
  name := "json:lex-unescaped"
  body := .node "json:lex-unescaped" (.class "JsonUnescapedClass")
}

private theorem unescapedLexicalDefinition_mem :
    unescapedLexicalDefinition ∈
      rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private def unescapedLetterDerivation :
    RFC8259RecognizesAt [65] (.ref "json:lex-unescaped") 0 1 :=
  .ref unescapedLexicalDefinition unescapedLexicalDefinition_mem rfl <|
    .node <| .classMember (by rfl) (by
      change
        rfc8259ParserProfile.classAccepts?
          "JsonUnescapedClass" 65 = some true
      decide)

/-- The lexical layer does not merely accept the scalar: it produces the
exact labelled lexical occurrence, its scalar leaf, and its physical span. -/
theorem rfc8259_unescaped_letter_exact_cst :
    Nonempty (CSTRecognizesAtUsing rfc8259ClassEvidence
      rfc8259ScannerlessPresentation [65]
      (.ref "json:lex-unescaped") 0 1
      [.node "json:lex-unescaped" 0 1 [.terminal [65] 0 1]]) := by
  exact ⟨⟨unescapedLetterDerivation, rfl⟩⟩

private def unescapedLexicalState :
    Mettapedia.GSLT.Parsing.ParserProfileSemantics.LexicalStateDecl := {
  resultSort := "JsonUnescaped"
  className := "JsonUnescapedClass"
  ruleLabel := "json:lex-unescaped"
}

private def unescapedLexicalStateOccurrence :
    ListOccurrence rfc8259ParserProfile.states :=
  ⟨1, by decide⟩

private theorem unescapedLexicalStateOccurrence_value :
    rfc8259ParserProfile.states.get unescapedLexicalStateOccurrence =
      unescapedLexicalState := by
  rfl

private def unescapedSourceLexicalDerivation :
    SourceLexicalDerivesAt rfc8259ParserProfile [65]
      "JsonUnescaped" 0 1
      [.node "json:lex-unescaped" 0 1 [.terminal [65] 0 1]] :=
  .apply unescapedLexicalStateOccurrence
    ⟨.classMember (by rfl) (by
        change rfc8259ParserProfile.classAccepts?
          "JsonUnescapedClass" 65 = some true
        decide), rfl⟩

/-- The actual RFC lexical occurrence survives the compiled ParserPack
matcher with the same label, scalar leaf, span, and source-state fibre. -/
theorem rfc8259_compiled_unescaped_letter_exact_cst :
    Nonempty (CompiledLexicalDerivesAt rfc8259ParserProfile [65]
      "JsonUnescaped" 0 1
      [.node "json:lex-unescaped" 0 1 [.terminal [65] 0 1]]) := by
  exact ⟨rfc8259LexicalDerivationEquiv _ _ _ _ _
    unescapedSourceLexicalDerivation⟩

/-- The compiled class matcher reflects the profile's quotation exclusion;
it cannot silently degrade to `any`. -/
theorem rfc8259_compiled_unescaped_quotation_negative :
    IsEmpty (TerminalMatchesAt rfc8259ParserProfile [34]
      (.class "JsonUnescapedClass") 0 1) := by
  constructor
  intro matched
  cases matched with
  | classMember lookup evidence =>
      simp at lookup
      subst_vars
      change rfc8259ParserProfile.classAccepts?
        "JsonUnescapedClass" 34 = some true at evidence
      have rejected :
          rfc8259ParserProfile.classAccepts?
              "JsonUnescapedClass" 34 = some false :=
        unescaped_class_boundaries.2.1
      rw [rejected] at evidence
      simp at evidence

/-- Negative control: quotation cannot acquire an unescaped lexical
derivation. -/
theorem rfc8259_unescaped_quotation_negative :
    IsEmpty (RFC8259RecognizesAt [34]
      (.class "JsonUnescapedClass") 0 1) := by
  constructor
  intro derivation
  have admitted :
      rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 34 = some true :=
    (rfc8259_class_recognizes_singleton_iff _ _).mp ⟨derivation⟩
  have rejected :
      rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 34 = some false :=
    unescaped_class_boundaries.2.1
  rw [rejected] at admitted
  simp at admitted

/-! ## Whole-root scannerless canary -/

private def textCategoryDefinition : Definition := {
  name := "json:category:JsonText"
  body := .ref "json:rule:json:text"
}

private def textRuleDefinition : Definition := {
  name := "json:rule:json:text"
  body := .node "json:text"
    (.seq (.ref "json:category:JsonWs")
      (.seq (.ref "json:category:JsonValue")
        (.left (.ref "json:category:JsonWs") .epsilon)))
}

private def whitespaceCategoryDefinition : Definition := {
  name := "json:category:JsonWs"
  body := .alt (.ref "json:rule:json:ws-empty")
    (.ref "json:rule:json:ws-cons")
}

private def whitespaceEmptyRuleDefinition : Definition := {
  name := "json:rule:json:ws-empty"
  body := .node "json:ws-empty" .epsilon
}

private def valueCategoryDefinition : Definition := {
  name := "json:category:JsonValue"
  body := .alt (.ref "json:rule:json:value-false")
    (.alt (.ref "json:rule:json:value-null")
      (.alt (.ref "json:rule:json:value-true")
        (.alt (.ref "json:rule:json:value-object")
          (.alt (.ref "json:rule:json:value-array")
            (.alt (.ref "json:rule:json:value-number")
              (.ref "json:rule:json:value-string"))))))
}

private def nullRuleDefinition : Definition := {
  name := "json:rule:json:value-null"
  body := .node "json:value-null"
    (.right (.ref "json:literal:null") .epsilon)
}

private def nullLiteralDefinition : Definition := {
  name := "json:literal:null"
  body := .literal [110, 117, 108, 108]
}

private theorem textCategoryDefinition_mem :
    textCategoryDefinition ∈ rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem textRuleDefinition_mem :
    textRuleDefinition ∈ rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem whitespaceCategoryDefinition_mem :
    whitespaceCategoryDefinition ∈
      rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem whitespaceEmptyRuleDefinition_mem :
    whitespaceEmptyRuleDefinition ∈
      rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem valueCategoryDefinition_mem :
    valueCategoryDefinition ∈ rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem nullRuleDefinition_mem :
    nullRuleDefinition ∈ rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private theorem nullLiteralDefinition_mem :
    nullLiteralDefinition ∈
      rfc8259ScannerlessPresentation.definitions := by
  decide +kernel

private def whitespaceEmptyDerivation (input : List Nat) (cursor : Nat) :
    RFC8259RecognizesAt input (.ref "json:category:JsonWs") cursor cursor :=
  .ref whitespaceCategoryDefinition whitespaceCategoryDefinition_mem rfl <|
    .altLeft <|
      .ref whitespaceEmptyRuleDefinition whitespaceEmptyRuleDefinition_mem rfl <|
        .node (.epsilon cursor)

private def nullValueDerivation :
    RFC8259RecognizesAt [110, 117, 108, 108]
      (.ref "json:category:JsonValue") 0 4 :=
  .ref valueCategoryDefinition valueCategoryDefinition_mem rfl <|
    .altRight <| .altLeft <|
      .ref nullRuleDefinition nullRuleDefinition_mem rfl <|
        .node <| .right
          (.ref nullLiteralDefinition nullLiteralDefinition_mem rfl <|
            .literal (by decide))
          (.epsilon 4)

private def nullTextDerivation :
    RFC8259RecognizesAt [110, 117, 108, 108]
      (.ref "json:category:JsonText") 0 4 :=
  .ref textCategoryDefinition textCategoryDefinition_mem rfl <|
    .ref textRuleDefinition textRuleDefinition_mem rfl <| .node <|
      .seq (whitespaceEmptyDerivation _ 0) <|
        .seq nullValueDerivation <|
          .left (whitespaceEmptyDerivation _ 4) (.epsilon 4)

/-- Positive whole-root canary: the exact profile plus the definitions
generated from all authored syntax rows recognizes `null`, including both
empty-whitespace occurrences and the selected value alternative. -/
theorem rfc8259_null_is_recognized :
    Nonempty (RFC8259RecognizesAt [110, 117, 108, 108]
      (.ref "json:category:JsonText") 0 4) := by
  exact ⟨nullTextDerivation⟩

/-- Whole-root codepoint-to-CST correspondence for the smallest JSON value.
The CST contains both zero-width whitespace occurrences and the selected
value production; literal codepoints are consumed but discarded by the
authored semantic action. -/
theorem rfc8259_null_exact_cst :
    Nonempty (CSTRecognizesAtUsing rfc8259ClassEvidence
      rfc8259ScannerlessPresentation [110, 117, 108, 108]
      (.ref "json:category:JsonText") 0 4
      [.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []]]) := by
  exact ⟨⟨nullTextDerivation, rfl⟩⟩

/-! ## Executed target-plan canary -/

private def textPackOccurrence :
    ListOccurrence rfc8259ParserPackPlan.structural :=
  ⟨0, by decide⟩

private def whitespaceEmptyPackOccurrence :
    ListOccurrence rfc8259ParserPackPlan.structural :=
  ⟨1, by decide⟩

private def nullValuePackOccurrence :
    ListOccurrence rfc8259ParserPackPlan.structural :=
  ⟨4, by decide⟩

private def textSourceOccurrence :
    ListOccurrence compiledSyntaxRules :=
  ⟨0, by decide⟩

private def whitespaceEmptySourceOccurrence :
    ListOccurrence compiledSyntaxRules :=
  ⟨1, by decide⟩

private def nullValueSourceOccurrence :
    ListOccurrence compiledSyntaxRules :=
  ⟨4, by decide⟩

private def whitespaceEmptySourceDerivation
    (input : List Nat) (cursor : Nat) :
    SourcePlanDerivesAt jsonTerminalScalars? rfc8259ParserProfile
      compiledSyntaxRules input "JsonWs" cursor cursor
      (.node "json:ws-empty" cursor cursor []) := by
  refine SourcePlanDerivesAt.structural whitespaceEmptySourceOccurrence.val
    whitespaceEmptySourceOccurrence.isLt
    (by rfl) (by rfl) ?_
  exact .nil

private def nullValueSourceDerivation :
    SourcePlanDerivesAt jsonTerminalScalars? rfc8259ParserProfile
      compiledSyntaxRules [110, 117, 108, 108] "JsonValue" 0 4
      (.node "json:value-null" 0 4 []) := by
  refine SourcePlanDerivesAt.structural nullValueSourceOccurrence.val
    nullValueSourceOccurrence.isLt
    (by rfl) (by rfl) ?_
  exact .terminal (by rfl)
      (.cons (by rfl) <| .cons (by rfl) <|
        .cons (by rfl) <| .cons (by rfl) (.nil 4)) .nil

private def nullTextSourceDerivation :
    SourcePlanRootDerives jsonTerminalScalars? rfc8259ParserProfile
      compiledSyntaxRules [110, 117, 108, 108]
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []]) := by
  refine SourcePlanDerivesAt.structural textSourceOccurrence.val
    textSourceOccurrence.isLt
    (by rfl) (by rfl) ?_
  exact .nonterminal (whitespaceEmptySourceDerivation _ 0) <|
      .nonterminal nullValueSourceDerivation <|
        .nonterminal (whitespaceEmptySourceDerivation _ 4) .nil

private def whitespaceEmptyPackDerivation
    (input : List Nat) (cursor : Nat) :
    ParserPackDerivesAt rfc8259ParserProfile rfc8259ParserPackPlan input
      "JsonWs" cursor cursor (.node "json:ws-empty" cursor cursor []) := by
  refine ParserPackDerivesAt.structural whitespaceEmptyPackOccurrence.val
    whitespaceEmptyPackOccurrence.isLt (by rfl) (by rfl) ?_
  exact .nil

private def nullValuePackDerivation :
    ParserPackDerivesAt rfc8259ParserProfile rfc8259ParserPackPlan
      [110, 117, 108, 108] "JsonValue" 0 4
      (.node "json:value-null" 0 4 []) := by
  refine ParserPackDerivesAt.structural nullValuePackOccurrence.val
    nullValuePackOccurrence.isLt (by rfl) (by rfl) ?_
  exact .terminal (.char (by rfl)) <|
    .terminal (.char (by rfl)) <|
      .terminal (.char (by rfl)) <|
        .terminal (.char (by rfl)) .nil

private def nullTextPackDerivation :
    ParserPackRootDerives rfc8259ParserProfile rfc8259ParserPackPlan
      [110, 117, 108, 108]
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []]) := by
  refine ParserPackDerivesAt.structural textPackOccurrence.val
    textPackOccurrence.isLt (by rfl) (by rfl) ?_
  exact .nonterminal (whitespaceEmptyPackDerivation _ 0) <|
    .nonterminal nullValuePackDerivation <|
      .nonterminal (whitespaceEmptyPackDerivation _ 4) .nil

/-- The complete RFC presentation has an exact proof-fibre equivalence at the
whole-input `null` CST.  This is stronger than equality of parse success: both
directions retain the selected physical productions, zero-width whitespace
occurrences, and spans.  The synthetic entry separately checks EOF. -/
def rfc8259_null_proof_fibre_equiv :
    SourcePlanRootDerives jsonTerminalScalars? rfc8259ParserProfile
        compiledSyntaxRules [110, 117, 108, 108]
        (.node "json:text" 0 4
          [.node "json:ws-empty" 0 0 [],
           .node "json:value-null" 0 4 [],
           .node "json:ws-empty" 4 4 []]) ≃
      ParserPackRootDerives rfc8259ParserProfile rfc8259ParserPackPlan
        [110, 117, 108, 108]
        (.node "json:text" 0 4
          [.node "json:ws-empty" 0 0 [],
           .node "json:value-null" 0 4 [],
           .node "json:ws-empty" 4 4 []]) :=
  sourcePlanRootDerivationEquiv rfc8259ParserPackAgreement _

theorem rfc8259_null_source_proof_roundtrip :
    rfc8259_null_proof_fibre_equiv.symm
        (rfc8259_null_proof_fibre_equiv nullTextSourceDerivation) =
      nullTextSourceDerivation :=
  rfc8259_null_proof_fibre_equiv.left_inv nullTextSourceDerivation

theorem rfc8259_null_target_proof_roundtrip :
    rfc8259_null_proof_fibre_equiv
        (rfc8259_null_proof_fibre_equiv.symm nullTextPackDerivation) =
      nullTextPackDerivation :=
  rfc8259_null_proof_fibre_equiv.right_inv nullTextPackDerivation

/-! ## Portable ParserPack certificate canary -/

/-- The finite certificate emitted by the `null` target derivation.  Every
structural row is identified by its physical production position, and every
terminal and nonterminal seam carries its exact scalar span. -/
def rfc8259NullCertificate : Certificate :=
  .structural 0 0 4 <|
    .nonterminal "JsonWs" 0 0 (.structural 1 0 0 (.nil 0)) <|
      .nonterminal "JsonValue" 0 4
        (.structural 4 0 4 <|
          .terminal (.char 110) 0 1 <|
            .terminal (.char 117) 1 2 <|
              .terminal (.char 108) 2 3 <|
                .terminal (.char 108) 3 4 (.nil 4)) <|
        .nonterminal "JsonWs" 4 4 (.structural 1 4 4 (.nil 4)) (.nil 4)

/-- Certificate erasure exposes exactly the expected portable data rather
than retaining a hidden Lean proof object. -/
theorem rfc8259_null_certificate_exact :
    Certificate.ofDerivation nullTextPackDerivation =
      rfc8259NullCertificate := by
  rfl

/-- The portable `null` certificate is admitted by exact replay against the
supplied RFC profile, compiled plan, and scalar input. -/
noncomputable def rfc8259NullAdmittedCertificate :
    AdmittedRootCertificate rfc8259ParserProfile rfc8259ParserPackPlan
      [110, 117, 108, 108]
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []]) :=
  rootDerivationCertificateEquiv rfc8259ParserProfile
    rfc8259ParserPackPlan [110, 117, 108, 108] _
    nullTextPackDerivation

theorem rfc8259_null_admitted_certificate_exact :
    rfc8259NullAdmittedCertificate.val = rfc8259NullCertificate := by
  rfl

/-- Replaying the admitted finite certificate reconstructs the exact target
derivation, including physical production choices and zero-width steps. -/
theorem rfc8259_null_certificate_replay_roundtrip :
    (rootDerivationCertificateEquiv rfc8259ParserProfile
      rfc8259ParserPackPlan [110, 117, 108, 108] _).symm
        rfc8259NullAdmittedCertificate = nullTextPackDerivation :=
  (rootDerivationCertificateEquiv rfc8259ParserProfile
    rfc8259ParserPackPlan [110, 117, 108, 108] _).left_inv
      nullTextPackDerivation

/-- Canonical shared forest containing the complete `null` certificate. -/
def rfc8259NullForest : Forest :=
  pack [("JsonText", Certificate.ofDerivation nullTextPackDerivation)]

theorem rfc8259_null_forest_exact :
    rfc8259NullForest = pack [("JsonText", rfc8259NullCertificate)] := by
  rw [rfc8259NullForest, rfc8259_null_certificate_exact]

/-- The exact `null` certificate unfolds from the canonical shared forest. -/
theorem rfc8259_null_forest_unfolds :
    RootUnfolds rfc8259NullForest "JsonText"
      (Certificate.ofDerivation nullTextPackDerivation) := by
  exact member_pack_rootUnfolds (by simp)

theorem rfc8259_null_expected_certificate_unfolds :
    RootUnfolds rfc8259NullForest "JsonText" rfc8259NullCertificate := by
  rw [← rfc8259_null_certificate_exact]
  exact rfc8259_null_forest_unfolds

/-- The shared forest and finite certificate jointly replay against the
supplied RFC profile and plan. -/
def rfc8259NullPackedReplay :
    PackedReplays rfc8259NullForest rfc8259ParserProfile
      rfc8259ParserPackPlan [110, 117, 108, 108]
      (Certificate.ofDerivation nullTextPackDerivation) "JsonText" 0 4
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []]) := by
  refine ⟨⟨rfc8259_null_forest_unfolds⟩, ?_⟩
  exact Replays.ofDerivation nullTextPackDerivation

/-- Packed replay reconstructs the same exact target derivation; forest
packing adds sharing but no semantic authority. -/
theorem rfc8259_null_packed_replay_exact :
    rfc8259NullPackedReplay.derivation = nullTextPackDerivation := by
  exact Replays.derivation_ofDerivation nullTextPackDerivation

/-- The concrete ParserPack plan executes the same whole-root `null` CST as
the independently defined scannerless presentation, including both
zero-width whitespace occurrences and exact spans. -/
theorem rfc8259_compiled_parser_pack_null_exact_cst :
    Nonempty (ParserPackRootDerives rfc8259ParserProfile
      rfc8259ParserPackPlan [110, 117, 108, 108]
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []])) := by
  exact ⟨nullTextPackDerivation⟩

/-- The generic recursive preservation map, instantiated on the complete
RFC presentation, carries the independently defined source-plan derivation
to the executable ParserPack proof fibre. -/
theorem rfc8259_source_plan_null_is_preserved :
    Nonempty (SourcePlanRootDerives jsonTerminalScalars?
        rfc8259ParserProfile compiledSyntaxRules [110, 117, 108, 108]
        (.node "json:text" 0 4
          [.node "json:ws-empty" 0 0 [],
           .node "json:value-null" 0 4 [],
           .node "json:ws-empty" 4 4 []])) ∧
      Nonempty (ParserPackRootDerives rfc8259ParserProfile
        rfc8259ParserPackPlan [110, 117, 108, 108]
        (.node "json:text" 0 4
          [.node "json:ws-empty" 0 0 [],
           .node "json:value-null" 0 4 [],
           .node "json:ws-empty" 4 4 []])) := by
  refine ⟨⟨nullTextSourceDerivation⟩, ?_⟩
  exact ⟨preserveSourcePlanDerivation rfc8259ParserPackAgreement
    nullTextSourceDerivation⟩

/-- Conversely, the target `null` execution reflects to source-plan evidence;
this is the concrete RFC no-invention direction of the generic theorem. -/
theorem rfc8259_parser_pack_null_invents_no_source_derivation :
    Nonempty (SourcePlanRootDerives jsonTerminalScalars?
      rfc8259ParserProfile compiledSyntaxRules [110, 117, 108, 108]
      (.node "json:text" 0 4
        [.node "json:ws-empty" 0 0 [],
         .node "json:value-null" 0 4 [],
         .node "json:ws-empty" 4 4 []])) := by
  exact ⟨reflectSourcePlanDerivation rfc8259ParserPackAgreement
    nullTextPackDerivation⟩

/-- Every generated rule retains its complete authored source row. -/
theorem compiledSyntaxRules_source_exact :
    compiledSyntaxRules.map (fun rule => rule.source) =
      rfc8259Syntax.terms :=
  compileRules_sourceRules jsonSyntaxBinding rfc8259Syntax
    compiledSyntaxRules compile_rfc8259Syntax_exact

/-- Every target structural production retains one exact source occurrence,
including source order and multiplicity.  This uses the generic compiler
provenance theorem rather than recomputing the 45 rows. -/
theorem rfc8259_parser_pack_structural_source_exact :
    rfc8259ParserPackPlan.structural.map
        (fun production => production.source) =
      rfc8259Syntax.terms := by
  have compiledStructural :
      compileStructuralProductions? jsonTerminalScalars?
          rfc8259ParserProfile.startSort compiledSyntaxRules =
        some rfc8259ParserPackPlan.structural := by
    decide +kernel
  calc
    rfc8259ParserPackPlan.structural.map
          (fun production => production.source) =
        compiledSyntaxRules.map (fun rule => rule.source) :=
      compileStructuralProductions_source jsonTerminalScalars?
        rfc8259ParserProfile.startSort compiledSyntaxRules
        rfc8259ParserPackPlan.structural compiledStructural
    _ = rfc8259Syntax.terms := compiledSyntaxRules_source_exact

/-- Terminals, nonterminals, order, and multiplicity survive structural
compilation exactly. -/
theorem compiledSyntaxRules_syntax_exact :
    compiledSyntaxRules.map (fun rule =>
        rule.atoms.map StructuralAtom.sourceSyntax) =
      rfc8259Syntax.terms.map (fun rule => rule.syntaxPattern) :=
  compileRules_sourceSyntax jsonSyntaxBinding rfc8259Syntax
    compiledSyntaxRules compile_rfc8259Syntax_exact

/-- The generated structural rule machine derives exactly the authored
token-level JSON trees: preservation and no invention are both inherited from
the language-neutral compiler theorem. -/
theorem compiledSyntaxRules_derivation_iff
    (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives compiledSyntaxRules sort tokens tree ↔
      Mettapedia.OSLF.Framework.GrammarDerives.Derives
        rfc8259Syntax sort tokens tree :=
  compileRules_derivation_iff compile_rfc8259Syntax_exact sort tokens tree

/-- Every generated JSON rule has the canonical independently decodable
terminal-discard/nonterminal-retention action shape. -/
theorem compiledSyntaxRules_action_shape
    (rule : CompiledRule) (member : rule ∈ compiledSyntaxRules) :
    rule.body = .node rule.source.label (compileSequence rule.atoms) ∧
      decodeSequenceActions? (compileSequence rule.atoms) =
        some (rule.atoms.map StructuralAtom.referenceAction) :=
  compileRules_action_shape compile_rfc8259Syntax_exact rule member

/-- Negative control: deleting an authored production changes the compiler
result.  The compiler cannot recognize the presentation by name and return a
fixed RFC 8259 parser. -/
def missingTextRuleMutation : LanguageDef :=
  { rfc8259Syntax with terms := rfc8259Syntax.terms.drop 1 }

theorem missing_text_rule_changes_compilation :
    compileRules? jsonSyntaxBinding missingTextRuleMutation ≠
      compileRules? jsonSyntaxBinding rfc8259Syntax := by
  decide +kernel

/-! ## Exact operational status of the syntax presentation -/

/-- The authored syntax object has structural constructors but no operational
rewrite rules.  This is not a parser kernel; parser execution belongs to the
separate ParserPack presentation. -/
def rfc8259SyntaxTheory : Mettapedia.GSLT.GSLT :=
  languageGSLT rfc8259Syntax
    (ReductionRespectsEquations.of_equation_free rfl)

theorem rfc8259SyntaxTheory_no_step (source target : Pattern) :
    ¬ rfc8259SyntaxTheory.Step source target := by
  intro reduction
  unfold rfc8259SyntaxTheory at reduction
  rw [languageGSLT_step] at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

/-- Exact decision for the intentionally empty operational relation.  Its
existence must not be confused with executable JSON parsing. -/
def rfc8259SyntaxStepDecision :
    EffectiveStructure.StepDecision rfc8259SyntaxTheory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact rfc8259SyntaxTheory_no_step source target

def rfc8259SyntaxOSLF := langOSLF rfc8259Syntax "JsonText"

theorem rfc8259Syntax_galois :
    GaloisConnection (langDiamond rfc8259Syntax) (langBox rfc8259Syntax) :=
  langGalois rfc8259Syntax

private def ws : Pattern := .apply "json:ws-empty" []
private def key : Pattern :=
  .apply "json:string" [.apply "json:string-chars-empty" []]
private def member (value : Pattern) : Pattern :=
  .apply "json:member" [key, ws, ws, value]
private def duplicateCST : Pattern :=
  .apply "json:value-object"
    [.apply "json:object"
      [ws,
       .apply "json:members-some"
        [.apply "json:members"
          [member (.apply "json:value-false" []),
           .apply "json:member-tail-cons"
            [ws, ws, member (.apply "json:value-true" []),
             .apply "json:member-tail-empty" []]]],
       ws]]

/-- Duplicate key syntax remains an ordered pair of member occurrences; the
syntax language does not silently normalize it to a map. -/
theorem duplicate_cst_is_normal :
    rewriteAt (engineBasePremises RelationEnv.empty)
        rfc8259Syntax 1 duplicateCST = [] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
