import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mathlib.Tactic

/-!
# Exact physical codec for structured plain-BNF values

The executable plain-BNF workbench exchanges ordinary MeTTa values built from
the authored `bnf-v1:*` constructors.  This module gives those existing values
their typed Lean meaning.  It reuses the project's physical CeTTa
S-expression carrier; no BNF-specific wire or parser representation is added.

Encoding is canonical and total.  Decoding is structural and fail-closed:
constructor names, arities, quoted-string positions, list tails, and Unicode
scalar validity must all agree.  Grammar admission remains separate from wire
decoding, so properties such as unique definitions and resolved references do
not appear here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec

open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.LanguageDef.CettaWire

/-! ## BNF text and source spans -/

def encodeTextChars : List Char -> Term
  | [] => .application "bnf-v1:text-nil" []
  | character :: rest =>
      .application "bnf-v1:text-cons"
        [.natural character.toNat, encodeTextChars rest]

def decodeTextChars : Term -> Option (List Char)
  | .application "bnf-v1:text-nil" [] => some []
  | .application "bnf-v1:text-cons" [.natural scalar, rest] =>
      if isUnicodeScalar scalar then do
        let decodedRest <- decodeTextChars rest
        some (Char.ofNat scalar :: decodedRest)
      else
        none
  | _ => none
termination_by term => sizeOf term

private theorem unicodeScalar_toNat (character : Char) :
    isUnicodeScalar character.toNat = true := by
  cases character with
  | mk value valid =>
      simp [isUnicodeScalar, Char.toNat] at valid ⊢
      omega

@[simp] theorem decodeTextChars_encodeTextChars (characters : List Char) :
    decodeTextChars (encodeTextChars characters) = some characters := by
  induction characters with
  | nil => simp [encodeTextChars, decodeTextChars]
  | cons character rest ih =>
      simp [encodeTextChars, decodeTextChars, unicodeScalar_toNat,
        Char.ofNat_toNat, ih]

def encodeText (value : String) : Term :=
  encodeTextChars value.toList

def decodeText (term : Term) : Option String := do
  let characters <- decodeTextChars term
  some (String.ofList characters)

@[simp] theorem decodeText_encodeText (value : String) :
    decodeText (encodeText value) = some value := by
  simp [encodeText, decodeText, String.ofList_toList]

theorem encodeText_injective : Function.Injective encodeText := by
  intro left right equal
  have decoded := congrArg decodeText equal
  simpa using decoded

def encodeSourceSpan (span : SourceSpan) : Term :=
  .application "bnf-v1:source-span"
    [.natural span.start, .natural span.stop]

def decodeSourceSpan : Term -> Option SourceSpan
  | .application "bnf-v1:source-span"
      [.natural start, .natural stop] =>
      some { start, stop }
  | _ => none

@[simp] theorem decodeSourceSpan_encodeSourceSpan (span : SourceSpan) :
    decodeSourceSpan (encodeSourceSpan span) = some span := by
  cases span
  rfl

/-! ## Grammar document -/

def encodeElement : Element -> Term
  | .reference name span =>
      .application "bnf-v1:reference"
        [encodeText name, encodeSourceSpan span]
  | .literal text span =>
      .application "bnf-v1:literal"
        [encodeText text, encodeSourceSpan span]

def decodeElement : Term -> Option Element
  | .application "bnf-v1:reference" [name, span] => do
      let decodedName <- decodeText name
      let decodedSpan <- decodeSourceSpan span
      some (.reference decodedName decodedSpan)
  | .application "bnf-v1:literal" [text, span] => do
      let decodedText <- decodeText text
      let decodedSpan <- decodeSourceSpan span
      some (.literal decodedText decodedSpan)
  | _ => none

@[simp] theorem decodeElement_encodeElement (element : Element) :
    decodeElement (encodeElement element) = some element := by
  cases element <;> simp [encodeElement, decodeElement]

def encodeElements : List Element -> Term
  | [] => .application "bnf-v1:elements-nil" []
  | element :: rest =>
      .application "bnf-v1:elements-cons"
        [encodeElement element, encodeElements rest]

def decodeElements : Term -> Option (List Element)
  | .application "bnf-v1:elements-nil" [] => some []
  | .application "bnf-v1:elements-cons" [element, rest] => do
      let decodedElement <- decodeElement element
      let decodedRest <- decodeElements rest
      some (decodedElement :: decodedRest)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeElements_encodeElements (elements : List Element) :
    decodeElements (encodeElements elements) = some elements := by
  induction elements with
  | nil => simp [encodeElements, decodeElements]
  | cons element rest ih =>
      simp [encodeElements, decodeElements, ih]

def encodeAlternative (alternative : Alternative) : Term :=
  .application "bnf-v1:alternative"
    [encodeElements alternative.elements,
      encodeSourceSpan alternative.span]

def decodeAlternative : Term -> Option Alternative
  | .application "bnf-v1:alternative" [elements, span] => do
      let decodedElements <- decodeElements elements
      let decodedSpan <- decodeSourceSpan span
      some { elements := decodedElements, span := decodedSpan }
  | _ => none

@[simp] theorem decodeAlternative_encodeAlternative
    (alternative : Alternative) :
    decodeAlternative (encodeAlternative alternative) = some alternative := by
  cases alternative
  simp [encodeAlternative, decodeAlternative]

def encodeAlternatives : List Alternative -> Term
  | [] => .application "bnf-v1:alternatives-nil" []
  | alternative :: rest =>
      .application "bnf-v1:alternatives-cons"
        [encodeAlternative alternative, encodeAlternatives rest]

def decodeAlternatives : Term -> Option (List Alternative)
  | .application "bnf-v1:alternatives-nil" [] => some []
  | .application "bnf-v1:alternatives-cons" [alternative, rest] => do
      let decodedAlternative <- decodeAlternative alternative
      let decodedRest <- decodeAlternatives rest
      some (decodedAlternative :: decodedRest)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeAlternatives_encodeAlternatives
    (alternatives : List Alternative) :
    decodeAlternatives (encodeAlternatives alternatives) = some alternatives := by
  induction alternatives with
  | nil => simp [encodeAlternatives, decodeAlternatives]
  | cons alternative rest ih =>
      simp [encodeAlternatives, decodeAlternatives, ih]

def encodeExpression (expression : Expression) : Term :=
  .application "bnf-v1:expression"
    [encodeAlternatives expression.alternatives,
      encodeSourceSpan expression.span]

def decodeExpression : Term -> Option Expression
  | .application "bnf-v1:expression" [alternatives, span] => do
      let decodedAlternatives <- decodeAlternatives alternatives
      let decodedSpan <- decodeSourceSpan span
      some { alternatives := decodedAlternatives, span := decodedSpan }
  | _ => none

@[simp] theorem decodeExpression_encodeExpression (expression : Expression) :
    decodeExpression (encodeExpression expression) = some expression := by
  cases expression
  simp [encodeExpression, decodeExpression]

def encodeEntry : Entry -> Term
  | .rule name expression span =>
      .application "bnf-v1:rule"
        [encodeText name, encodeExpression expression, encodeSourceSpan span]
  | .comment text span =>
      .application "bnf-v1:comment"
        [encodeText text, encodeSourceSpan span]
  | .blank span =>
      .application "bnf-v1:blank" [encodeSourceSpan span]

def decodeEntry : Term -> Option Entry
  | .application "bnf-v1:rule" [name, expression, span] => do
      let decodedName <- decodeText name
      let decodedExpression <- decodeExpression expression
      let decodedSpan <- decodeSourceSpan span
      some (.rule decodedName decodedExpression decodedSpan)
  | .application "bnf-v1:comment" [text, span] => do
      let decodedText <- decodeText text
      let decodedSpan <- decodeSourceSpan span
      some (.comment decodedText decodedSpan)
  | .application "bnf-v1:blank" [span] => do
      let decodedSpan <- decodeSourceSpan span
      some (.blank decodedSpan)
  | _ => none

@[simp] theorem decodeEntry_encodeEntry (entry : Entry) :
    decodeEntry (encodeEntry entry) = some entry := by
  cases entry <;> simp [encodeEntry, decodeEntry]

def encodeEntries : List Entry -> Term
  | [] => .application "bnf-v1:entries-nil" []
  | entry :: rest =>
      .application "bnf-v1:entries-cons"
        [encodeEntry entry, encodeEntries rest]

def decodeEntries : Term -> Option (List Entry)
  | .application "bnf-v1:entries-nil" [] => some []
  | .application "bnf-v1:entries-cons" [entry, rest] => do
      let decodedEntry <- decodeEntry entry
      let decodedRest <- decodeEntries rest
      some (decodedEntry :: decodedRest)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeEntries_encodeEntries (entries : List Entry) :
    decodeEntries (encodeEntries entries) = some entries := by
  induction entries with
  | nil => simp [encodeEntries, decodeEntries]
  | cons entry rest ih =>
      simp [encodeEntries, decodeEntries, ih]

def encodeDocument (document : Document) : Term :=
  .application "bnf-v1:document"
    [encodeEntries document.entries, encodeSourceSpan document.span]

def decodeDocument : Term -> Option Document
  | .application "bnf-v1:document" [entries, span] => do
      let decodedEntries <- decodeEntries entries
      let decodedSpan <- decodeSourceSpan span
      some { entries := decodedEntries, span := decodedSpan }
  | _ => none

@[simp] theorem decodeDocument_encodeDocument (document : Document) :
    decodeDocument (encodeDocument document) = some document := by
  cases document
  simp [encodeDocument, decodeDocument]

theorem encodeDocument_injective : Function.Injective encodeDocument := by
  intro left right equal
  have decoded := congrArg decodeDocument equal
  simpa using decoded

/-! ## Explicit start and lexical authority -/

def encodeScalars : List Nat -> Term
  | [] => .application "bnf-v1:scalars-nil" []
  | scalar :: rest =>
      .application "bnf-v1:scalars-cons"
        [.natural scalar, encodeScalars rest]

def decodeScalars : Term -> Option (List Nat)
  | .application "bnf-v1:scalars-nil" [] => some []
  | .application "bnf-v1:scalars-cons" [.natural scalar, rest] => do
      let decodedRest <- decodeScalars rest
      some (scalar :: decodedRest)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeScalars_encodeScalars (scalars : List Nat) :
    decodeScalars (encodeScalars scalars) = some scalars := by
  induction scalars with
  | nil => simp [encodeScalars, decodeScalars]
  | cons scalar rest ih =>
      simp [encodeScalars, decodeScalars, ih]

def encodeLexicalMatcher : LexicalMatcher -> Term
  | .points scalars =>
      .application "bnf-v1:lexical-points" [encodeScalars scalars]
  | .except excluded =>
      .application "bnf-v1:lexical-except" [encodeScalars excluded]

def decodeLexicalMatcher : Term -> Option LexicalMatcher
  | .application "bnf-v1:lexical-points" [scalars] => do
      let decodedScalars <- decodeScalars scalars
      some (.points decodedScalars)
  | .application "bnf-v1:lexical-except" [excluded] => do
      let decodedExcluded <- decodeScalars excluded
      some (.except decodedExcluded)
  | _ => none

@[simp] theorem decodeLexicalMatcher_encodeLexicalMatcher
    (matcher : LexicalMatcher) :
    decodeLexicalMatcher (encodeLexicalMatcher matcher) = some matcher := by
  cases matcher <;> simp [encodeLexicalMatcher, decodeLexicalMatcher]

def encodeLexicalOrigin (origin : LexicalOrigin) : Term :=
  .application "bnf-v1:lexical-origin"
    [.string origin.authority, .natural origin.occurrence]

def decodeLexicalOrigin : Term -> Option LexicalOrigin
  | .application "bnf-v1:lexical-origin"
      [.string authority, .natural occurrence] =>
      some { authority, occurrence }
  | _ => none

@[simp] theorem decodeLexicalOrigin_encodeLexicalOrigin
    (origin : LexicalOrigin) :
    decodeLexicalOrigin (encodeLexicalOrigin origin) = some origin := by
  cases origin
  rfl

def encodeLexicalDeclaration (declaration : LexicalDeclaration) : Term :=
  .application "bnf-v1:lexical-declaration"
    [encodeText declaration.referenceName,
      .string declaration.className,
      encodeLexicalMatcher declaration.matcher,
      .string declaration.ruleLabel,
      encodeLexicalOrigin declaration.origin]

def decodeLexicalDeclaration : Term -> Option LexicalDeclaration
  | .application "bnf-v1:lexical-declaration"
      [referenceName, .string className, matcher, .string ruleLabel, origin] => do
      let decodedReferenceName <- decodeText referenceName
      let decodedMatcher <- decodeLexicalMatcher matcher
      let decodedOrigin <- decodeLexicalOrigin origin
      some {
        referenceName := decodedReferenceName
        className
        matcher := decodedMatcher
        ruleLabel
        origin := decodedOrigin }
  | _ => none

@[simp] theorem decodeLexicalDeclaration_encodeLexicalDeclaration
    (declaration : LexicalDeclaration) :
    decodeLexicalDeclaration (encodeLexicalDeclaration declaration) =
      some declaration := by
  cases declaration
  simp [encodeLexicalDeclaration, decodeLexicalDeclaration]

def encodeLexicalDeclarations : List LexicalDeclaration -> Term
  | [] => .application "bnf-v1:lexical-declarations-nil" []
  | declaration :: rest =>
      .application "bnf-v1:lexical-declarations-cons"
        [encodeLexicalDeclaration declaration,
          encodeLexicalDeclarations rest]

def decodeLexicalDeclarations : Term -> Option (List LexicalDeclaration)
  | .application "bnf-v1:lexical-declarations-nil" [] => some []
  | .application "bnf-v1:lexical-declarations-cons"
      [declaration, rest] => do
      let decodedDeclaration <- decodeLexicalDeclaration declaration
      let decodedRest <- decodeLexicalDeclarations rest
      some (decodedDeclaration :: decodedRest)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeLexicalDeclarations_encodeLexicalDeclarations
    (declarations : List LexicalDeclaration) :
    decodeLexicalDeclarations (encodeLexicalDeclarations declarations) =
      some declarations := by
  induction declarations with
  | nil => simp [encodeLexicalDeclarations, decodeLexicalDeclarations]
  | cons declaration rest ih =>
      simp [encodeLexicalDeclarations, decodeLexicalDeclarations, ih]

def encodeGrammarAuthority (authority : GrammarAuthority) : Term :=
  .application "bnf-v1:grammar-authority"
    [.application "bnf-v1:start" [encodeText authority.startName],
      .application "bnf-v1:lexical-environment"
        [encodeLexicalDeclarations authority.lexicalDeclarations]]

def decodeGrammarAuthority : Term -> Option GrammarAuthority
  | .application "bnf-v1:grammar-authority"
      [.application "bnf-v1:start" [startName],
        .application "bnf-v1:lexical-environment" [declarations]] => do
      let decodedStartName <- decodeText startName
      let decodedDeclarations <- decodeLexicalDeclarations declarations
      some {
        startName := decodedStartName
        lexicalDeclarations := decodedDeclarations }
  | _ => none

@[simp] theorem decodeGrammarAuthority_encodeGrammarAuthority
    (authority : GrammarAuthority) :
    decodeGrammarAuthority (encodeGrammarAuthority authority) =
      some authority := by
  cases authority
  simp [encodeGrammarAuthority, decodeGrammarAuthority]

theorem encodeGrammarAuthority_injective :
    Function.Injective encodeGrammarAuthority := by
  intro left right equal
  have decoded := congrArg decodeGrammarAuthority equal
  simpa using decoded

/-! ## Complete denotation query input -/

def encodeGrammarInput
    (document : Document) (authority : GrammarAuthority) : Term :=
  .application "bnf-v1:grammar-input"
    [encodeDocument document, encodeGrammarAuthority authority]

def decodeGrammarInput : Term -> Option (Document × GrammarAuthority)
  | .application "bnf-v1:grammar-input" [document, authority] => do
      let decodedDocument <- decodeDocument document
      let decodedAuthority <- decodeGrammarAuthority authority
      some (decodedDocument, decodedAuthority)
  | _ => none

@[simp] theorem decodeGrammarInput_encodeGrammarInput
    (document : Document) (authority : GrammarAuthority) :
    decodeGrammarInput (encodeGrammarInput document authority) =
      some (document, authority) := by
  simp [encodeGrammarInput, decodeGrammarInput]

theorem encodeGrammarInput_injective :
    Function.Injective (Function.uncurry encodeGrammarInput) := by
  rintro ⟨leftDocument, leftAuthority⟩
    ⟨rightDocument, rightAuthority⟩ equal
  have decoded := congrArg decodeGrammarInput equal
  simpa [Function.uncurry] using decoded

/-! ## Discriminating malformed-wire controls -/

/-- The authored BNF empty constructors are applications, unlike the bare
`LNil` symbol used by the separate LanguageDef list protocol. -/
theorem empty_constructors_are_applications :
    encodeTextChars [] = .application "bnf-v1:text-nil" [] ∧
    encodeElements [] = .application "bnf-v1:elements-nil" [] ∧
    encodeAlternatives [] = .application "bnf-v1:alternatives-nil" [] ∧
    encodeEntries [] = .application "bnf-v1:entries-nil" [] ∧
    encodeScalars [] = .application "bnf-v1:scalars-nil" [] ∧
    encodeLexicalDeclarations [] = .application "bnf-v1:lexical-declarations-nil" [] := by
  simp [encodeTextChars, encodeElements, encodeAlternatives, encodeEntries,
    encodeScalars, encodeLexicalDeclarations]

theorem empty_constructor_symbols_are_refused :
    decodeTextChars (.symbol "bnf-v1:text-nil") = none ∧
    decodeElements (.symbol "bnf-v1:elements-nil") = none ∧
    decodeAlternatives (.symbol "bnf-v1:alternatives-nil") = none ∧
    decodeEntries (.symbol "bnf-v1:entries-nil") = none ∧
    decodeScalars (.symbol "bnf-v1:scalars-nil") = none ∧
    decodeLexicalDeclarations (.symbol "bnf-v1:lexical-declarations-nil") = none := by
  simp [decodeTextChars, decodeElements, decodeAlternatives, decodeEntries,
    decodeScalars, decodeLexicalDeclarations]

theorem empty_text_renders_with_parentheses :
    (encodeText "").render = "(bnf-v1:text-nil)" := by
  rfl

theorem text_rejects_surrogate_scalar :
    decodeText
      (.application "bnf-v1:text-cons"
        [.natural 55296, .application "bnf-v1:text-nil" []]) = none := by
  decide +kernel

theorem document_rejects_wrong_list_tail :
    decodeDocument
      (.application "bnf-v1:document"
        [.application "bnf-v1:entries-cons"
          [.application "bnf-v1:blank"
            [.application "bnf-v1:source-span" [.natural 0, .natural 0]],
            .application "bnf-v1:alternatives-nil" []],
          .application "bnf-v1:source-span" [.natural 0, .natural 0]]) = none := by
  decide +kernel

theorem authority_rejects_symbol_where_string_required :
    decodeGrammarAuthority
      (.application "bnf-v1:grammar-authority"
        [.application "bnf-v1:start" [.symbol "s"],
          .application "bnf-v1:lexical-environment"
            [.application "bnf-v1:lexical-declarations-nil" []]]) = none := by
  decide +kernel

theorem input_rejects_extra_argument :
    decodeGrammarInput
      (.application "bnf-v1:grammar-input"
        [.symbol "unexpected", .symbol "unexpected", .symbol "extra"]) = none := by
  rfl

theorem lexical_matcher_rejects_ordinary_list_encoding :
    decodeLexicalMatcher
      (.application "bnf-v1:lexical-points"
        [.application "LCons" [.natural 55, .symbol "LNil"]]) = none := by
  decide +kernel

#print axioms decodeText_encodeText
#print axioms decodeDocument_encodeDocument
#print axioms encodeDocument_injective
#print axioms decodeGrammarAuthority_encodeGrammarAuthority
#print axioms encodeGrammarAuthority_injective
#print axioms decodeGrammarInput_encodeGrammarInput
#print axioms encodeGrammarInput_injective
#print axioms text_rejects_surrogate_scalar
#print axioms document_rejects_wrong_list_tail
#print axioms authority_rejects_symbol_where_string_required
#print axioms input_rejects_extra_argument
#print axioms lexical_matcher_rejects_ordinary_list_encoding
#print axioms empty_constructors_are_applications
#print axioms empty_constructor_symbols_are_refused
#print axioms empty_text_renders_with_parentheses

end Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
