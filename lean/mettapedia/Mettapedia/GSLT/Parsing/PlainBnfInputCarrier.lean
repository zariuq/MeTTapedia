import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import Mathlib.Tactic
import Std.Data.String.ToInt

/-!
# Structural Integer transport in the authored plain-BNF input carrier

The complete authored data-language wire is decoded into the existing
`LanguageDef`. The selected decoder rejects unsupported fields rather than
discarding them. Its independent re-encoding check retains every actual
type, constructor, parameter, field order, and empty operational field.

The input theorems concern the existing `Pattern` carrier and its executable
structural type check, before BNF semantic validation. This carrier identifies
an atom with a nullary application; no faithful physical S-expression codec
or native admission correspondence is asserted here. Integer leaves need
only have a successful `String.toInt?`, not canonical token spelling, Unicode
membership, machine bounds, or increasing order.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfInputCarrier

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def wireSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_grammar_v1.metta"

/-- The selected wire uses unescaped quoted names. Other string encodings
are outside this decoder, not silently normalized. -/
def name? : SExpr → Option String
  | .atom token =>
      match token.toList with
      | '"' :: characters =>
          match characters.reverse with
          | '"' :: reversed =>
              let text := reversed.reverse
              if text.all (fun c => c != '"' && c != '\\')
              then some (String.ofList text) else none
          | _ => none
      | _ => none
  | _ => none

def quotedName (name : String) : SExpr := .atom ("\"" ++ name ++ "\"")


def rows? {α : Type} (decode : SExpr → Option α) : SExpr → Option (List α)
  | .atom "LNil" => some []
  | .list [.atom "LCons", first, rest] => do
      return (← decode first) :: (← rows? decode rest)
  | _ => none
termination_by tree => sizeOf tree

def rows {α : Type} (encode : α → SExpr) : List α → SExpr
  | [] => .atom "LNil"
  | first :: rest => .list [.atom "LCons", encode first, rows encode rest]

def type? : SExpr → Option TypeDecl
  | .list [.atom "TypeDecl", name, .atom carrier] => do
      let name ← name? name
      let carrier ← match carrier with
        | "CarrierAst" => some CarrierKind.ast
        | "CarrierBuiltinInt" => some CarrierKind.builtinInt
        | "CarrierBuiltinString" => some CarrierKind.builtinString
        | _ => none
      return { name, carrier }
  | _ => none

def parameter? : SExpr → Option TermParam
  | .list [.atom "TermSimple", name, .list [.atom "TBase", sort]] => do
      return .simple (← name? name) (.base (← name? sort))
  | _ => none

def rule? : SExpr → Option GrammarRule
  | .list [.atom "GrammarRule", label, category, parameters,
      .atom "LNil", .atom "EvalNone"] => do
      let label ← name? label
      let category ← name? category
      let params ← rows? parameter? parameters
      return { label, category, params, syntaxPattern := [] }
  | _ => none

def decodeLanguage? : SExpr → Option LanguageDef
  | .list [.atom "GSLTLanguageDefWireV1", name, types, terms,
      .atom "LNil", .atom "LNil"] => do
      let name ← name? name
      let types ← rows? type? types
      let terms ← rows? rule? terms
      return { name, types, terms, equations := [], rewrites := [] }
  | _ => none

theorem wire_decodes : (decodeLanguage? wireSyntax).isSome = true := by
  simp [decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

def language : LanguageDef := (decodeLanguage? wireSyntax).get wire_decodes

theorem language_from_wire : decodeLanguage? wireSyntax = some language := by
  exact (Option.some_get wire_decodes).symm

def encodeType? (type : TypeDecl) : Option SExpr := do
  let carrier ← match type.carrier with
    | .ast => some "CarrierAst"
    | .builtinInt => some "CarrierBuiltinInt"
    | .builtinString => some "CarrierBuiltinString"
    | _ => none
  return .list [.atom "TypeDecl", quotedName type.name, .atom carrier]

def encodeParameter? : TermParam → Option SExpr
  | .simple name (.base sort) => some
      (.list [.atom "TermSimple", quotedName name, .list [.atom "TBase", quotedName sort]])
  | _ => none

def encodeRule? (rule : GrammarRule) : Option SExpr := do
  if !rule.syntaxPattern.isEmpty || rule.evalPolicy?.isSome || rule.algebra?.isSome then none
  else return .list [.atom "GrammarRule", quotedName rule.label, quotedName rule.category,
    rows id (← rule.params.mapM encodeParameter?), .atom "LNil", .atom "EvalNone"]

def encodeLanguage? (value : LanguageDef) : Option SExpr := do
  if !value.equations.isEmpty || !value.rewrites.isEmpty then none
  else return .list [.atom "GSLTLanguageDefWireV1", quotedName value.name,
    rows id (← value.types.mapM encodeType?), rows id (← value.terms.mapM encodeRule?),
    .atom "LNil", .atom "LNil"]

/-- Independent re-encoding checks all fields of the actual wire, not just
its counts or selected constructor labels. -/
theorem complete_wire_roundtrip : encodeLanguage? language = some wireSyntax := by
  simp [encodeLanguage?, encodeRule?, encodeType?, encodeParameter?, quotedName, rows,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem inventory : language.types.length = 21 ∧ language.terms.length = 29 := by
  simp [language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

def Checked (pattern : Pattern) (sort : String) : Prop :=
  checkHasType language FreeTypeContext.empty [] pattern (.base sort) = true

theorem checked_sound {pattern : Pattern} {sort : String} (checked : Checked pattern sort) :
    HasType language FreeTypeContext.empty [] pattern (.base sort) :=
  checkHasType_sound checked

theorem checked_iff {pattern : Pattern} {sort : String}
    (object : isObjectPattern pattern = true) :
    Checked pattern sort ↔ HasType language FreeTypeContext.empty [] pattern (.base sort) :=
  checkHasType_eq_true_iff object

theorem grammar_input_iff (document authority : Pattern) :
    Checked (.apply "bnf-v1:grammar-input" [document, authority]) "BnfGrammarInput" ↔
      Checked document "BnfGrammarDocument" ∧ Checked authority "BnfGrammarAuthority" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem scalar_cons_iff (head tail : Pattern) :
    Checked (.apply "bnf-v1:scalars-cons" [head, tail]) "BnfScalarList" ↔
      Checked head "Integer" ∧ Checked tail "BnfScalarList" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem authority_iff (start lexical : Pattern) :
    Checked (.apply "bnf-v1:grammar-authority" [start, lexical]) "BnfGrammarAuthority" ↔
      Checked start "BnfStartSelection" ∧ Checked lexical "BnfLexicalEnvironment" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem lexical_environment_iff (declarations : Pattern) :
    Checked (.apply "bnf-v1:lexical-environment" [declarations]) "BnfLexicalEnvironment" ↔
      Checked declarations "BnfLexicalDeclarations" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem declarations_cons_iff (head tail : Pattern) :
    Checked (.apply "bnf-v1:lexical-declarations-cons" [head, tail]) "BnfLexicalDeclarations" ↔
      Checked head "BnfLexicalDeclaration" ∧ Checked tail "BnfLexicalDeclarations" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem declaration_iff (reference className matcher label origin : Pattern) :
    Checked (.apply "bnf-v1:lexical-declaration"
      [reference, className, matcher, label, origin]) "BnfLexicalDeclaration" ↔
      Checked reference "BnfText" ∧ Checked className "String" ∧
        Checked matcher "BnfLexicalMatcher" ∧ Checked label "String" ∧
          Checked origin "BnfLexicalOrigin" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem lexical_points_iff (scalars : Pattern) :
    Checked (.apply "bnf-v1:lexical-points" [scalars]) "BnfLexicalMatcher" ↔
      Checked scalars "BnfScalarList" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem lexical_except_iff (scalars : Pattern) :
    Checked (.apply "bnf-v1:lexical-except" [scalars]) "BnfLexicalMatcher" ↔
      Checked scalars "BnfScalarList" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem lexical_origin_iff (authority occurrence : Pattern) :
    Checked (.apply "bnf-v1:lexical-origin" [authority, occurrence]) "BnfLexicalOrigin" ↔
      Checked authority "String" ∧ Checked occurrence "Integer" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem source_span_iff (start stop : Pattern) :
    Checked (.apply "bnf-v1:source-span" [start, stop]) "BnfSourceSpan" ↔
      Checked start "Integer" ∧ Checked stop "Integer" := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    LanguageDef.WellSorted.parameterType?, LanguageDef.WellSorted.matchesParameterRepresentation?,
    LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem integer_apply_iff (token : String) (arguments : List Pattern) :
    Checked (.apply token arguments) "Integer" ↔
      arguments = [] ∧ token.toInt?.isSome = true := by
  simp [Checked, checkHasType, checkBuiltinAtomHasType, carrierAcceptsAtom,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem integer_leaf (pattern : Pattern) (checked : Checked pattern "Integer") :
    ∃ token value, pattern = .apply token [] ∧ token.toInt? = some value := by
  cases pattern with
  | apply token arguments =>
      obtain ⟨rfl, parsed⟩ := (integer_apply_iff token arguments).mp checked
      exact ⟨token, token.toInt?.get parsed, rfl, (Option.some_get parsed).symm⟩
  | bvar index => simp [Checked, checkHasType] at checked
  | fvar name => simp [Checked, checkHasType, FreeTypeContext.empty] at checked
  | lambda binder body => simp [Checked, checkHasType] at checked
  | multiLambda count names body => simp [Checked, checkHasType] at checked
  | subst body replacement => simp [Checked, checkHasType] at checked
  | collection kind values rest =>
      simp [Checked, checkHasType, LanguageDef.WellSorted.bareCollectionElementType?,
        language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?] at checked

/-- An adjacent pair at an exact list position, including repeated values.
This selects existing constructor occurrences; it is not a new value carrier. -/
inductive AdjacentAt : Pattern → Nat → Pattern → Pattern → Prop where
  | here (left right tail : Pattern) :
      AdjacentAt (.apply "bnf-v1:scalars-cons"
        [left, .apply "bnf-v1:scalars-cons" [right, tail]]) 0 left right
  | next {scalars left right : Pattern} {position : Nat} (head : Pattern) :
      AdjacentAt scalars position left right →
      AdjacentAt (.apply "bnf-v1:scalars-cons" [head, scalars]) (position + 1) left right

theorem adjacent_checked {scalars left right : Pattern} {position : Nat}
    (selected : AdjacentAt scalars position left right)
    (checked : Checked scalars "BnfScalarList") :
    Checked left "Integer" ∧ Checked right "Integer" := by
  induction selected with
  | here left right tail =>
      obtain ⟨leftChecked, tailChecked⟩ := (scalar_cons_iff _ _).mp checked
      exact ⟨leftChecked, ((scalar_cons_iff _ _).mp tailChecked).1⟩
  | next head selected inductionHypothesis =>
      exact inductionHypothesis ((scalar_cons_iff _ _).mp checked).2

/-- An exact lexical declaration occurrence; duplicates are not identified. -/
inductive DeclarationAt : Pattern → Nat → Pattern → Prop where
  | here (declaration tail : Pattern) :
      DeclarationAt (.apply "bnf-v1:lexical-declarations-cons" [declaration, tail]) 0 declaration
  | next {declarations declaration : Pattern} {occurrence : Nat} (head : Pattern) :
      DeclarationAt declarations occurrence declaration →
      DeclarationAt (.apply "bnf-v1:lexical-declarations-cons" [head, declarations])
        (occurrence + 1) declaration

theorem declaration_at_checked {declarations declaration : Pattern} {occurrence : Nat}
    (selected : DeclarationAt declarations occurrence declaration)
    (checked : Checked declarations "BnfLexicalDeclarations") :
    Checked declaration "BnfLexicalDeclaration" := by
  induction selected with
  | here declaration tail => exact ((declarations_cons_iff _ _).mp checked).1
  | next head selected inductionHypothesis =>
      exact inductionHypothesis ((declarations_cons_iff _ _).mp checked).2

def inputRoot (document start declarations : Pattern) : Pattern :=
  .apply "bnf-v1:grammar-input" [document,
    .apply "bnf-v1:grammar-authority" [start,
      .apply "bnf-v1:lexical-environment" [declarations]]]

theorem input_declarations_checked (document start declarations : Pattern)
    (checked : Checked (inputRoot document start declarations) "BnfGrammarInput") :
    Checked declarations "BnfLexicalDeclarations" :=
  (lexical_environment_iff _).mp
    ((authority_iff _ _).mp ((grammar_input_iff _ _).mp checked).2).2

/-- The authored root-to-scalar route, indexed by both declaration and
adjacency occurrence. Its origin is the same untouched constructor field. -/
def InputScalarPair (input : Pattern) (declarationOccurrence scalarPosition : Nat)
    (left right origin : Pattern) : Prop :=
  ∃ document start declarations reference className matcher label scalars,
    input = inputRoot document start declarations ∧
    DeclarationAt declarations declarationOccurrence
      (.apply "bnf-v1:lexical-declaration" [reference, className, matcher, label, origin]) ∧
    (matcher = .apply "bnf-v1:lexical-points" [scalars] ∨
      matcher = .apply "bnf-v1:lexical-except" [scalars]) ∧
    AdjacentAt scalars scalarPosition left right

theorem input_pair_checked {input left right origin : Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : Checked input "BnfGrammarInput")
    (selected : InputScalarPair input declarationOccurrence scalarPosition left right origin) :
    Checked left "Integer" ∧ Checked right "Integer" ∧ Checked origin "BnfLexicalOrigin" := by
  obtain ⟨document, start, declarations, reference, className, matcher, label, scalars,
    rfl, declarationSelected, matcherSelected, adjacent⟩ := selected
  have declarationsChecked := input_declarations_checked document start declarations checked
  have declarationChecked := declaration_at_checked declarationSelected declarationsChecked
  obtain ⟨_, _, matcherChecked, _, originChecked⟩ :=
    (declaration_iff reference className matcher label origin).mp declarationChecked
  have scalarsChecked : Checked scalars "BnfScalarList" := by
    cases matcherSelected with
    | inl same => exact (lexical_points_iff scalars).mp (same ▸ matcherChecked)
    | inr same => exact (lexical_except_iff scalars).mp (same ▸ matcherChecked)
  obtain ⟨leftChecked, rightChecked⟩ := adjacent_checked adjacent scalarsChecked
  exact ⟨leftChecked, rightChecked, originChecked⟩

/-- Structural checking alone supplies Integer values for every selected
scalar-order call site. No semantic admission, Unicode test, or canonical
spelling premise participates in this implication. -/
theorem input_pair_integer_values {input left right origin : Pattern}
    {declarationOccurrence scalarPosition : Nat}
    (checked : Checked input "BnfGrammarInput")
    (selected : InputScalarPair input declarationOccurrence scalarPosition left right origin) :
    ∃ leftToken rightToken leftValue rightValue,
      left = .apply leftToken [] ∧ right = .apply rightToken [] ∧
      leftToken.toInt? = some leftValue ∧ rightToken.toInt? = some rightValue := by
  obtain ⟨leftChecked, rightChecked, _⟩ := input_pair_checked checked selected
  obtain ⟨leftToken, leftValue, leftShape, leftParsed⟩ := integer_leaf left leftChecked
  obtain ⟨rightToken, rightValue, rightShape, rightParsed⟩ := integer_leaf right rightChecked
  exact ⟨leftToken, rightToken, leftValue, rightValue,
    leftShape, rightShape, leftParsed, rightParsed⟩

/-! ## Discriminating controls -/

def controlScalars : Pattern :=
  .apply "bnf-v1:scalars-cons" [.apply (toString (-3 : Int)) [],
    .apply "bnf-v1:scalars-cons"
      [.apply (toString (1114112 : Int)) [], .apply "bnf-v1:scalars-nil" []]]

def controlOrigin : Pattern := .apply "bnf-v1:lexical-origin"
  [.apply "authority" [], .apply (toString (9223372036854775808 : Int)) []]

def controlDeclaration : Pattern := .apply "bnf-v1:lexical-declaration"
  [.apply "bnf-v1:text-nil" [], .apply "class" [],
    .apply "bnf-v1:lexical-points" [controlScalars], .apply "label" [], controlOrigin]

def controlInput : Pattern := inputRoot
  (.apply "bnf-v1:document" [.apply "bnf-v1:entries-nil" [],
    .apply "bnf-v1:source-span" [.apply (toString (-20 : Int)) [], .apply (toString (-10 : Int)) []]])
  (.apply "bnf-v1:start" [.apply "bnf-v1:text-nil" []])
  (.apply "bnf-v1:lexical-declarations-cons"
    [controlDeclaration, .apply "bnf-v1:lexical-declarations-nil" []])

/-- Negative/out-of-Unicode scalars, negative spans, and an occurrence larger
than signed Int64 remain structurally typed. Semantic bounds are separate. -/
theorem control_input_checked : Checked controlInput "BnfGrammarInput" := by
  simp only [controlInput, inputRoot, controlDeclaration, controlScalars, controlOrigin,
    grammar_input_iff, authority_iff, lexical_environment_iff, declarations_cons_iff,
    declaration_iff, lexical_points_iff, lexical_origin_iff, scalar_cons_iff,
    integer_apply_iff]
  simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
    carrierAcceptsAtom, LanguageDef.WellSorted.parameterType?,
    LanguageDef.WellSorted.matchesParameterRepresentation?, LanguageDef.WellSorted.usesBareCollection?,
    language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?, Int.toInt?_repr]

theorem control_input_pair :
    InputScalarPair controlInput 0 0
      (.apply (toString (-3 : Int)) []) (.apply (toString (1114112 : Int)) []) controlOrigin := by
  refine ⟨.apply "bnf-v1:document" [.apply "bnf-v1:entries-nil" [],
      .apply "bnf-v1:source-span" [.apply (toString (-20 : Int)) [], .apply (toString (-10 : Int)) []]],
    .apply "bnf-v1:start" [.apply "bnf-v1:text-nil" []],
    .apply "bnf-v1:lexical-declarations-cons"
      [controlDeclaration, .apply "bnf-v1:lexical-declarations-nil" []],
    .apply "bnf-v1:text-nil" [], .apply "class" [],
    .apply "bnf-v1:lexical-points" [controlScalars], .apply "label" [], controlScalars,
    rfl, ?_, Or.inl rfl, ?_⟩
  · exact .here controlDeclaration _
  · exact .here _ _ _

theorem noncanonical_integer_spelling :
    Checked (.apply "01" []) "Integer" ∧
      "01".toInt? = some 1 ∧ toString (1 : Int) ≠ "01" := by
  have spelling : "01".toList = ['0', '1'] := by decide
  have digits : "01".isNat = true :=
    String.isNat_of_isDigit (by decide) (by
      intro character member
      rw [spelling] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
  have natural : "01".toNat? = some 1 := by
    simpa [spelling, Nat.ofDigitChars] using String.toNat?_eq_some_ofDigitChars digits
  have parsed : "01".toInt? = some 1 := String.toInt?_eq_some_of_toNat?_eq_some natural
  rw [integer_apply_iff, parsed]
  simp [Int.toString_eq_repr, Int.repr_eq_if]
  decide

theorem float_not_integer : ¬ Checked (.apply "1.0" []) "Integer" := by
  have notNat : "1.0".isNat = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have character := (String.isNat_iff.mp accepted).2.1 '.' (by decide)
    simp [Char.isDigit] at character
  have parsed : "1.0".toInt? = none := by
    rw [String.toInt?_eq_toNat?_of_startsWith_eq_false (by decide), String.toNat?_eq_none notNat]
    rfl
  simp [integer_apply_iff, parsed]

theorem float_scalar_refused (tail : Pattern) :
    ¬ Checked (.apply "bnf-v1:scalars-cons" [.apply "1.0" [], tail]) "BnfScalarList" := by
  rw [scalar_cons_iff]
  exact fun accepted => float_not_integer accepted.1

theorem nonempty_integer_application_refused (token : String) (argument : Pattern) :
    ¬ Checked (.apply token [argument]) "Integer" := by
  simp [integer_apply_iff]

theorem schema_substitution_refused (body replacement : Pattern) :
    ¬ Checked (.subst body replacement) "Integer" := by
  simp [Checked, checkHasType]

theorem equal_pairs_keep_positions (value : Pattern) :
    AdjacentAt (.apply "bnf-v1:scalars-cons" [value,
      .apply "bnf-v1:scalars-cons" [value,
        .apply "bnf-v1:scalars-cons" [value, .apply "bnf-v1:scalars-nil" []]]]) 0 value value ∧
    AdjacentAt (.apply "bnf-v1:scalars-cons" [value,
      .apply "bnf-v1:scalars-cons" [value,
        .apply "bnf-v1:scalars-cons" [value, .apply "bnf-v1:scalars-nil" []]]]) 1 value value :=
  ⟨.here _ _ _, .next _ (.here _ _ _)⟩

theorem unquoted_name_refused : name? (.atom "Integer") = none := rfl

theorem extra_rule_field_refused (label category parameters extra : SExpr) :
    rule? (.list [.atom "GrammarRule", label, category, parameters,
      .atom "LNil", .atom "EvalNone", extra]) = none := rfl

theorem nonempty_operational_field_refused (name types terms rule : SExpr) :
    decodeLanguage? (.list [.atom "GSLTLanguageDefWireV1", name, types, terms,
      .list [.atom "LCons", rule, .atom "LNil"], .atom "LNil"]) = none := rfl

#print axioms complete_wire_roundtrip
#print axioms checked_sound
#print axioms scalar_cons_iff
#print axioms integer_leaf
#print axioms input_pair_integer_values
#print axioms control_input_checked

end Mettapedia.GSLT.Parsing.PlainBnfInputCarrier
