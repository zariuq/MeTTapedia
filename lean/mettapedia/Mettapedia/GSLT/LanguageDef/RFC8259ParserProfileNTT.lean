import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-!
# RFC 8259 parser-profile native-type diagnostics

The parser profile is separate authored data: it fixes the start sort, scalar
classes, and the lexical production associated with each lexical result sort.
This module records that data without making it a parser implementation.  A
byte-level decoder theorem is still needed to authenticate an external wire
file as this in-memory value.
-/

namespace Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

private def offsetRange (first count : Nat) : List Nat :=
  (List.range count).map (first + ·)

/-- The exact finite data carried by `RFC8259JsonParserV1`. -/
def rfc8259ParserProfile : ParserProfileLayer := {
  name := "RFC8259JsonParserV1"
  startSort := "JsonText"
  classes := [
    { name := "JsonWsClass", kind := .points [9, 10, 13, 32] },
    { name := "JsonUnescapedClass",
      kind := .except (List.range 32 ++ [34, 92]) },
    { name := "JsonDigitClass", kind := .points (offsetRange 48 10) },
    { name := "JsonDigit19Class", kind := .points (offsetRange 49 9) },
    { name := "JsonHexDigitClass",
      kind := .points
        (offsetRange 48 10 ++ offsetRange 65 6 ++ offsetRange 97 6) },
    { name := "JsonSimpleEscapeClass",
      kind := .points [34, 47, 92, 98, 102, 110, 114, 116] },
    { name := "JsonExpMarkClass", kind := .points [69, 101] },
    { name := "JsonSignClass", kind := .points [43, 45] }]
  states := [
    { resultSort := "JsonWsChar", className := "JsonWsClass",
      ruleLabel := "json:lex-ws" },
    { resultSort := "JsonUnescaped", className := "JsonUnescapedClass",
      ruleLabel := "json:lex-unescaped" },
    { resultSort := "JsonDigit", className := "JsonDigitClass",
      ruleLabel := "json:lex-digit" },
    { resultSort := "JsonDigit19", className := "JsonDigit19Class",
      ruleLabel := "json:lex-digit19" },
    { resultSort := "JsonHexDigit", className := "JsonHexDigitClass",
      ruleLabel := "json:lex-hexdigit" },
    { resultSort := "JsonSimpleEscape", className := "JsonSimpleEscapeClass",
      ruleLabel := "json:lex-simple-escape" },
    { resultSort := "JsonExpMark", className := "JsonExpMarkClass",
      ruleLabel := "json:lex-exp-mark" },
    { resultSort := "JsonSign", className := "JsonSignClass",
      ruleLabel := "json:lex-sign" }]
}

theorem rfc8259ParserProfile_inventory :
    rfc8259ParserProfile.classes.length = 8 ∧
    rfc8259ParserProfile.states.length = 8 := by
  decide

theorem whitespace_class_exact :
    [9, 10, 13, 32].map
        (rfc8259ParserProfile.classAccepts? "JsonWsClass") =
      [some true, some true, some true, some true] ∧
    rfc8259ParserProfile.classAccepts? "JsonWsClass" 11 = some false := by
  decide

theorem unescaped_class_boundaries :
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 31 = some false ∧
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 34 = some false ∧
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 65 = some true ∧
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 92 = some false := by
  decide

/-- Complement classes cannot admit Unicode surrogates or values beyond the
Unicode maximum. -/
theorem unescaped_rejects_non_scalars :
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 55296 = some false ∧
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 1114112 = some false := by
  decide

theorem digit_and_hex_boundaries :
    rfc8259ParserProfile.classAccepts? "JsonDigitClass" 48 = some true ∧
    rfc8259ParserProfile.classAccepts? "JsonDigit19Class" 48 = some false ∧
    rfc8259ParserProfile.classAccepts? "JsonHexDigitClass" 70 = some true ∧
    rfc8259ParserProfile.classAccepts? "JsonHexDigitClass" 71 = some false ∧
    rfc8259ParserProfile.classAccepts? "JsonHexDigitClass" 102 = some true := by
  decide

theorem lexical_rule_lookup_exact :
    rfc8259ParserProfile.lexicalRule? "JsonDigit" = some "json:lex-digit" ∧
    rfc8259ParserProfile.lexicalRule? "JsonUnescaped" =
      some "json:lex-unescaped" ∧
    rfc8259ParserProfile.lexicalRule? "JsonText" = none := by
  decide

/-- Negative control: changing the authored exclusion set changes lexical
meaning. -/
def quotationAdmittingMutation : ParserProfileLayer :=
  { rfc8259ParserProfile with
    classes := rfc8259ParserProfile.classes.map fun declaration =>
      if declaration.name == "JsonUnescapedClass" then
        { declaration with kind := .except (List.range 32 ++ [92]) }
      else
        declaration }

theorem quotation_mutation_changes_semantics :
    quotationAdmittingMutation.classAccepts? "JsonUnescapedClass" 34 = some true ∧
    rfc8259ParserProfile.classAccepts? "JsonUnescapedClass" 34 = some false := by
  decide

/-! ## Native structural schema -/

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
}

/-- Structural GSLT schema for parser-profile data.  The concrete RFC profile
above inhabits this shape; execution is supplied only after compilation into
ParserPack. -/
def parserProfileSchema : LanguageDef := {
  name := "ParserProfileLayerV1"
  types := [
    { name := "String", carrier := .builtinString },
    { name := "CodepointList", carrier := .tokenRaw },
    "LexicalClass", "LexicalClassList", "LexicalState",
    "LexicalStateList", "ParserProfile"]
  terms := [
    ctor "profile:class-points" "LexicalClass"
      [("name", "String"), ("codepoints", "CodepointList")],
    ctor "profile:class-except" "LexicalClass"
      [("name", "String"), ("excluded", "CodepointList")],
    ctor "profile:classes-empty" "LexicalClassList" [],
    ctor "profile:classes-cons" "LexicalClassList"
      [("head", "LexicalClass"), ("tail", "LexicalClassList")],
    ctor "profile:state" "LexicalState"
      [("resultSort", "String"), ("className", "String"),
       ("ruleLabel", "String")],
    ctor "profile:states-empty" "LexicalStateList" [],
    ctor "profile:states-cons" "LexicalStateList"
      [("head", "LexicalState"), ("tail", "LexicalStateList")],
    ctor "profile:layer" "ParserProfile"
      [("name", "String"), ("startSort", "String"),
       ("classes", "LexicalClassList"), ("states", "LexicalStateList")]
  ]
  equations := []
  rewrites := []
}

theorem parserProfileSchema_inventory :
    parserProfileSchema.types.length = 7 ∧
    parserProfileSchema.terms.length = 8 := by
  decide

/-- The current constructor-category projection deliberately extracts only
unary crossings.  Parser-profile constructors retain their names and payloads,
so none is unary; silently projecting away those fields would be unsound. -/
theorem parserProfileSchema_unary_crossings_empty :
    unaryCrossings parserProfileSchema = [] := by
  decide

theorem class_points_constructor_is_binary :
    ∃ rule ∈ parserProfileSchema.terms,
      rule.label = "profile:class-points" ∧
      rule.category = "LexicalClass" ∧ rule.params.length = 2 := by
  decide

theorem profile_layer_constructor_is_quaternary :
    ∃ rule ∈ parserProfileSchema.terms,
      rule.label = "profile:layer" ∧
      rule.category = "ParserProfile" ∧ rule.params.length = 4 := by
  decide

/-- A raw codepoint list cannot bypass lexical-class construction and become
a parser profile directly. -/
theorem no_codepoint_list_profile_crossing :
    ("profile:invented-direct", "CodepointList", "ParserProfile") ∉
      unaryCrossings parserProfileSchema := by
  decide

def parserProfileOSLF := langOSLF parserProfileSchema "ParserProfile"

theorem parserProfile_galois :
    GaloisConnection
      (langDiamond parserProfileSchema) (langBox parserProfileSchema) :=
  langGalois parserProfileSchema

end Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT
