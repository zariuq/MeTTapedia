import Mettapedia.OSLF.Syntax.JsonTermRung
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.LanguageDefSignature

/-!
# The authored JSON data presentation and its list desugaring

The book gives two algebraic result sorts, Value and Field. Its scalar
parameters are external data, while `List(Value)` and `List(Field)` are
ordered constructor arguments. The intrinsic signature makes those two list
sorts and their constructors explicit. This module records the authoring
declaration and checks the constructor inventory and its desugaring boundary.
The `BigRat` authoring sort is an external scalar parameter; it does not
claim that raw source tokens are already parsed as Lean rationals.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.JsonAuthoredComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.JsonTermRung
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.LanguageDefSignature

private def value : TypeExpr := .base "Value"
private def field : TypeExpr := .base "Field"
private def bool : TypeExpr := .base "Bool"
private def bigRat : TypeExpr := .base "BigRat"
private def str : TypeExpr := .base "Str"

/-- The Chapter 7 JSON constructor presentation. Ordered lists are authored
as `vec` parameters; the intrinsic signature exposes their nil/cons grammar. -/
def authored : LanguageDef :=
  { name := "Json"
    types := [
      { name := "Bool", carrier := .builtinBool },
      { name := "BigRat", carrier := .ast },
      { name := "Str", carrier := .builtinString },
      "Value", "Field"]
    terms := [
      { label := "JNull", category := "Value", params := [],
        syntaxPattern := [.terminal "null"] },
      { label := "JBool", category := "Value",
        params := [.simple "b" bool], syntaxPattern := [.nonTerminal "b"] },
      { label := "JNum", category := "Value",
        params := [.simple "n" bigRat], syntaxPattern := [.nonTerminal "n"] },
      { label := "JStr", category := "Value",
        params := [.simple "s" str], syntaxPattern := [.nonTerminal "s"] },
      { label := "JArr", category := "Value",
        params := [.simple "values" (.vec value)],
        syntaxPattern := [.terminal "[", .nonTerminal "values", .terminal "]"] },
      { label := "JObj", category := "Value",
        params := [.simple "fields" (.vec field)],
        syntaxPattern := [.terminal "{", .nonTerminal "fields", .terminal "}"] },
      { label := "Field", category := "Field",
        params := [.simple "k" str, .simple "v" value],
        syntaxPattern := [.nonTerminal "k", .terminal ":", .nonTerminal "v"] }]
    equations := []
    rewrites := [] }

theorem authored_inventory :
    authored.types.length = 5 ∧ authored.terms.length = 7 ∧
      authored.equations = [] ∧ authored.rewrites = [] := by
  decide

/-- All seven authored data constructors retain their source labels and
result sorts; the extra intrinsic constructors belong only to list expansion. -/
theorem authored_constructor_results :
    authored.terms.map (fun term => (term.label, term.category)) =
      [("JNull", "Value"), ("JBool", "Value"),
       ("JNum", "Value"), ("JStr", "Value"),
       ("JArr", "Value"), ("JObj", "Value"),
       ("Field", "Field")] := by
  decide

/-- The source's two implicit ordered-list arguments are exactly the two
parameters expanded to list sorts in the intrinsic signature. -/
theorem ordered_list_parameters :
    (authored.terms.get ⟨4, by decide⟩).params =
      [.simple "values" (.vec value)] ∧
    (authored.terms.get ⟨5, by decide⟩).params =
      [.simple "fields" (.vec field)] := by
  decide

/-- The retained base-only signature compiler sees the scalar argument of
`JBool` but correctly refuses to flatten the ordered-list argument of `JArr`.
The two list sorts in the intrinsic signature are necessary desugaring data. -/
theorem base_signature_boundary :
    parameterBaseSorts? (authored.terms.get ⟨1, by decide⟩).params =
      some ["Bool"] ∧
    parameterBaseSorts? (authored.terms.get ⟨4, by decide⟩).params =
      none := by
  decide

private theorem authored_terms_valid :
    ∀ term ∈ authored.terms, LanguageDef.validateTerm authored term = [] := by
  intro term membership
  simp only [authored, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide [LanguageDef.validateTerm, authored,
    LanguageDef.typeNames, value, field, bool, bigRat, str,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]

/-- The authored record passes the canonical structural validation gate. -/
theorem authored_valid : authored.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide
  · decide
  · decide
  · decide
  · exact authored_terms_valid
  · intro equation membership
    simp [authored] at membership
  · intro rewrite membership
    simp [authored] at membership

/-- Each source scalar constructor is represented by a family of nullary
intrinsic operators indexed by the interpreted scalar value. -/
theorem scalar_operator_arities (b : Bool) (n : Rat) (s : String) :
    sig.arity (Op.bool b) = [] ∧
    sig.arity (Op.num n) = [] ∧
    sig.arity (Op.str s) = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The object and array constructors consume the explicit list sorts. -/
theorem collection_operator_arities :
    sig.arity Op.arr = [([], Srt.values)] ∧
    sig.arity Op.obj = [([], Srt.fields)] := by
  exact ⟨rfl, rfl⟩

end Mettapedia.OSLF.Binding.JsonAuthoredComparison
