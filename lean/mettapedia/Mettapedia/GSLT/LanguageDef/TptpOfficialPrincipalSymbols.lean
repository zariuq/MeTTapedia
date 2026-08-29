import Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

/-!
# Principal-symbol extraction from the official TPTP AST

TSTP `new_symbols` records name official `principal_symbol` values: ordinary
functors or variables.  This module extracts exactly those constructors from
an admitted formula tree.  It does not infer symbol identity from rendered
text and it does not classify defined or system symbols as user-introduced
principal symbols.

The traversal is shared by every TPTP family because the all-family grammar
uses the same `functor` and `variable` constructors below FOF, TFF, TCF, THF,
and NHF formula nodes.  A non-AST MeTTa pattern fails closed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

structure PrincipalSymbolId where
  kind : PrincipalSymbolKind
  name : String
  deriving DecidableEq, Repr

def PrincipalSymbol.id (symbol : PrincipalSymbol) : PrincipalSymbolId :=
  { kind := symbol.kind, name := symbol.name }

def decodePrincipalSymbolNode? : Pattern -> Option PrincipalSymbolId
  | .apply "tptp92-ast:functor:alt-1" [word] => do
      let name <- decodeAtomicWord? word
      some { kind := .functor, name }
  | .apply "tptp92-ast:variable:alt-1" [token] => do
      let name <- decodeLexeme? token
      some { kind := .variable, name }
  | _ => none

mutual
  /-- Extract principal-symbol occurrences in exact left-to-right AST order.
  Recognized principal-symbol nodes are leaves of this traversal, so their
  lexical representation is not visited a second time. -/
  def collectPrincipalSymbols? : Pattern -> Option (List PrincipalSymbolId)
    | pattern@(.apply "tptp92-ast:functor:alt-1" [_]) =>
        return [← decodePrincipalSymbolNode? pattern]
    | pattern@(.apply "tptp92-ast:variable:alt-1" [_]) =>
        return [← decodePrincipalSymbolNode? pattern]
    | .apply _ arguments => collectPrincipalSymbolsList? arguments
    | _ => none

  def collectPrincipalSymbolsList? : List Pattern ->
      Option (List PrincipalSymbolId)
    | [] => some []
    | pattern :: patterns => do
        let first <- collectPrincipalSymbols? pattern
        let rest <- collectPrincipalSymbolsList? patterns
        some (first ++ rest)
end

def principalSymbolSet? (formula : Pattern) : Option (Finset PrincipalSymbolId) :=
  (collectPrincipalSymbols? formula).map List.toFinset

namespace Canary

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def word (name : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1" [
    a "tptp92-ast:token:lower-word" [a name]]

def functor (name : String) : Pattern :=
  a "tptp92-ast:functor:alt-1" [word name]

def variableNode (name : String) : Pattern :=
  a "tptp92-ast:variable:alt-1" [
    a "tptp92-ast:token:upper-word" [a name]]

def constantTerm (name : String) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [functor name]]]]

def variableTerm (name : String) : Pattern :=
  a "tptp92-ast:fof-term:alt-2" [variableNode name]

def arguments : Pattern :=
  a "tptp92-ast:fof-arguments:alt-2" [
    constantTerm "a",
    a "tptp92-ast:fof-arguments:alt-1" [variableTerm "X"]]

def formula : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-2" [
        functor "p", arguments]]]

theorem formula_occurrences_preserve_kind_name_and_order :
    collectPrincipalSymbols? formula = some [
      { kind := .functor, name := "p" },
      { kind := .functor, name := "a" },
      { kind := .variable, name := "X" }] := by
  rfl

theorem formula_symbol_set_is_exact :
    principalSymbolSet? formula = some ([
      { kind := .functor, name := "p" },
      { kind := .functor, name := "a" },
      { kind := .variable, name := "X" }].toFinset) := by
  rfl

theorem malformed_functor_fails_closed :
    collectPrincipalSymbols?
      (a "tptp92-ast:functor:alt-1" [a "not-an-atomic-word"]) = none := by
  rfl

theorem non_ast_pattern_fails_closed :
    collectPrincipalSymbols? (.fvar "not-official-ast") = none := by
  rfl

end Canary

#print axioms Canary.formula_occurrences_preserve_kind_name_and_order
#print axioms Canary.formula_symbol_set_is_exact
#print axioms Canary.malformed_functor_fails_closed
#print axioms Canary.non_ast_pattern_fails_closed

end Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
