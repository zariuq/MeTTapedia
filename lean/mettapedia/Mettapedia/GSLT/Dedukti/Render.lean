import Mettapedia.GSLT.Dedukti.CousineauDowek

/-!
# Rendering a theory in the concrete syntax of Dedukti

The theory of the embedding of a pure type system, and translated terms, are
written out in the concrete syntax that the Dedukti checker reads, so that the
definitions of `CousineauDowek` can be checked by that program.  Nothing in
this module is used by a proof.

`renderEmbedding profile` is the theory: one declaration for each constant
that the profile declares, with the decoding symbols declared definable, and
one rewrite rule for each axiom and each product rule.  `renderDefinition`
is a definition of a name by a term at a type.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Render

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)

/-- A term in concrete syntax.  `names` are the names of the variables in
scope, innermost first; `fresh` numbers the next bound variable. -/
def term (names : List String) (fresh : Nat) : Term → String
  | .var index => names.getD index s!"free{index}"
  | .srt .type => "Type"
  | .srt .kind => "Kind"
  | .con name => name
  | .pi domain body =>
      s!"(x{fresh} : {term names (fresh + 1) domain} -> " ++
        s!"{term (s!"x{fresh}" :: names) (fresh + 1) body})"
  | .lam domain body =>
      s!"(x{fresh} : {term names (fresh + 1) domain} => " ++
        s!"{term (s!"x{fresh}" :: names) (fresh + 1) body})"
  | .app function argument => s!"({term names fresh function} {term names fresh argument})"

/-- The declaration of a constant.  A constant that heads a rule is declared
definable. -/
def declaration (definable : Bool) (name : String) (type : Term) : String :=
  (if definable then "def " else "") ++ s!"{name} : {term [] 0 type}.\n"

/-- A rewrite rule, with its pattern variables named. -/
def rule (patternNames : List String) (declared : RewriteRule) : String :=
  s!"[{", ".intercalate patternNames.reverse}] {term patternNames 0 declared.lhs} --> " ++
    s!"{term patternNames 0 declared.rhs}.\n"

/-- Whether a constant heads a rule of the embedding. -/
def definable : Symbol → Bool
  | .decode _ => true
  | _ => false

/-- The declarations of the embedding of a pure type system. -/
def declarations (profile : Profile) : String :=
  String.join <| Symbol.all.filterMap fun symbol =>
    (Symbol.declaredType profile symbol).map fun type =>
      declaration (definable symbol) symbol.name type

/-- The rules of the embedding of a pure type system. -/
def rules (profile : Profile) : String :=
  let sorts : List Srt := [.type, .kind]
  let codeRules := sorts.filterMap fun source =>
    (profile.sortAxiom source).map fun target => rule [] (codeRule source target)
  let prodRules := profile.products.map fun product => rule ["Y", "X"] (prodRule product)
  String.join (codeRules ++ prodRules)

/-- **The theory of the embedding**, as a Dedukti file. -/
def renderEmbedding (profile : Profile) : String :=
  declarations profile ++ rules profile

/-- A definition of a name by a term at a type. -/
def renderDefinition (name : String) (type body : Term) : String :=
  s!"def {name} : {term [] 0 type} := {term [] 0 body}.\n"

end Mettapedia.GSLT.Dedukti.Render
