import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagCompilation

/-! A ground-head ACU search pattern with one residual bag variable is a
shared matcher request. Its result is the variable's actual residual bag.
This stage selects observations; it does not add transitions to the source
rewrite system or approximate a Maude equational condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def stateSort : String := "maude:acu:query-state"
def requestName : String := "maude:acu:query"
def resultName : String := "maude:acu:solution"

structure Prepared where
  language : LanguageDef
  heads : List Maude.Term
  variableName : String

def componentName? : Maude.Term → Option String
  | .var name => some name
  | _ => none

def isHead : Maude.Term → Bool
  | .var _ => false
  | _ => true

def queryRule (operation : Maude.Operator) (heads : List Maude.Term) (variableName : String) : RewriteRule where
  name := "maude:acu:select-query"
  typeContext := [(variableName, .collection .hashBag (.base (ACUBagCompilation.tokenSort operation)))]
  premises := []
  left := .apply requestName [ACUBagPresentation.pack (ACUBagCompilation.wrapperName operation)
    heads (some variableName)]
  right := .apply resultName [.fvar variableName]

def prepare {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (base : LanguageDef) (target : Maude.Term) : Except String Prepared := do
  let parts := operation.flatten target
  let names := parts.filterMap componentName?
  let [variableName] := names | throw "this query profile requires one residual bag variable"
  let heads := parts.filter isHead
  unless heads.all (fun term => term.variables.isEmpty) do
    throw "a nonground component requires a stronger ACU query profile"
  let request : GrammarRule := {
    label := requestName, category := stateSort,
    params := [.simple "state" (.base operation.declaration.result)],
    syntaxPattern := [.terminal requestName, .nonTerminal "state"] }
  let result : GrammarRule := {
    label := resultName, category := stateSort,
    params := [.simple "rest" (.collection .hashBag (.base (ACUBagCompilation.tokenSort operation.declaration)))],
    syntaxPattern := [.terminal resultName, .nonTerminal "rest"], collectionRepresentation := .wrapped }
  let rule := queryRule operation.declaration heads variableName
  let language : LanguageDef := {base with
    name := base.name ++ ":query"
    types := base.types ++ [TypeDecl.plain stateSort]
    terms := base.terms ++ [request, result]
    rewrites := [rule] }
  unless language.validate.isEmpty do throw "the generated ACU query declarations are invalid"
  pure ⟨language, heads, variableName⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagQuery
