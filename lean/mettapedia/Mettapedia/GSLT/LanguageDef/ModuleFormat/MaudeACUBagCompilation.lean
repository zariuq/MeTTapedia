import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagPresentation
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Ground transition rows of a flat ACU carrier lower to the existing
wrapped-bag rule profile. Source equations and conditional rows require
their separate realizers and are refused here. This compilation boundary
does not itself supply a module's normalization or coherence certificate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open ACUBagPresentation

def wrapperName (declaration : Maude.Operator) : String := "maude:acu:bag:" ++ declaration.id
def tokenSort (declaration : Maude.Operator) : String := "maude:acu:token:" ++ declaration.result
def restName : String := "maude:acu:rest"

def wrapperDeclaration (declaration : Maude.Operator) : GrammarRule where
  label := wrapperName declaration
  category := declaration.result
  params := [.simple "items" (.collection .hashBag (.base (tokenSort declaration)))]
  syntaxPattern := [.terminal (wrapperName declaration), .nonTerminal "items"]
  collectionRepresentation := .wrapped

def tokenDeclaration (operation token : Maude.Operator) : GrammarRule where
  label := token.id
  category := tokenSort operation
  params := []
  syntaxPattern := [.terminal token.id]

def compileRule {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (row : Maude.Row) (index : Nat) : RewriteRule where
  name := "maude:acu:rule:" ++ toString index ++ ":" ++ row.name
  typeContext := [(restName, .collection .hashBag (.base (tokenSort operation.declaration)))]
  premises := []
  left := pack (wrapperName operation.declaration) (operation.flatten row.left) (some restName)
  right := pack (wrapperName operation.declaration) (operation.flatten row.right) (some restName)

def flatToken (declaration : Maude.Operator) (term : Maude.Term) : Bool :=
  match term with
  | .app label [] => label != declaration.id
  | _ => false

def prepare {theory : Maude.Theory} (operation : Maude.ACUOperation theory []) : Except String LanguageDef := do
  unless theory.check do throw "the source theory is ill-sorted"
  unless theory.equations.isEmpty do throw "source equations require their certified equation realizer"
  unless theory.signature.sorts == [operation.declaration.result] do
    throw "the flat ACU transition profile requires a single carrier sort"
  unless theory.signature.operators.all (fun declaration =>
      declaration.id == operation.declaration.id ||
        (declaration.arguments.isEmpty && declaration.result == operation.declaration.result)) do
    throw "a non-token constructor requires a recursive ACU presentation"
  for row in theory.rules do
    unless row.conditions.isEmpty do throw "conditional rows require their certified premise realizer"
    unless row.left.variables.isEmpty && row.right.variables.isEmpty do
      throw "this transition profile requires ground source rows"
    unless (operation.flatten row.left ++ operation.flatten row.right).all (flatToken operation.declaration) do
      throw "a source row contains a non-token ACU component"
  let tokens := theory.signature.operators.filter (fun declaration =>
    declaration.id != operation.declaration.id && some (.app declaration.id []) != some operation.unit)
  let language : LanguageDef := {
    name := theory.name ++ ":ACU-transitions"
    types := [TypeDecl.plain operation.declaration.result, TypeDecl.plain (tokenSort operation.declaration)]
    terms := wrapperDeclaration operation.declaration :: tokens.map (tokenDeclaration operation.declaration)
    equations := []
    rewrites := theory.rules.zipIdx.map fun (row, index) => compileRule operation row index }
  unless language.validate.isEmpty do throw "the generated ACU bag language is invalid"
  pure language

def plan (language : LanguageDef) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨language, [], {signatures := [], rows := []}⟩
    {sites := .rootOnly, includeDerivedEquations := false}

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagCompilation
