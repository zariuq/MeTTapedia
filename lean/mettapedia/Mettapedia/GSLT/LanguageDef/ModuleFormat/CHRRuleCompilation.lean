import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
import Mettapedia.Languages.CHR.Admission
import Mettapedia.Languages.CHR.Operational
import Mathlib.Data.Nat.Digits.Defs
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! General CHR head compilation to ordinary GSLT bag rules. Each authored
head occurrence has one request constructor; the refined controller chooses
that constructor in rule/head order. Matching returns an ordered environment,
selected occurrences and the untouched bag remainder. It performs neither a
guard nor a commit. Literal pools bind constants before the store is matched.
No grounding enumeration or source-syntax tree is used in execution. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace CHRMatchAuthoring
#module_tree "../../../../../../metta/gslt/module/CHRMatch.module" as Match
end CHRMatchAuthoring

namespace CHRCompilation

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.CHR
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def baseLanguage? : Option LanguageDef := CHRMatchAuthoring.Match.language.toOption
def baseLanguage : LanguageDef := module_language_view% baseLanguage?
theorem baseLanguage_exact : baseLanguage? = some baseLanguage := by decide +kernel

structure Vocabulary where
  predicates : List String
  scalars : List Value
  deriving Repr, DecidableEq

def valueLeaves : Value → List Value
  | .tuple fields => fields.flatMap valueLeaves
  | datum => [datum]

def termLeaves : Mettapedia.Languages.CHR.Term → List Value
  | .value datum => valueLeaves datum
  | .var _ => []
  | .tuple fields => fields.flatMap termLeaves

def headLeaves (head : Head) : List Value := head.arguments.flatMap termLeaves

def guardLeaves : Mettapedia.Languages.CHR.Guard → List Value
  | .identical left right | .distinct left right => termLeaves left ++ termLeaves right
  | .compare _ _ _ => []

def vocabulary (program : Program) (seeds : List Constraint) : Vocabulary :=
  ⟨(program.declarations.map Declaration.name).eraseDups,
   ((program.rules.flatMap fun rule => rule.heads.flatMap headLeaves ++ rule.guards.flatMap guardLeaves ++
       rule.body.flatMap fun goal => match goal with | .tell head => headLeaves head | _ => []) ++
      seeds.flatMap fun constraint => constraint.arguments.flatMap valueLeaves).eraseDups⟩

def predicateSlot (index : Nat) : String := "chr:pool:predicate:" ++ toString index
def scalarSlot (index : Nat) : String := "chr:pool:scalar:" ++ toString index
def variableSlot (index : Nat) : String := "chr:variable:" ++ toString index
def idSlot (index active : Nat) : String := if index == active then "chr:active" else "chr:head:" ++ toString index
def predicateRef (index : Nat) : Pattern := .fvar ("chr:predicate:" ++ toString index)
def scalarRef (index : Nat) : Pattern := .fvar ("chr:scalar:" ++ toString index)
def digits (index : Nat) : Pattern := .collection .vec
  ((Nat.digits 16 index).map (fun digit => .apply ("R16Nibble" ++ toString digit) [])) none
def integer (number : Int) : Pattern := .apply "ChrIntegerDigits"
  [.apply (if number < 0 then "ChrNegative" else "ChrNonnegative") [], digits number.natAbs]
def occurrenceRef (index : Nat) : Pattern := .apply "ChrOccurrenceNumber" [digits index]
def queryLabel (index : Nat) : String := "ChrMatchQuery:" ++ toString index

def vector (items : List Pattern) : Pattern := .collection .vec items none
def heads (items : List Pattern) : Pattern := .apply "ChrHeads" [vector items]
def store (items : List Pattern) : Pattern := .apply "ChrStore" [.collection .hashBag items none]
def occurrence (id constraint : Pattern) : Pattern := .apply "ChrOccurrence" [id, constraint]

def value? (vocabulary : Vocabulary) : Value → Option Pattern
  | .integer number => some (integer number)
  | .tuple fields => do pure (.apply "ChrTuple" [vector (← fields.mapM (value? vocabulary))])
  | datum => scalarRef <$> vocabulary.scalars.idxOf? datum

def literal? (vocabulary : Vocabulary) : Value → Option Pattern
  | .tuple fields => do pure (.apply "ChrTuple" [vector (← fields.mapM (literal? vocabulary))])
  | datum => (fun index => Pattern.fvar (scalarSlot index)) <$> vocabulary.scalars.idxOf? datum

def term? (vocabulary : Vocabulary) : Mettapedia.Languages.CHR.Term → Option Pattern
  | .value datum => literal? vocabulary datum
  | .var index => some (.fvar (variableSlot index))
  | .tuple fields => do pure (.apply "ChrTuple" [vector (← fields.mapM (term? vocabulary))])

def head? (vocabulary : Vocabulary) (head : Head) : Option Pattern := do
  let predicate ← vocabulary.predicates.idxOf? head.name
  pure (.apply "ChrConstraint" [.fvar (predicateSlot predicate), vector (← head.arguments.mapM (term? vocabulary))])

def constraint? (vocabulary : Vocabulary) (constraint : Constraint) : Option Pattern := do
  let predicate ← vocabulary.predicates.idxOf? constraint.name
  pure (.apply "ChrConstraint" [predicateRef predicate, vector (← constraint.arguments.mapM (value? vocabulary))])

def poolPatterns (vocabulary : Vocabulary) : List Pattern :=
  [vector ((List.range vocabulary.predicates.length).map (fun index => .fvar (predicateSlot index))),
   vector ((List.range vocabulary.scalars.length).map (fun index => .fvar (scalarSlot index)))]

def request (vocabulary : Vocabulary) (query active : Nat) (contents : List Pattern) : Pattern :=
  .apply (queryLabel query)
    [vector ((List.range vocabulary.predicates.length).map predicateRef),
     vector (vocabulary.scalars.zipIdx.map (fun (datum,index) =>
       match datum with | .integer number => integer number | _ => scalarRef index)), occurrenceRef active, store contents]

def queryDeclaration (index : Nat) : GrammarRule :=
  { label := queryLabel index
    category := "ChrMatchState"
    params := [.simple "predicates" (.collection .vec (.base "ChrAtom")),
      .simple "scalars" (.collection .vec (.base "ChrValue")),
      .simple "active" (.base "ChrOccurrenceId"), .simple "store" (.base "ChrStoreData")]
    syntaxPattern := [.terminal (queryLabel index), .nonTerminal "predicates", .nonTerminal "scalars",
      .nonTerminal "active", .nonTerminal "store"] }

def variableContext (vocabulary : Vocabulary) (rule : Rule) (active : Nat) : List (String × TypeExpr) :=
  ((List.range vocabulary.predicates.length).map fun index => (predicateSlot index, .base "ChrAtom")) ++
  ((List.range vocabulary.scalars.length).map fun index => (scalarSlot index, .base "ChrValue")) ++
  (rule.variables.eraseDups.map fun index => (variableSlot index, .base "ChrValue")) ++
  ((List.range rule.heads.length).map fun index => (idSlot index active, .base "ChrOccurrenceId")) ++
  [("chr:rest", .collection .hashBag (.base "ChrOccurrenceData"))]

def compileRule? (vocabulary : Vocabulary) (query active : Nat) (rule : Rule) : Option RewriteRule := do
  if active < rule.heads.length then
    let selected ← rule.heads.zipIdx.mapM fun (head,index) => do
      pure (occurrence (.fvar (idSlot index active)) (← head? vocabulary head))
    let kept := selected.take rule.kept.length
    let removed := selected.drop rule.kept.length
    pure {
      name := "chr-query:" ++ toString query
      typeContext := variableContext vocabulary rule active
      premises := []
      left := .apply (queryLabel query) (poolPatterns vocabulary ++
        [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]])
      right := .apply "ChrMatched" [vector (rule.variables.eraseDups.map (fun index => .fvar (variableSlot index))),
        heads kept, heads removed, .apply "ChrStore" [.fvar "chr:rest"]] }
  else none

structure Entry where
  occurrence : RuleOccurrence
  boundVariables : List Nat
  rule : RewriteRule
  deriving Repr

structure Prepared where
  program : Program
  vocabulary : Vocabulary
  entries : List Entry
  compiled : LanguageDef
  deriving Repr

def prepare (program : Program) (seeds : List Constraint) : Except String Prepared := do
  if let some diagnostic := Admission.diagnose program then
    throw s!"CHR admission refused: {reprStr diagnostic}"
  if let some constraint := seeds.find? (fun constraint =>
      !program.declarations.any (fun declaration => declaration.name == constraint.name &&
        declaration.arity == constraint.arguments.length)) then
    throw s!"input constraint is undeclared: {reprStr constraint}"
  let vocabulary := vocabulary program seeds
  let entries ← (occurrences program).zipIdx.mapM fun (occurrence,query) => do
    let some rule := program.rules[occurrence.rule]? | throw "invalid authored rule occurrence"
    let some compiled := compileRule? vocabulary query occurrence.head rule | throw "CHR head compilation refused"
    pure (Entry.mk occurrence rule.variables.eraseDups compiled)
  let language : LanguageDef := { baseLanguage with
    name := "CHRCompiledMatch"
    terms := baseLanguage.terms ++ (List.range entries.length).map queryDeclaration
    rewrites := entries.map Entry.rule }
  if !language.validate.isEmpty then throw s!"compiled CHR declarations are invalid: {reprStr language.validate}"
  pure ⟨program, vocabulary, entries, language⟩

def freeTypes (prepared : Prepared) : List (String × TypeExpr) :=
  ((List.range prepared.vocabulary.predicates.length).map fun index =>
    ("chr:predicate:" ++ toString index, .base "ChrAtom")) ++
  ((List.range prepared.vocabulary.scalars.length).map fun index =>
    ("chr:scalar:" ++ toString index, .base "ChrValue"))

def snapshot (prepared : Prepared) : GeneralExecutionAdmission.Snapshot :=
  ⟨prepared.compiled, freeTypes prepared, {signatures := [], rows := []}⟩
def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def plan (prepared : Prepared) := GeneralExecutionAdmission.compile (snapshot prepared) permissions

end CHRCompilation
end Mettapedia.GSLT.LanguageDef.ModuleFormat
