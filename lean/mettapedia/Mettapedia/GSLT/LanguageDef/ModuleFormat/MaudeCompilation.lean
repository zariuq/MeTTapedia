import Mettapedia.Languages.Maude.Semantics
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-! A many-sorted Maude theory compiles directly to the existing LanguageDef.
The executable terms are the declared first-order constructors. ACU laws
remain explicit equations of their selected operator; no global collection
equality or silent equation-to-rule conversion is introduced.

Equational conditions query a declared equality interface. A certified
equational decision procedure must justify that interface; a single rule
step is not an equality test. Per-module normalization/coherence and native
realization remain separate obligations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def encode : Maude.Term → Pattern
  | .var name => .fvar name
  | .app id arguments => .apply id (arguments.map encode)

def decode? : Pattern → Option Maude.Term
  | .fvar name => some (.var name)
  | .apply id arguments => .app id <$> arguments.mapM decode?
  | _ => none

def operator (declaration : Maude.Operator) : GrammarRule where
  label := declaration.id
  category := declaration.result
  params := declaration.arguments.zipIdx.map fun (sort, index) => .simple ("p" ++ toString index) (.base sort)
  syntaxPattern := .terminal declaration.id ::
    declaration.arguments.zipIdx.map (fun (_, index) => .nonTerminal ("p" ++ toString index))
  collectionRepresentation := .wrapped

def equalityRelation (sort : String) : String := "maude:equivalent:" ++ sort

def conditions? (signature : Maude.Signature) (row : Maude.Row) : Option (List Premise) :=
  row.conditions.mapM fun condition => do
    let sort ← Maude.inferSort? signature row.formals condition.left
    pure (.relationQuery (equalityRelation sort) [encode condition.left, encode condition.right])

def context (row : Maude.Row) : List (String × TypeExpr) := row.usedContext.map fun entry => (entry.1, .base entry.2)

def equation? (signature : Maude.Signature) (index : Nat) (row : Maude.Row) : Option Equation := do
  let premises ← conditions? signature row
  pure {
    name := "maude:equation:" ++ toString index
    typeContext := context row
    premises := premises
    left := encode row.left
    right := encode row.right}

def rewrite? (signature : Maude.Signature) (index : Nat) (row : Maude.Row) : Option RewriteRule := do
  let premises ← conditions? signature row
  pure {
    name := "maude:rule:" ++ toString index
    typeContext := context row
    premises := premises
    left := encode row.left
    right := encode row.right}

inductive AlgebraLaw where
  | associative | commutative | leftUnit | rightUnit
  deriving Repr, DecidableEq, BEq

def algebraRows (declaration : Maude.Operator) : List (AlgebraLaw × Maude.Row) := Id.run do
  let x := Maude.Term.var "maude:axiom:X"
  let y := Maude.Term.var "maude:axiom:Y"
  let z := Maude.Term.var "maude:axiom:Z"
  let apply := fun first second => Maude.Term.app declaration.id [first, second]
  let xy := [("maude:axiom:X", declaration.result), ("maude:axiom:Y", declaration.result)]
  let mut rows := []
  if declaration.attributes.associative then
    rows := rows ++ [(.associative, ⟨declaration.id ++ ":assoc", xy ++ [("maude:axiom:Z", declaration.result)], [],
      apply (apply x y) z, apply x (apply y z)⟩)]
  if declaration.attributes.commutative then
    let domain := declaration.arguments.headD declaration.result
    let commutativeContext := [("maude:axiom:X", domain), ("maude:axiom:Y", domain)]
    rows := rows ++ [(.commutative, ⟨declaration.id ++ ":comm", commutativeContext, [], apply x y, apply y x⟩)]
  if let some unit := declaration.attributes.identity then
    rows := rows ++ [(.leftUnit, ⟨declaration.id ++ ":left-unit", [("maude:axiom:X", declaration.result)], [],
      apply unit x, x⟩),
      (.rightUnit, ⟨declaration.id ++ ":right-unit", [("maude:axiom:X", declaration.result)], [],
      apply x unit, x⟩)]
  return rows

/-- Congruence is explicit in the compiled language. The native profile
uses root sites, so context descent is not counted a second time. -/
def congruences (declaration : Maude.Operator) : List RewriteRule :=
  declaration.arguments.zipIdx.map fun (sort, position) =>
    let fields := declaration.arguments.zipIdx.map fun (_, index) => Pattern.fvar ("maude:field:" ++ toString index)
    let replacement := Pattern.fvar "maude:replacement"
    {name := "maude:context:" ++ declaration.id ++ ":" ++ toString position,
     typeContext := ("maude:replacement", .base sort) ::
       declaration.arguments.zipIdx.map (fun (sort, index) => ("maude:field:" ++ toString index, .base sort)),
     premises := [.congruence (.fvar ("maude:field:" ++ toString position)) replacement],
     left := .apply declaration.id fields,
     right := .apply declaration.id (fields.set position replacement)}

inductive EquationOrigin where
  | authored (index : Nat)
  | algebra (operatorIndex : Nat) (law : AlgebraLaw)
  deriving Repr, DecidableEq, BEq

structure Prepared where
  source : Maude.Theory
  language : LanguageDef
  equationOrigins : List EquationOrigin
  ruleOrigins : List (Option Nat)
  terms_exact : language.terms = source.signature.operators.map operator
  sorts_exact : language.types = source.signature.sorts.map TypeDecl.plain
  deriving Repr

def prepare (theory : Maude.Theory) : Except String Prepared := do
  unless theory.check do throw "Maude core signature, variables or row sorts are invalid"
  let some equations := theory.equations.zipIdx.mapM (fun (row, index) => equation? theory.signature index row)
    | throw "Maude equational condition has no declared sort"
  let generated := theory.signature.operators.zipIdx.flatMap fun (declaration, index) =>
    (algebraRows declaration).map fun (law, row) => (index, law, row)
  let some axioms := generated.zipIdx.mapM (fun (entry, index) =>
      (equation? theory.signature (theory.equations.length + index) entry.2.2))
    | throw "Maude algebra equation encoding failed"
  let some rules := theory.rules.zipIdx.mapM (fun (row, index) => rewrite? theory.signature index row)
    | throw "Maude rule condition has no declared sort"
  let contexts := theory.signature.operators.flatMap congruences
  let language : LanguageDef := {
    name := theory.name
    types := theory.signature.sorts.map TypeDecl.plain
    terms := theory.signature.operators.map operator
    equations := equations ++ axioms
    rewrites := rules ++ contexts}
  unless language.validate.isEmpty do throw s!"Maude core declarations are invalid: {reprStr language.validate}"
  pure ⟨theory, language,
    (theory.equations.zipIdx.map fun (_, index) => .authored index) ++
      generated.map (fun entry => .algebra entry.1 entry.2.1),
    (theory.rules.zipIdx.map fun (_, index) => some index) ++ contexts.map (fun _ => none), rfl, rfl⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
