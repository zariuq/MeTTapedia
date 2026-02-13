import Mettapedia.OSLF.MeTTaCore.Atomspace
import Mettapedia.OSLF.MeTTaCore.Types
import Mettapedia.OSLF.MeTTaCore.MinimalOps
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# MeTTaCore Premise Environment (Atomspace-Backed)

Argument-dependent relation environment for MeTTa-style premise queries.
This file provides a first Atomspace-backed relation family used by
`MeTTaCore.FullLanguageDef`.
-/

namespace Mettapedia.OSLF.MeTTaCore.Premises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Canonical atom constants used across first MeTTaFull premise relations. -/
private def aTrue : Pattern := .apply "ATrue" []
private def aFalse : Pattern := .apply "AFalse" []
private def tyBool : Pattern := .apply "Bool" []
private def tyAtom : Pattern := .apply "Atom" []
private def tyInt : Pattern := .apply "Int" []
private def tyString : Pattern := .apply "String" []

/-- Encode collection tags into atom symbols. -/
private def collTag : CollType → String
  | .vec => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

/-- Read a token from `apply token []`. -/
private def tokenOfPattern? : Pattern → Option String
  | .apply tok [] => some tok
  | _ => none

/-- Bridge from MeTTaIL patterns to MeTTaCore atoms. -/
partial def patternToCoreAtom : Pattern → Atom
  | .apply "GBoolTrue" [] => .grounded (.bool true)
  | .apply "GBoolFalse" [] => .grounded (.bool false)
  | .apply "GInt" [tok] =>
      match tokenOfPattern? tok with
      | some s =>
          match s.toInt? with
          | some n => .grounded (.int n)
          | none => .expression [.symbol "GInt", patternToCoreAtom tok]
      | none => .expression [.symbol "GInt", patternToCoreAtom tok]
  | .apply "GString" [tok] =>
      match tokenOfPattern? tok with
      | some s => .grounded (.string s)
      | none => .expression [.symbol "GString", patternToCoreAtom tok]
  | .bvar n => .var s!"_b{n}"
  | .fvar x => .var x
  | .apply ctor args =>
      if args.isEmpty then
        .symbol ctor
      else
        .expression (.symbol ctor :: args.map patternToCoreAtom)
  | .lambda body =>
      .expression [.symbol "λ", patternToCoreAtom body]
  | .multiLambda n body =>
      .expression [.symbol "λ*", .grounded (.int n), patternToCoreAtom body]
  | .subst body repl =>
      .expression [.symbol "subst", patternToCoreAtom body, patternToCoreAtom repl]
  | .collection ct elems rest =>
      let elemsA := elems.map patternToCoreAtom
      let restA := rest.map (fun r => [.var r]) |>.getD []
      .expression (.symbol (collTag ct) :: elemsA ++ restA)

/-- Partial bridge from MeTTaCore atoms to MeTTaIL patterns. -/
partial def coreAtomToPattern? : Atom → Option Pattern
  | .var x => some (.fvar x)
  | .symbol s => some (.apply s [])
  | .grounded (.bool true) => some (.apply "GBoolTrue" [])
  | .grounded (.bool false) => some (.apply "GBoolFalse" [])
  | .grounded (.int n) => some (.apply "GInt" [(.apply s!"{n}" [])])
  | .grounded (.string s) => some (.apply "GString" [(.apply s [])])
  | .expression [] => none
  | .expression (.symbol ctor :: args) => do
      let ps ← args.mapM coreAtomToPattern?
      pure (.apply ctor ps)
  | .expression _ => none

/-- Canonical `Space0` atomspace used by the first full MeTTa slice. -/
def space0Atomspace : Atomspace :=
  (Atomspace.empty
    |>.addEquation (.symbol "ATrue") (.symbol "AFalse")
    |>.addEquation (.symbol "AFalse") (.symbol "ATrue")
    |>.addType (.symbol "ATrue") (.symbol "Bool")
    |>.addType (.symbol "AFalse") (.symbol "Bool")
    |>.addType (.symbol "ATrue") (.symbol "Atom")
    |>.addType (.symbol "AFalse") (.symbol "Atom"))

/-- Canonical `Space0` entries in pattern form. -/
def space0Entries : List Pattern :=
  [ .apply "=" [aTrue, aFalse]
  , .apply "=" [aFalse, aTrue]
  , .apply ":" [aTrue, tyBool]
  , .apply ":" [aFalse, tyBool]
  , .apply ":" [aTrue, tyAtom]
  , .apply ":" [aFalse, tyAtom]
  ]

/-- Extract entry lists from collection-shaped payloads. -/
private def entriesOfCollection? : Pattern → Option (List Pattern)
  | .collection _ elems _ => some elems
  | _ => none

/-- Decode a space term into explicit equation/type entries.

Supported encodings:
- `Space0`
- `Space` (empty)
- `Space payload` where payload is a collection
- `Space eqs tys` where both are collections
- `SpaceEqs eqs`, `SpaceTypes tys`
- raw collections (interpreted as entries directly)
-/
def spaceEntriesOfPattern? : Pattern → Option (List Pattern)
  | .apply "Space0" [] => some space0Entries
  | .apply "Space" [] => some []
  | .apply "Space" [payload] =>
      match entriesOfCollection? payload with
      | some entries => some entries
      | none => some [payload]
  | .apply "Space" [eqs, tys] =>
      match entriesOfCollection? eqs, entriesOfCollection? tys with
      | some eqEntries, some tyEntries => some (eqEntries ++ tyEntries)
      | _, _ => some [eqs, tys]
  | .apply "SpaceEqs" [eqs] => entriesOfCollection? eqs
  | .apply "SpaceTypes" [tys] => entriesOfCollection? tys
  | .collection _ entries _ => some entries
  | _ => none

/-- Build an atomspace from a list of encoded entries. -/
def atomspaceOfEntries (entries : List Pattern) : Atomspace :=
  Atomspace.ofList (entries.map patternToCoreAtom)

/-- Decode a space term into a concrete atomspace model. -/
def atomspaceOfPattern? : Pattern → Option Atomspace
  | space =>
      match spaceEntriesOfPattern? space with
      | some entries => some (atomspaceOfEntries entries)
      | none => none

/-- Extract RHS when an entry is an equation with matching source. -/
private def eqnRhsForSrc? (src : Pattern) : Pattern → Option Pattern
  | .apply "=" [lhs, rhs] =>
      if lhs == src then some rhs else none
  | _ => none

/-- Atomspace-backed tuples for `eqnLookup(space, src, dst)`. -/
def eqnLookupTuples : List Pattern → List (List Pattern)
  | [space, src, _dst] =>
      match spaceEntriesOfPattern? space with
      | none => []
      | some entries =>
          (entries.filterMap (eqnRhsForSrc? src)).map fun dst =>
            [space, src, dst]
  | _ => []

/-- Tuples for `noEqnLookup(space, src)` (explicit fallback trigger). -/
def noEqnLookupTuples : List Pattern → List (List Pattern)
  | [space, src] =>
      if (eqnLookupTuples [space, src, .fvar "_"]) = [] then
        [[space, src]]
      else
        []
  | _ => []

/-- Tuples for inequality checks `neq(lhs, rhs)`. -/
def neqTuples : List Pattern → List (List Pattern)
  | [lhs, rhs] =>
      if lhs == rhs then
        []
      else
        [[lhs, rhs]]
  | _ => []

/-- Tuples for `typeOf(space, atom, ty)`. -/
private def checkTypeWithAnnotations (space : Atomspace) (atom ty : Atom) : Bool :=
  checkType space atom ty || space.contains (typeAnnotation atom ty)

/-- Tuples for `typeOf(space, atom, ty)`. -/
def typeOfTuples : List Pattern → List (List Pattern)
  | [space, atom, ty] =>
      match atomspaceOfPattern? space with
      | none => []
      | some asp =>
          if checkTypeWithAnnotations asp (patternToCoreAtom atom) (patternToCoreAtom ty) then
            [[space, atom, ty]]
          else
            []
  | _ => []

/-- Tuples for `notTypeOf(space, atom, ty)`. -/
def notTypeOfTuples : List Pattern → List (List Pattern)
  | [space, atom, ty] =>
      if (typeOfTuples [space, atom, ty]).isEmpty then
        [[space, atom, ty]]
      else
        []
  | _ => []

/-- Tuples for `cast(space, atom, ty, out)` (first slice: identity cast when typable). -/
def castTuples : List Pattern → List (List Pattern)
  | [space, atom, ty, _out] =>
      match atomspaceOfPattern? space with
      | none => []
      | some asp =>
          if checkTypeWithAnnotations asp (patternToCoreAtom atom) (patternToCoreAtom ty) then
            [[space, atom, ty, atom]]
          else
            []
  | _ => []

/-- Tuples for `notCast(space, atom, ty)` fallback branching. -/
def notCastTuples : List Pattern → List (List Pattern)
  | [space, atom, ty] =>
      if (castTuples [space, atom, ty, .fvar "_"]).isEmpty then
        [[space, atom, ty]]
      else
        []
  | _ => []

/-- Parse boolean payload from symbolic or grounded boolean atoms. -/
private def boolOfPattern? : Pattern → Option Bool
  | .apply "ATrue" [] => some true
  | .apply "AFalse" [] => some false
  | .apply "GBoolTrue" [] => some true
  | .apply "GBoolFalse" [] => some false
  | _ => none

/-- Canonical symbolic bool output for relation tuples. -/
private def patternOfBool (b : Bool) : Pattern :=
  if b then aTrue else aFalse

/-- Single-step grounded call relation for boolean core ops. -/
def groundedCallTuples : List Pattern → List (List Pattern)
  | [op, arg, _out] =>
      match op, boolOfPattern? arg with
      | .apply "not" [], some b => [[op, arg, patternOfBool (!b)]]
      | _, _ => []
  | [op, lhs, rhs, _out] =>
      match op, boolOfPattern? lhs, boolOfPattern? rhs with
      | .apply "and" [], some b1, some b2 => [[op, lhs, rhs, patternOfBool (b1 && b2)]]
      | .apply "or" [], some b1, some b2 => [[op, lhs, rhs, patternOfBool (b1 || b2)]]
      | .apply "xor" [], some b1, some b2 => [[op, lhs, rhs, patternOfBool (b1 != b2)]]
      | .apply "eqBool" [], some b1, some b2 => [[op, lhs, rhs, patternOfBool (b1 == b2)]]
      | _, _, _ => []
  | _ => []

/-- Fallback tuples for grounded-call miss branches. -/
def noGroundedCallTuples : List Pattern → List (List Pattern)
  | [op, arg] =>
      if (groundedCallTuples [op, arg, .fvar "_"]).isEmpty then
        [[op, arg]]
      else
        []
  | [op, lhs, rhs] =>
      if (groundedCallTuples [op, lhs, rhs, .fvar "_"]).isEmpty then
        [[op, lhs, rhs]]
      else
        []
  | _ => []

/-- First full-oriented relation environment:
`eqnLookup`, `typeOf/cast`, grounded calls, and miss-branch companions. -/
def mettaFullRelEnv : RelationEnv where
  tuples := fun rel args =>
    if rel == "eqnLookup" then
      eqnLookupTuples args
    else if rel == "noEqnLookup" then
      noEqnLookupTuples args
    else if rel == "neq" then
      neqTuples args
    else if rel == "typeOf" then
      typeOfTuples args
    else if rel == "notTypeOf" then
      notTypeOfTuples args
    else if rel == "cast" then
      castTuples args
    else if rel == "notCast" then
      notCastTuples args
    else if rel == "groundedCall" then
      groundedCallTuples args
    else if rel == "noGroundedCall" then
      noGroundedCallTuples args
    else
      []

-- Smoke checks.
#eval! do
  let s : Pattern := .apply "Space0" []
  let t : Pattern := .apply "ATrue" []
  let tuples := eqnLookupTuples [s, t, .fvar "dst"]
  IO.println s!"MeTTaCore.Premises eqnLookup tuples: {tuples}"

#eval! do
  let tuples := neqTuples [(.apply "ATrue" [] : Pattern), (.apply "AFalse" [] : Pattern)]
  IO.println s!"MeTTaCore.Premises neq tuples: {tuples}"

#eval! do
  let s : Pattern := .apply "Space" [(.collection .hashBag [(.apply ":" [aTrue, tyBool])] none)]
  let tuples := typeOfTuples [s, aTrue, tyBool]
  IO.println s!"MeTTaCore.Premises typeOf tuples: {tuples}"

#eval! do
  let tuples := groundedCallTuples [(.apply "and" [] : Pattern), aTrue, aFalse, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises groundedCall tuples: {tuples}"

end Mettapedia.OSLF.MeTTaCore.Premises
