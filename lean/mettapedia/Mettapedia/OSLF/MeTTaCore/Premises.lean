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

/-- Read token list from a closed collection payload. -/
private def tokensOfClosedCollection? : Pattern → Option (List String)
  | .collection _ elems none => elems.mapM tokenOfPattern?
  | _ => none

/-- Decode a string from ASCII/Unicode codepoint tokens. -/
private def stringOfCodeTokens? (tokens : List String) : Option String := do
  let chars ← tokens.mapM fun tok => do
    let n ← tok.toInt?
    if n < 0 then
      none
    else
      some (Char.ofNat n.toNat)
  pure (String.ofList chars)

/-- Encode a string as codepoint tokens for robust literal transport. -/
private def codeTokensOfString (s : String) : List Pattern :=
  s.toList.map (fun c => .apply s!"{c.toNat}" [])

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
  | .apply "GStringVec" [chunks] =>
      match tokensOfClosedCollection? chunks with
      | some parts => .grounded (.string (String.intercalate "" parts))
      | none => .expression [.symbol "GStringVec", patternToCoreAtom chunks]
  | .apply "GStringCodes" [codes] =>
      match tokensOfClosedCollection? codes with
      | some toks =>
          match stringOfCodeTokens? toks with
          | some s => .grounded (.string s)
          | none => .expression [.symbol "GStringCodes", patternToCoreAtom codes]
      | none => .expression [.symbol "GStringCodes", patternToCoreAtom codes]
  | .apply "GCustom" [tyTok, dataTok] =>
      match tokenOfPattern? tyTok, tokenOfPattern? dataTok with
      | some ty, some data => .grounded (.custom ty data)
      | _, _ => .expression [.symbol "GCustom", patternToCoreAtom tyTok, patternToCoreAtom dataTok]
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
  | .grounded (.string s) => some (.apply "GStringCodes" [(.collection .vec (codeTokensOfString s) none)])
  | .grounded (.custom ty data) => some (.apply "GCustom" [(.apply ty []), (.apply data [])])
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

/-- Canonical equation entries for `Space0`. -/
def space0EqEntries : List Pattern :=
  [ .apply "=" [aTrue, aFalse]
  , .apply "=" [aFalse, aTrue]
  ]

/-- Canonical type entries for `Space0`. -/
def space0TypeEntries : List Pattern :=
  [ .apply ":" [aTrue, tyBool]
  , .apply ":" [aFalse, tyBool]
  , .apply ":" [aTrue, tyAtom]
  , .apply ":" [aFalse, tyAtom]
  ]

/-- Canonical `Space0` entries in pattern form. -/
def space0Entries : List Pattern := space0EqEntries ++ space0TypeEntries

/-- Canonical space constructor schema: `Space(equations, types)`. -/
def mkCanonicalSpace (eqEntries tyEntries : List Pattern) : Pattern :=
  .apply "Space" [(.collection .hashBag eqEntries none), (.collection .hashBag tyEntries none)]

/-- Canonical `Space0` encoded with the `Space(eqs,tys)` schema. -/
def space0Pattern : Pattern := mkCanonicalSpace space0EqEntries space0TypeEntries

/-- Extract closed collection entries used by canonical space schema. -/
private def entriesOfCollection? : Pattern → Option (List Pattern)
  | .collection _ elems none => some elems
  | _ => none

/-- Decode canonical space schema into `(equation entries, type entries)`. -/
private def decodeCanonicalSpace? : Pattern → Option (List Pattern × List Pattern)
  | .apply "Space0" [] => some (space0EqEntries, space0TypeEntries)
  | .apply "Space" [eqs, tys] =>
      match entriesOfCollection? eqs, entriesOfCollection? tys with
      | some eqEntries, some tyEntries => some (eqEntries, tyEntries)
      | _, _ => none
  | _ => none

/-- Decode a space term into explicit equation/type entries. -/
def spaceEntriesOfPattern? : Pattern → Option (List Pattern)
  | space =>
      match decodeCanonicalSpace? space with
      | some (eqEntries, tyEntries) => some (eqEntries ++ tyEntries)
      | none => none

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

/-- Parse boolean payload from symbolic or grounded boolean atoms. -/
private def boolOfPattern? : Pattern → Option Bool
  | .apply "ATrue" [] => some true
  | .apply "AFalse" [] => some false
  | .apply "GBoolTrue" [] => some true
  | .apply "GBoolFalse" [] => some false
  | _ => none

/-- Parse integer payload from `GInt(token)`. -/
private def intOfPattern? : Pattern → Option Int
  | .apply "GInt" [tok] =>
      match tokenOfPattern? tok with
      | some s => s.toInt?
      | none => none
  | _ => none

/-- Parse string payload from `GString(token)`. -/
private def stringOfPattern? : Pattern → Option String
  | .apply "GString" [tok] => tokenOfPattern? tok
  | .apply "GStringVec" [chunks] =>
      match tokensOfClosedCollection? chunks with
      | some parts => some (String.intercalate "" parts)
      | none => none
  | .apply "GStringCodes" [codes] =>
      match tokensOfClosedCollection? codes with
      | some toks => stringOfCodeTokens? toks
      | none => none
  | _ => none

/-- Canonical symbolic bool output for relation tuples. -/
private def patternOfBoolSym (b : Bool) : Pattern :=
  if b then aTrue else aFalse

/-- Canonical grounded bool output for conversion/grounded-call tuples. -/
private def patternOfBoolGrounded (b : Bool) : Pattern :=
  if b then .apply "GBoolTrue" [] else .apply "GBoolFalse" []

/-- Canonical grounded int output for conversion/grounded-call tuples. -/
private def patternOfIntGrounded (n : Int) : Pattern :=
  .apply "GInt" [(.apply s!"{n}" [])]

/-- Canonical grounded string output for conversion/grounded-call tuples. -/
private def patternOfStringGrounded (s : String) : Pattern :=
  .apply "GStringCodes" [(.collection .vec (codeTokensOfString s) none)]

/-- Conversion branch for cast semantics beyond typable identity. -/
private def castConversion? (atom ty : Pattern) : Option Pattern :=
  match ty with
  | .apply "Bool" [] =>
      match boolOfPattern? atom, intOfPattern? atom, stringOfPattern? atom with
      | some b, _, _ => some (patternOfBoolGrounded b)
      | none, some n, _ => some (patternOfBoolGrounded (n != 0))
      | none, none, some s =>
          if s == "true" || s == "True" || s == "1" then
            some (patternOfBoolGrounded true)
          else if s == "false" || s == "False" || s == "0" then
            some (patternOfBoolGrounded false)
          else
            none
      | none, none, none => none
  | .apply "Int" [] =>
      match intOfPattern? atom, boolOfPattern? atom, stringOfPattern? atom with
      | some n, _, _ => some (patternOfIntGrounded n)
      | none, some b, _ => some (patternOfIntGrounded (if b then 1 else 0))
      | none, none, some s =>
          match s.toInt? with
          | some n => some (patternOfIntGrounded n)
          | none => none
      | none, none, none => none
  | .apply "String" [] =>
      match stringOfPattern? atom, intOfPattern? atom, boolOfPattern? atom with
      | some s, _, _ => some (patternOfStringGrounded s)
      | none, some n, _ => some (patternOfStringGrounded s!"{n}")
      | none, none, some b =>
          some (patternOfStringGrounded (if b then "true" else "false"))
      | none, none, none => none
  | _ => none

/-- Tuples for `cast(space, atom, ty, out)` with conversion + typable identity. -/
def castTuples : List Pattern → List (List Pattern)
  | [space, atom, ty, _out] =>
      match atomspaceOfPattern? space with
      | none => []
      | some asp =>
          match castConversion? atom ty with
          | some casted => [[space, atom, ty, casted]]
          | none =>
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

/-- Generic grounded-call interpreter by reusing `executeGroundedOp`. -/
private def groundedCallViaCore : List Pattern → List (List Pattern)
  | [op, arg, _out] =>
      match executeGroundedOp (patternToCoreAtom op) [patternToCoreAtom arg] with
      | some outCore =>
          match coreAtomToPattern? outCore with
          | some outPat => [[op, arg, outPat]]
          | none => []
      | none => []
  | [op, lhs, rhs, _out] =>
      match executeGroundedOp (patternToCoreAtom op) [patternToCoreAtom lhs, patternToCoreAtom rhs] with
      | some outCore =>
          match coreAtomToPattern? outCore with
          | some outPat => [[op, lhs, rhs, outPat]]
          | none => []
      | none => []
  | _ => []

/-- Single-step grounded call relation for boolean core ops. -/
def groundedCallTuples : List Pattern → List (List Pattern)
  | [op, arg, _out] =>
      match op, boolOfPattern? arg with
      | .apply "not" [], some b => [[op, arg, patternOfBoolSym (!b)]]
      | _, _ => groundedCallViaCore [op, arg, .fvar "_"]
  | [op, lhs, rhs, _out] =>
      match op, boolOfPattern? lhs, boolOfPattern? rhs with
      | .apply "and" [], some b1, some b2 => [[op, lhs, rhs, patternOfBoolSym (b1 && b2)]]
      | .apply "or" [], some b1, some b2 => [[op, lhs, rhs, patternOfBoolSym (b1 || b2)]]
      | .apply "xor" [], some b1, some b2 => [[op, lhs, rhs, patternOfBoolSym (b1 != b2)]]
      | .apply "eqBool" [], some b1, some b2 => [[op, lhs, rhs, patternOfBoolSym (b1 == b2)]]
      | _, _, _ => groundedCallViaCore [op, lhs, rhs, .fvar "_"]
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
  let s : Pattern := space0Pattern
  let t : Pattern := .apply "ATrue" []
  let tuples := eqnLookupTuples [s, t, .fvar "dst"]
  IO.println s!"MeTTaCore.Premises eqnLookup tuples: {tuples}"

#eval! do
  let tuples := neqTuples [(.apply "ATrue" [] : Pattern), (.apply "AFalse" [] : Pattern)]
  IO.println s!"MeTTaCore.Premises neq tuples: {tuples}"

#eval! do
  let s : Pattern := mkCanonicalSpace [] [(.apply ":" [aTrue, tyBool])]
  let tuples := typeOfTuples [s, aTrue, tyBool]
  IO.println s!"MeTTaCore.Premises typeOf tuples: {tuples}"

#eval! do
  let tuples := groundedCallTuples [(.apply "and" [] : Pattern), aTrue, aFalse, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises groundedCall tuples: {tuples}"

#eval! do
  let tuples := groundedCallTuples
    [(.apply "+" [] : Pattern), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.fvar "out")]
  IO.println s!"MeTTaCore.Premises groundedCall int tuples: {tuples}"

#eval! do
  let tuples := groundedCallTuples
    [(.apply "concat" [] : Pattern),
      (.apply "GString" [(.apply "hello" [])]),
      (.apply "GString" [(.apply "world" [])]),
      (.fvar "out")]
  IO.println s!"MeTTaCore.Premises groundedCall string tuples: {tuples}"

#eval! do
  let tuples := castTuples [space0Pattern, (.apply "GString" [(.apply "42" [])]), tyInt, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast string->int tuples: {tuples}"

#eval! do
  let tuples := castTuples [space0Pattern, (.apply "ATrue" []), tyString, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast bool-symbol->string tuples: {tuples}"

#eval! do
  let tuples := castTuples [space0Pattern, (.apply "GString" [(.apply "abc" [])]), tyInt, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast invalid string->int tuples: {tuples}"

#eval! do
  let tuples := castTuples [space0Pattern, (.apply "GString" [(.apply "maybe" [])]), tyBool, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast invalid string->bool tuples: {tuples}"

#eval! do
  let spaced : Pattern := .apply "GStringCodes"
    [(.collection .vec [(.apply "104" []), (.apply "105" []), (.apply "32" []), (.apply "116" []), (.apply "104" []), (.apply "101" []), (.apply "114" []), (.apply "101" [])] none)]
  let tuples := castTuples [space0Pattern, spaced, tyInt, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast spaced-string->int tuples: {tuples}"

/-- Canonical-space helper roundtrip. -/
theorem space0Pattern_decode_roundtrip :
    spaceEntriesOfPattern? space0Pattern = some space0Entries := rfl

/-- Grounded Int call hit. -/
theorem groundedCallTuples_int_add_hit :
    groundedCallTuples
      [(.apply "+" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.fvar "out")]
      = [[(.apply "+" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.apply "GInt" [(.apply "5" [])])]] := by
  native_decide

/-- Grounded String call hit (robust encoded output). -/
theorem groundedCallTuples_string_concat_hit :
    groundedCallTuples
      [(.apply "concat" []), (.apply "GString" [(.apply "hello" [])]), (.apply "GString" [(.apply "world" [])]), (.fvar "out")]
      = [[(.apply "concat" []), (.apply "GString" [(.apply "hello" [])]), (.apply "GString" [(.apply "world" [])]), patternOfStringGrounded "helloworld"]] := by
  native_decide

/-- Grounded call miss stays empty. -/
theorem groundedCallTuples_unknown_miss :
    groundedCallTuples
      [(.apply "unknownOp" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.fvar "out")]
      = [] := by
  native_decide

/-- Coded string decoding roundtrip through `patternToCoreAtom`. -/
theorem patternToCoreAtom_string_codes_hi_there :
    patternToCoreAtom (patternOfStringGrounded "hi there") = .grounded (.string "hi there") := by
  native_decide

/-- Coded string encoding roundtrip through `coreAtomToPattern?`. -/
theorem coreAtomToPattern_string_codes_hi_there :
    coreAtomToPattern? (.grounded (.string "hi there")) = some (patternOfStringGrounded "hi there") := by
  native_decide

/-- Concrete decoded payload from `GStringCodes` with a space. -/
theorem stringOfPattern_string_codes_hi_there :
    stringOfPattern? (patternOfStringGrounded "hi there") = some "hi there" := by
  native_decide

/-- Grounded coded-string concat preserves spaces through relation tuples. -/
theorem groundedCallTuples_coded_concat_space_hit :
    groundedCallTuples
      [(.apply "concat" []), patternOfStringGrounded "hi ", patternOfStringGrounded "there", (.fvar "out")]
      = [[(.apply "concat" []), patternOfStringGrounded "hi ", patternOfStringGrounded "there", patternOfStringGrounded "hi there"]] := by
  native_decide

/-- Cast conversion hit: String -> Int. -/
theorem castTuples_string_to_int_hit :
    castTuples [space0Pattern, (.apply "GString" [(.apply "42" [])]), tyInt, (.fvar "out")]
      = [[space0Pattern, (.apply "GString" [(.apply "42" [])]), tyInt, (.apply "GInt" [(.apply "42" [])])]] := by
  have hInt : ("42".toInt?) = some 42 := by
    native_decide
  have hToString : toString (42 : Int) = "42" := by
    native_decide
  simp [castTuples, atomspaceOfPattern?, spaceEntriesOfPattern?, decodeCanonicalSpace?,
    entriesOfCollection?, castConversion?, intOfPattern?, boolOfPattern?, stringOfPattern?,
    tokenOfPattern?, tyInt, patternOfIntGrounded, space0Pattern, mkCanonicalSpace,
    space0EqEntries, space0TypeEntries, hInt, hToString]

/-- Cast conversion hit: Bool-symbol -> String (robust encoded output). -/
theorem castTuples_bool_to_string_hit :
    castTuples [space0Pattern, (.apply "ATrue" []), tyString, (.fvar "out")]
      = [[space0Pattern, (.apply "ATrue" []), tyString, patternOfStringGrounded "true"]] := by
  simp [castTuples, atomspaceOfPattern?, spaceEntriesOfPattern?, decodeCanonicalSpace?,
    entriesOfCollection?, castConversion?, intOfPattern?, boolOfPattern?, stringOfPattern?,
    tyString, patternOfStringGrounded, codeTokensOfString, space0Pattern,
    mkCanonicalSpace, space0EqEntries, space0TypeEntries]

/-- Cast conversion miss: non-parseable String -> Int. -/
theorem castTuples_string_to_int_miss :
    castTuples [space0Pattern, (.apply "GString" [(.apply "abc" [])]), tyInt, (.fvar "out")] = [] := by
  native_decide

/-- Cast conversion miss: invalid String -> Bool token. -/
theorem castTuples_string_to_bool_miss :
    castTuples [space0Pattern, (.apply "GString" [(.apply "maybe" [])]), tyBool, (.fvar "out")] = [] := by
  native_decide

end Mettapedia.OSLF.MeTTaCore.Premises
