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

@[simp] lemma tokenOfPattern?_apply (s : String) :
    tokenOfPattern? (.apply s []) = some s := by
  rfl

/-- True if a string has no whitespace (safe for direct token use). -/
private def isSafeToken (s : String) : Bool :=
  !(s.toList.any Char.isWhitespace)

/-- Parse a single decimal digit. -/
private def digitOfChar? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

/-- Parse a nonempty list of decimal digits into a Nat. -/
private def natOfCharList? : List Char → Option Nat
  | [] => none
  | cs => do
      let digits ← cs.mapM digitOfChar?
      pure (digits.foldl (fun n d => n * 10 + d) 0)

/-- Parse an integer token string (optional leading '-'). -/
private def intOfToken? (tok : String) : Option Int :=
  match tok.toList with
  | '-' :: rest =>
      match natOfCharList? rest with
      | some n => some (Int.negOfNat n)
      | none => none
  | cs =>
      match natOfCharList? cs with
      | some n => some (Int.ofNat n)
      | none => none

@[simp] lemma intOfToken?_2 : intOfToken? "2" = some 2 := by
  decide

@[simp] lemma intOfToken?_3 : intOfToken? "3" = some 3 := by
  decide

@[simp] lemma intOfToken?_42 : intOfToken? "42" = some 42 := by
  decide

@[simp] lemma intOfToken?_abc : intOfToken? "abc" = none := by
  decide

@[simp] lemma intOfToken?_maybe : intOfToken? "maybe" = none := by
  decide

/-- Decode a string from ASCII/Unicode codepoint tokens. -/
private def stringOfCodeTokens? (tokens : List String) : Option String := do
  let chars ← tokens.mapM fun tok => do
    let n ← intOfToken? tok
    if n < 0 then
      none
    else
      some (Char.ofNat n.toNat)
  pure (String.ofList chars)

/-- Encode a string as codepoint tokens for robust literal transport. -/
private def codeTokensOfString (s : String) : List Pattern :=
  s.toList.map (fun c => .apply s!"{c.toNat}" [])

/-- Encode a list of patterns as a cons-list (ACons/ANil). -/
def mkConsList (entries : List Pattern) : Pattern :=
  entries.foldr (fun entry acc => .apply "ACons" [entry, acc]) (.apply "ANil" [])

@[simp] lemma mkConsList_nil : mkConsList [] = .apply "ANil" [] := by
  rfl

@[simp] lemma mkConsList_cons (head : Pattern) (tail : List Pattern) :
    mkConsList (head :: tail) = .apply "ACons" [head, mkConsList tail] := by
  simp [mkConsList]

/-- Decode a cons-list (ACons/ANil) into a list of patterns. -/
def decodeConsList : Pattern → Option (List Pattern)
  | .apply "ANil" [] => some []
  | .apply "ACons" [head, tail] => do
      let rest ← decodeConsList tail
      some (head :: rest)
  | _ => none

@[simp] theorem decodeConsList_mkConsList (entries : List Pattern) :
    decodeConsList (mkConsList entries) = some entries := by
  induction entries with
  | nil => simp [decodeConsList]
  | cons head tail ih =>
      simp [decodeConsList, ih]

/-- Extract token strings from a cons-list. -/
def tokensOfConsList : Pattern → Option (List String)
  | .apply "ANil" [] => some []
  | .apply "ACons" [head, tail] => do
      let tok ← tokenOfPattern? head
      let rest ← tokensOfConsList tail
      some (tok :: rest)
  | _ => none

@[simp] theorem tokensOfConsList_mkConsList_tokens (tokens : List String) :
    tokensOfConsList (mkConsList (tokens.map (fun s => .apply s []))) = some tokens := by
  induction tokens with
  | nil => simp [tokensOfConsList]
  | cons tok tail ih =>
      simp [tokensOfConsList, tokenOfPattern?_apply, ih]

mutual
  /-- Bridge from MeTTaIL patterns to MeTTaCore atoms. -/
  def patternToCoreAtom : Pattern → Atom
    | .apply "GBoolTrue" [] => .grounded (.bool true)
    | .apply "GBoolFalse" [] => .grounded (.bool false)
    | .apply "GInt" [tok] =>
        match tokenOfPattern? tok with
        | some s =>
            match intOfToken? s with
            | some n => .grounded (.int n)
            | none => .expression [.symbol "GInt", patternToCoreAtom tok]
        | none => .expression [.symbol "GInt", patternToCoreAtom tok]
    | .apply "GString" [tok] =>
        match tokenOfPattern? tok with
        | some s => .grounded (.string s)
        | none => .expression [.symbol "GString", patternToCoreAtom tok]
    | .apply "GStringVec" [chunks] =>
        match tokensOfConsList chunks with
        | some parts => .grounded (.string (String.intercalate "" parts))
        | none => .expression [.symbol "GStringVec", patternToCoreAtom chunks]
    | .apply "GStringCodes" [codes] =>
        match tokensOfConsList codes with
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
          .expression (.symbol ctor :: patternToCoreAtomList args)
    | .lambda body =>
        .expression [.symbol "λ", patternToCoreAtom body]
    | .multiLambda n body =>
        .expression [.symbol "λ*", .grounded (.int n), patternToCoreAtom body]
    | .subst body repl =>
        .expression [.symbol "subst", patternToCoreAtom body, patternToCoreAtom repl]
    | .collection ct elems rest =>
        let elemsA := patternToCoreAtomList elems
        let restA := rest.map (fun r => [.var r]) |>.getD []
        .expression (.symbol (collTag ct) :: elemsA ++ restA)

  def patternToCoreAtomList : List Pattern → List Atom
    | [] => []
    | p :: ps => patternToCoreAtom p :: patternToCoreAtomList ps
end

@[simp] theorem patternToCoreAtom_GInt_token (s : String) :
    patternToCoreAtom (.apply "GInt" [(.apply s [])]) =
      match intOfToken? s with
      | some n => .grounded (.int n)
      | none => .expression [.symbol "GInt", patternToCoreAtom (.apply s [])] := by
  simp [patternToCoreAtom, tokenOfPattern?_apply]

@[simp] theorem patternToCoreAtom_GString_token (s : String) :
    patternToCoreAtom (.apply "GString" [(.apply s [])]) = .grounded (.string s) := by
  simp [patternToCoreAtom, tokenOfPattern?_apply]

@[simp] lemma patternToCoreAtom_plus :
    patternToCoreAtom (.apply "+" []) = .symbol "+" := by
  simp [patternToCoreAtom]

@[simp] lemma patternToCoreAtom_concat :
    patternToCoreAtom (.apply "concat" []) = .symbol "concat" := by
  simp [patternToCoreAtom]

@[simp] lemma patternToCoreAtom_unknownOp :
    patternToCoreAtom (.apply "unknownOp" []) = .symbol "unknownOp" := by
  simp [patternToCoreAtom]

mutual
  /-- Partial bridge from MeTTaCore atoms to MeTTaIL patterns. -/
  def coreAtomToPattern? : Atom → Option Pattern
    | .var x => some (.fvar x)
    | .symbol s => some (.apply s [])
    | .grounded (.bool true) => some (.apply "GBoolTrue" [])
    | .grounded (.bool false) => some (.apply "GBoolFalse" [])
    | .grounded (.int n) => some (.apply "GInt" [(.apply s!"{n}" [])])
    | .grounded (.string s) =>
        if isSafeToken s then
          some (.apply "GString" [(.apply s [])])
        else
          some (.apply "GStringCodes" [mkConsList (codeTokensOfString s)])
    | .grounded (.custom ty data) => some (.apply "GCustom" [(.apply ty []), (.apply data [])])
    | .expression [] => none
    | .expression (.symbol ctor :: args) => do
        let ps ← coreAtomToPatternList? args
        pure (.apply ctor ps)
    | .expression _ => none

  def coreAtomToPatternList? : List Atom → Option (List Pattern)
    | [] => some []
    | a :: as => do
        let p ← coreAtomToPattern? a
        let ps ← coreAtomToPatternList? as
        pure (p :: ps)
end


/-- Canonical `Space0` atomspace used by the first full MeTTa slice. -/
def space0Atomspace : Atomspace :=
  (Atomspace.empty
    |>.addEquation (.symbol "ATrue") (.symbol "AFalse")
    |>.addEquation (.symbol "AFalse") (.symbol "ATrue")
    |>.addType (.symbol "ATrue") (.symbol "Bool")
    |>.addType (.symbol "AFalse") (.symbol "Bool")
    |>.addType (.symbol "ATrue") (.symbol "Atom")
    |>.addType (.symbol "AFalse") (.symbol "Atom"))

/-- Canonical equation entries for `Space0` (as AEqEntry constructors). -/
def space0EqEntries : List Pattern :=
  [ .apply "AEqEntry" [aTrue, aFalse]
  , .apply "AEqEntry" [aFalse, aTrue]
  ]

/-- Canonical type entries for `Space0` (as ATypeEntry constructors). -/
def space0TypeEntries : List Pattern :=
  [ .apply "ATypeEntry" [aTrue, tyBool]
  , .apply "ATypeEntry" [aFalse, tyBool]
  , .apply "ATypeEntry" [aTrue, tyAtom]
  , .apply "ATypeEntry" [aFalse, tyAtom]
  ]

/-- Canonical `Space0` entries in pattern form. -/
def space0Entries : List Pattern := space0EqEntries ++ space0TypeEntries

/-- Canonical space constructor schema: `Space(eqs-cons-list, tys-cons-list)`. -/
def mkCanonicalSpace (eqEntries tyEntries : List Pattern) : Pattern :=
  .apply "Space" [mkConsList eqEntries, mkConsList tyEntries]

/-- Canonical `Space0` encoded with the `Space(eqs,tys)` schema. -/
def space0Pattern : Pattern := mkCanonicalSpace space0EqEntries space0TypeEntries

/-- Decode canonical space schema into `(equation entries, type entries)`. -/
private def decodeCanonicalSpace? : Pattern → Option (List Pattern × List Pattern)
  | .apply "Space0" [] => some (space0EqEntries, space0TypeEntries)
  | .apply "Space" [eqs, tys] =>
      match decodeConsList eqs, decodeConsList tys with
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
  | .apply "AEqEntry" [lhs, rhs] =>
      if lhs == src then some rhs else none
  | _ => none

/-- Traverse a cons-list of AEqEntry patterns, collecting matches for src. -/
private partial def eqnLookupInConsList (src : Pattern) : Pattern → List Pattern
  | .apply "ACons" [entry, tail] =>
      match eqnRhsForSrc? src entry with
      | some dst => dst :: eqnLookupInConsList src tail
      | none => eqnLookupInConsList src tail
  | .apply "ANil" [] => []
  | _ => []

/-- Extract the eqs cons-list from a Space pattern. -/
private def spaceEqsList? : Pattern → Option Pattern
  | .apply "Space" [eqs, _tys] => some eqs
  | _ => none

/-- Extract the tys cons-list from a Space pattern. -/
private def spaceTysList? : Pattern → Option Pattern
  | .apply "Space" [_eqs, tys] => some tys
  | _ => none

/-- Cons-list-backed tuples for `eqnLookup(space, src, dst)`. -/
def eqnLookupTuples : List Pattern → List (List Pattern)
  | [space, src, _dst] =>
      match spaceEqsList? space with
      | none => []
      | some eqs =>
          (eqnLookupInConsList src eqs).map fun dst =>
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

/-- Check if a cons-list of ATypeEntry contains a matching (atom, ty) pair. -/
def typeListContains (atom ty : Pattern) : Pattern → Bool
  | .apply "ACons" [.apply "ATypeEntry" [a, t], tail] =>
      (a == atom && t == ty) || typeListContains atom ty tail
  | .apply "ACons" [_, tail] => typeListContains atom ty tail
  | .apply "ANil" [] => false
  | _ => false

@[simp] lemma typeListContains_nil (atom ty : Pattern) :
    typeListContains atom ty (.apply "ANil" []) = false := by
  simp [typeListContains]

@[simp] lemma typeListContains_cons_entry (atom ty a t tail : Pattern) :
    typeListContains atom ty (.apply "ACons" [.apply "ATypeEntry" [a, t], tail]) =
      ((a == atom && t == ty) || typeListContains atom ty tail) := by
  rfl

/-- Tuples for `typeOf(space, atom, ty)`. -/
def typeOfTuples : List Pattern → List (List Pattern)
  | [space, atom, ty] =>
      match spaceTysList? space with
      | none => []
      | some tys =>
          if typeListContains atom ty tys then
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
      | some s => intOfToken? s
      | none => none
  | _ => none

/-- Parse string payload from `GString(token)`. -/
private def stringOfPattern? : Pattern → Option String
  | .apply "GString" [tok] => tokenOfPattern? tok
  | .apply "GStringVec" [chunks] =>
      match tokensOfConsList chunks with
      | some parts => some (String.intercalate "" parts)
      | none => none
  | .apply "GStringCodes" [codes] =>
      match tokensOfConsList codes with
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
  if isSafeToken s then
    .apply "GString" [(.apply s [])]
  else
    .apply "GStringCodes" [mkConsList (codeTokensOfString s)]

@[simp] lemma maybe_not_true_true_one :
    (("maybe" == "true") || ("maybe" == "True") || ("maybe" == "1")) = false := by
  decide

@[simp] lemma maybe_not_false_false_zero :
    (("maybe" == "false") || ("maybe" == "False") || ("maybe" == "0")) = false := by
  decide

@[simp] lemma maybe_not_true_true_one_prop :
    ((("maybe" = "true") ∨ ("maybe" = "True")) ∨ ("maybe" = "1")) = False := by
  decide

@[simp] lemma maybe_not_false_false_zero_prop :
    ((("maybe" = "false") ∨ ("maybe" = "False")) ∨ ("maybe" = "0")) = False := by
  decide

@[simp] lemma toString_42 : (toString (42 : Int)) = "42" := by
  decide

@[simp] lemma toString_5 : (toString (5 : Int)) = "5" := by
  decide

@[simp] lemma isSafeToken_hi_there : isSafeToken "hi_there" = true := by
  decide

@[simp] lemma isSafeToken_hi_ : isSafeToken "hi_" = true := by
  decide

@[simp] lemma isSafeToken_there : isSafeToken "there" = true := by
  decide

@[simp] lemma isSafeToken_hello : isSafeToken "hello" = true := by
  decide

@[simp] lemma isSafeToken_world : isSafeToken "world" = true := by
  decide

@[simp] lemma isSafeToken_helloworld : isSafeToken "helloworld" = true := by
  decide

@[simp] lemma isSafeToken_true : isSafeToken "true" = true := by
  decide

@[simp] lemma patternOfStringGrounded_hi_there :
    patternOfStringGrounded "hi_there" = .apply "GString" [(.apply "hi_there" [])] := by
  simp [patternOfStringGrounded, isSafeToken_hi_there]

@[simp] lemma patternOfStringGrounded_hi_ :
    patternOfStringGrounded "hi_" = .apply "GString" [(.apply "hi_" [])] := by
  simp [patternOfStringGrounded, isSafeToken_hi_]

@[simp] lemma patternOfStringGrounded_there :
    patternOfStringGrounded "there" = .apply "GString" [(.apply "there" [])] := by
  simp [patternOfStringGrounded, isSafeToken_there]

@[simp] lemma patternOfStringGrounded_hello :
    patternOfStringGrounded "hello" = .apply "GString" [(.apply "hello" [])] := by
  simp [patternOfStringGrounded, isSafeToken_hello]

@[simp] lemma patternOfStringGrounded_world :
    patternOfStringGrounded "world" = .apply "GString" [(.apply "world" [])] := by
  simp [patternOfStringGrounded, isSafeToken_world]

@[simp] lemma patternOfStringGrounded_helloworld :
    patternOfStringGrounded "helloworld" = .apply "GString" [(.apply "helloworld" [])] := by
  simp [patternOfStringGrounded, isSafeToken_helloworld]

@[simp] lemma patternOfStringGrounded_true :
    patternOfStringGrounded "true" = .apply "GString" [(.apply "true" [])] := by
  simp [patternOfStringGrounded, isSafeToken_true]

@[simp] lemma beq_aTrue_gstring_abc :
    (aTrue == .apply "GString" [(.apply "abc" [])]) = false := by
  decide

@[simp] lemma beq_aFalse_gstring_abc :
    (aFalse == .apply "GString" [(.apply "abc" [])]) = false := by
  decide

@[simp] lemma beq_aTrue_gstring_maybe :
    (aTrue == .apply "GString" [(.apply "maybe" [])]) = false := by
  decide

@[simp] lemma beq_aFalse_gstring_maybe :
    (aFalse == .apply "GString" [(.apply "maybe" [])]) = false := by
  decide

@[simp] lemma coreAtomToPattern_int (n : Int) :
    coreAtomToPattern? (.grounded (.int n)) = some (.apply "GInt" [(.apply s!"{n}" [])]) := by
  simp [coreAtomToPattern?]

@[simp] lemma coreAtomToPattern_string_helloworld :
    coreAtomToPattern? (.grounded (.string "helloworld")) =
      some (.apply "GString" [(.apply "helloworld" [])]) := by
  simp [coreAtomToPattern?, isSafeToken_helloworld]

@[simp] lemma coreAtomToPattern_string_hi_there :
    coreAtomToPattern? (.grounded (.string "hi_there")) =
      some (.apply "GString" [(.apply "hi_there" [])]) := by
  simp [coreAtomToPattern?, isSafeToken_hi_there]

@[simp] lemma typeListContains_space0_abc_int :
    typeListContains (.apply "GString" [(.apply "abc" [])]) (.apply "Int" [])
        (mkConsList space0TypeEntries) = false := by
  decide

@[simp] lemma typeListContains_space0_maybe_bool :
    typeListContains (.apply "GString" [(.apply "maybe" [])]) (.apply "Bool" [])
        (mkConsList space0TypeEntries) = false := by
  decide

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
          match intOfToken? s with
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
      match castConversion? atom ty with
      | some casted => [[space, atom, ty, casted]]
      | none =>
          match spaceTysList? space with
          | none => []
          | some tys =>
              if typeListContains atom ty tys then
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

/-- Tuples for `nonBoolAtom(cond)` — succeeds iff cond is not GBoolTrue/GBoolFalse. -/
def nonBoolAtomTuples : List Pattern → List (List Pattern)
  | [cond] =>
      match cond with
      | .apply "GBoolTrue" [] => []
      | .apply "GBoolFalse" [] => []
      | _ => [[cond]]
  | _ => []

/-- First full-oriented relation environment:
`eqnLookup`, `typeOf/cast`, grounded calls, `nonBoolAtom`, and miss-branch companions. -/
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
    else if rel == "nonBoolAtom" then
      nonBoolAtomTuples args
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
  let s : Pattern := mkCanonicalSpace [] [(.apply "ATypeEntry" [aTrue, tyBool])]
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
    [mkConsList [(.apply "104" []), (.apply "105" []), (.apply "32" []), (.apply "116" []), (.apply "104" []), (.apply "101" []), (.apply "114" []), (.apply "101" [])]]
  let tuples := castTuples [space0Pattern, spaced, tyInt, (.fvar "out")]
  IO.println s!"MeTTaCore.Premises cast spaced-string->int tuples: {tuples}"

/-- Canonical-space helper roundtrip. -/
theorem space0Pattern_decode_roundtrip :
    spaceEntriesOfPattern? space0Pattern = some space0Entries := by
  simp [spaceEntriesOfPattern?, space0Pattern, mkCanonicalSpace, decodeCanonicalSpace?,
    decodeConsList, space0Entries, space0EqEntries, space0TypeEntries]

/-- Grounded Int call hit. -/
theorem groundedCallTuples_int_add_hit :
    groundedCallTuples
      [(.apply "+" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.fvar "out")]
      = [[(.apply "+" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.apply "GInt" [(.apply "5" [])])]] := by
  simp [groundedCallTuples, groundedCallViaCore, executeGroundedOp, GroundedType.execute]

/-- Grounded String call hit (robust encoded output). -/
theorem groundedCallTuples_string_concat_hit :
    groundedCallTuples
      [(.apply "concat" []), (.apply "GString" [(.apply "hello" [])]), (.apply "GString" [(.apply "world" [])]), (.fvar "out")]
      = [[(.apply "concat" []), (.apply "GString" [(.apply "hello" [])]), (.apply "GString" [(.apply "world" [])]), patternOfStringGrounded "helloworld"]] := by
  simp [groundedCallTuples, groundedCallViaCore, executeGroundedOp, GroundedType.execute]

/-- Grounded call miss stays empty. -/
theorem groundedCallTuples_unknown_miss :
    groundedCallTuples
      [(.apply "unknownOp" []), (.apply "GInt" [(.apply "2" [])]), (.apply "GInt" [(.apply "3" [])]), (.fvar "out")]
      = [] := by
  simp [groundedCallTuples, groundedCallViaCore, executeGroundedOp]

/-- String decoding roundtrip through `patternToCoreAtom`. -/
theorem patternToCoreAtom_string_token_hi_there :
    patternToCoreAtom (patternOfStringGrounded "hi_there") = .grounded (.string "hi_there") := by
  simp

/-- String encoding roundtrip through `coreAtomToPattern?`. -/
theorem coreAtomToPattern_string_token_hi_there :
    coreAtomToPattern? (.grounded (.string "hi_there")) = some (patternOfStringGrounded "hi_there") := by
  simp

/-- Concrete decoded payload from a token-grounded string. -/
theorem stringOfPattern_string_token_hi_there :
    stringOfPattern? (patternOfStringGrounded "hi_there") = some "hi_there" := by
  simp [stringOfPattern?]

/-- Grounded string concat preserves tokens through relation tuples. -/
theorem groundedCallTuples_concat_safe_hit :
    groundedCallTuples
      [(.apply "concat" []), patternOfStringGrounded "hi_", patternOfStringGrounded "there", (.fvar "out")]
      = [[(.apply "concat" []), patternOfStringGrounded "hi_", patternOfStringGrounded "there", patternOfStringGrounded "hi_there"]] := by
  simp [groundedCallTuples, groundedCallViaCore, executeGroundedOp, GroundedType.execute]

/-- Cast conversion hit: String -> Int. -/
theorem castTuples_string_to_int_hit :
    castTuples [space0Pattern, (.apply "GString" [(.apply "42" [])]), tyInt, (.fvar "out")]
      = [[space0Pattern, (.apply "GString" [(.apply "42" [])]), tyInt, (.apply "GInt" [(.apply "42" [])])]] := by
  simp [castTuples, castConversion?, intOfPattern?, boolOfPattern?, stringOfPattern?, tokenOfPattern?,
    patternOfIntGrounded, tyInt]

/-- Cast conversion hit: Bool-symbol -> String (robust encoded output). -/
theorem castTuples_bool_to_string_hit :
    castTuples [space0Pattern, (.apply "ATrue" []), tyString, (.fvar "out")]
      = [[space0Pattern, (.apply "ATrue" []), tyString, patternOfStringGrounded "true"]] := by
  simp [castTuples, castConversion?, boolOfPattern?, intOfPattern?, stringOfPattern?,
    tyString]

/-- Cast conversion miss: non-parseable String -> Int. -/
theorem castTuples_string_to_int_miss :
    castTuples [space0Pattern, (.apply "GString" [(.apply "abc" [])]), tyInt, (.fvar "out")] = [] := by
  simp [castTuples, castConversion?, intOfPattern?, boolOfPattern?, stringOfPattern?, tokenOfPattern?,
    tyInt, space0Pattern, mkCanonicalSpace, spaceTysList?]

/-- Cast conversion miss: invalid String -> Bool token. -/
theorem castTuples_string_to_bool_miss :
    castTuples [space0Pattern, (.apply "GString" [(.apply "maybe" [])]), tyBool, (.fvar "out")] = [] := by
  simp [castTuples, castConversion?, boolOfPattern?, intOfPattern?, stringOfPattern?, tokenOfPattern?,
    tyBool, space0Pattern, mkCanonicalSpace, spaceTysList?]

end Mettapedia.OSLF.MeTTaCore.Premises
