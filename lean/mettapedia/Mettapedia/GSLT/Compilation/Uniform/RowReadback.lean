import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep

/-!
# Reading compiled rows at a relation call

The root compiler has an injective row encoding for every pattern, including
a closed value captured by a variable. Built-in relations use the inverse
on the image of this encoding. Reading rejects a malformed tuple.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.RowReadback

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep (Expr)
open RootRewritesOnTheStep (charsCode char_toNat_lt labelCode encode encodeList optionRow namesRow)

def characters (n : ℕ) : List Char :=
  if h : n = 0 then []
  else Char.ofNat (n % 1114113 - 1) :: characters (n / 1114113)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem characters_code (chars : List Char) : characters (charsCode chars) = chars := by
  induction chars with
  | nil => rw [charsCode, characters, dif_pos rfl]
  | cons first rest ih =>
      have low := char_toNat_lt first
      have remainder : (first.toNat + 1 + 1114113 * charsCode rest) % 1114113 = first.toNat + 1 := by
        omega
      have quotient : (first.toNat + 1 + 1114113 * charsCode rest) / 1114113 = charsCode rest := by
        omega
      rw [charsCode, characters, dif_neg (by omega), remainder, quotient, ih]
      simp

def label (n : ℕ) : String := String.ofList (characters n)

@[simp] theorem label_code (name : String) : label (labelCode name) = name := by
  simp [label, labelCode, characters_code]

def optionalName : Expr → Option (Option String)
  | .sym 0 => some none
  | .code (.sym n) => some (some (label n))
  | _ => none

@[simp] theorem optionalName_row (name : Option String) : optionalName (optionRow name) = some name := by
  cases name <;> simp [optionalName, optionRow]

def names : Expr → Option (List String)
  | .sym 0 => some []
  | .app (.sym n) rest => (names rest).map (label n :: ·)
  | _ => none

@[simp] theorem names_row (values : List String) : names (namesRow values) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [names, namesRow, ih]

def collection : ℕ → Option CollType
  | 0 => some .vec
  | 1 => some .hashBag
  | 2 => some .hashSet
  | _ => none

@[simp] theorem collection_code (kind : CollType) : collection (collectionCode kind) = some kind := by
  cases kind <;> rfl

/-- A number read back off its row. -/
def readNumeral : Expr → Option ℕ
  | .sym 0 => some 0
  | .app (.sym 1) rest => (readNumeral rest).map (· + 1)
  | _ => none

@[simp] theorem readNumeral_numeral (n : ℕ) : readNumeral (RootRewritesOnTheStep.numeral n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [readNumeral, RootRewritesOnTheStep.numeral, ih]

mutual

  def readPattern : Expr → Option Pattern
    | .app (.sym 0) index => (readNumeral index).map .bvar
    | .app (.sym 1) (.sym name) => some (.fvar (label name))
    | .app (.sym 2) (.app (.sym name) arguments) =>
        (readList arguments).map (.apply (label name) ·)
    | .app (.sym 3) (.app name body) => do
        return .lambda (← optionalName name) (← readPattern body)
    | .app (.sym 4) (.app arity (.app binders body)) => do
        return .multiLambda (← readNumeral arity) (← names binders) (← readPattern body)
    | .app (.sym 5) (.app body value) => do
        return .subst (← readPattern body) (← readPattern value)
    | .app (.sym 6) (.app (.sym kind) (.app elements rest)) => do
        return .collection (← collection kind) (← readList elements) (← optionalName rest)
    | _ => none

  def readList : Expr → Option (List Pattern)
    | .sym 0 => some []
    | .app first rest => do
        return (← readPattern first) :: (← readList rest)
    | _ => none

end

mutual

  theorem readPattern_encode : ∀ p : Pattern, readPattern (encode p) = some p
    | .bvar _ => by simp [readPattern, encode]
    | .fvar _ => by simp [readPattern, encode]
    | .apply _ arguments => by simp [readPattern, encode, readList_encode arguments]
    | .lambda _ body => by simp [readPattern, encode, readPattern_encode body]
    | .multiLambda _ _ body => by simp [readPattern, encode, readPattern_encode body]
    | .subst body value => by simp [readPattern, encode, readPattern_encode body, readPattern_encode value]
    | .collection _ elements _ => by simp [readPattern, encode, readList_encode elements]

  theorem readList_encode : ∀ ps : List Pattern, readList (encodeList ps) = some ps
    | [] => rfl
    | first :: rest => by simp [readList, encodeList, readPattern_encode first, readList_encode rest]

end

/-- Check the encoded arguments as well as decoding their syntax. This matters
when a built-in relation can be called on rows outside the compiler's image. -/
def readArguments (arguments : List Expr) : Option (List Pattern) := do
  let patterns ← arguments.mapM readPattern
  if patterns.map encode = arguments then some patterns else none

@[simp] theorem readArguments_encode (arguments : List Pattern) :
    readArguments (arguments.map encode) = some arguments := by
  have decoded : (arguments.map encode).mapM readPattern = some arguments := by
    induction arguments with
    | nil => rfl
    | cons first rest ih => simp [List.mapM_cons, readPattern_encode first, ih]
  simp [readArguments, decoded]

theorem encode_readArguments {rows : List Expr} {arguments : List Pattern}
    (decoded : readArguments rows = some arguments) : arguments.map encode = rows := by
  cases matched : rows.mapM readPattern with
  | none => simp [readArguments, matched] at decoded
  | some patterns =>
      by_cases equal : patterns.map encode = rows
      · have same : patterns = arguments := by simpa [readArguments, matched, equal] using decoded
        simpa [← same] using equal
      · simp [readArguments, matched, equal] at decoded

#print axioms readPattern_encode
#print axioms readArguments_encode
#print axioms encode_readArguments

end Mettapedia.GSLT.Compilation.Uniform.RowReadback
