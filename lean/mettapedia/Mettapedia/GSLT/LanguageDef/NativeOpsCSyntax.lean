import Mettapedia.GSLT.LanguageDef.NativeOpsCLex

/-!
# Syntax of the deployed native C fragment

The target retains actual C identifiers, casts, address expressions, field
selectors, explicit array initialization loops, labels and jumps. It is not a
source function table or an executable runtime. Admission and typed lowering
are separate operations on this syntax.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev Name := List Char

structure CType where
  name : Name
  pointers : Nat := 0
  deriving DecidableEq, Repr

inductive UnaryOperator where
  | not | complement | dereference | address | increment
  deriving DecidableEq, Repr

inductive BinaryOperator where
  | add | sub | mul | div | mod | shiftLeft | shiftRight | bitAnd | bitOr | bitXor
  | eq | ne | lt | le | gt | ge | and | or
  deriving DecidableEq, Repr

inductive CExpr where
  | identifier (name : Name)
  | decimal (value : Nat)
  | word (value : BitVec 64)
  | byte (value : BitVec 8)
  | bool (value : Bool)
  | null
  | zero (type : CType)
  | sizeOf (type : CType)
  | call (name : Name) (arguments : List CExpr)
  | unary (operator : UnaryOperator) (operand : CExpr)
  | cast (type : CType) (operand : CExpr)
  | binary (operator : BinaryOperator) (left right : CExpr)
  | conditional (condition whenTrue whenFalse : CExpr)
  | field (record : CExpr) (name : Name) (throughPointer : Bool)
  | index (array index : CExpr)
  deriving Repr

inductive CStatement where
  | empty
  | declare (type : CType) (name : Name) (value : CExpr)
  | assign (location value : CExpr)
  | effect (value : CExpr)
  | branch (condition : CExpr) (whenTrue whenFalse : List CStatement)
  | forLoop (type : CType) (counter : Name) (initial condition increment : CExpr)
      (body : List CStatement)
  | switch (selector : CExpr) (cases : List (CExpr × List CStatement))
      (otherwise : List CStatement)
  | block (body : List CStatement)
  | label (name : Name)
  | jump (name : Name)
  | break
  | return (value : Option CExpr)
  deriving Repr

structure CParameter where
  type : CType
  name : Name
  deriving DecidableEq, Repr

structure CFunction where
  result : CType
  name : Name
  parameters : List CParameter
  body : List CStatement
  deriving Repr

structure CUnit where
  includeHeader : Name
  functions : List CFunction
  deriving Repr

/-- This table is checked against the separately admitted declaration layout. -/
abbrev TypeNames := List Name

def decimalChars? (characters : List Char) : Option Nat :=
  if characters.isEmpty || !characters.all digit then none
  else some (characters.foldl (fun value c => 10 * value + (c.toNat - '0'.toNat)) 0)

def wordChars? (characters : List Char) : Option (BitVec 64) := do
  let value ← decimalChars? characters
  if value < 2 ^ 64 then some (BitVec.ofNat 64 value) else none

def byteChars? (characters : List Char) : Option (BitVec 8) := do
  let value ← decimalChars? characters
  if value < 2 ^ 8 then some (BitVec.ofNat 8 value) else none

def binaryOperator? : Name → Option (BinaryOperator × Nat)
  | ['|', '|'] => some (.or, 1)
  | ['&', '&'] => some (.and, 2)
  | ['|'] => some (.bitOr, 3)
  | ['^'] => some (.bitXor, 4)
  | ['&'] => some (.bitAnd, 5)
  | ['=', '='] => some (.eq, 6)
  | ['!', '='] => some (.ne, 6)
  | ['<'] => some (.lt, 7)
  | ['<', '='] => some (.le, 7)
  | ['>'] => some (.gt, 7)
  | ['>', '='] => some (.ge, 7)
  | ['<', '<'] => some (.shiftLeft, 8)
  | ['>', '>'] => some (.shiftRight, 8)
  | ['+'] => some (.add, 9)
  | ['-'] => some (.sub, 9)
  | ['*'] => some (.mul, 10)
  | ['/'] => some (.div, 10)
  | ['%'] => some (.mod, 10)
  | _ => none

def pointerSuffix : List Token → Nat × List Token
  | .punctuation ['*'] :: rest =>
      let next := pointerSuffix rest
      (next.1 + 1, next.2)
  | tokens => (0, tokens)

def cType? (names : TypeNames) : List Token → Option (CType × List Token)
  | .identifier name :: rest =>
      if names.contains name then
        let suffix := pointerSuffix rest
        some (⟨name, suffix.1⟩, suffix.2)
      else none
  | _ => none

theorem decimal_word_maximum : wordChars? "18446744073709551615".toList =
    some (BitVec.ofNat 64 (2 ^ 64 - 1)) := by decide +kernel

theorem decimal_word_overflow_refused : wordChars? "18446744073709551616".toList = none :=
  by decide +kernel

theorem malformed_decimal_refused : decimalChars? "12_3".toList = none :=
  by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
