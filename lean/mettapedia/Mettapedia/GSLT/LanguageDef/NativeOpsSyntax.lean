import Mettapedia.GSLT.LanguageDef.NativeWord64

/-!
# Syntax and expression typing of authored native operations

This is the operational compiler's required source fragment: compact scalars,
records, references and counted arrays, with explicit operations and control.
The `bytes` spelling is normalized to an array of bytes.  External functions
have typed declarations in a supplied interface; their physical contracts and
catalogue admission remain distinct from expression typing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word Byte WordOp Comparison)

inductive NativeType where
  | unit | word | byte | bool
  | named (name : String)
  | ref (element : NativeType)
  | array (element : NativeType)
  deriving DecidableEq, Repr

def bytesType : NativeType := .array .byte

structure Parameter where
  name : String
  type : NativeType
  deriving DecidableEq, Repr

structure Record where
  name : String
  fields : List Parameter
  deriving DecidableEq, Repr

structure Header where
  name : String
  parameters : List Parameter
  result : NativeType
  deriving DecidableEq, Repr

inductive Effect where
  | pure | effect
  deriving DecidableEq, Repr

structure External where
  header : Header
  cSymbol : String
  effect : Effect
  includeHeader : Option String
  deriving DecidableEq, Repr

structure Opaque where
  name : String
  cType : String
  includeHeader : String
  deriving DecidableEq, Repr

structure Interface where
  records : List Record
  opaques : List Opaque
  functions : List Header
  externals : List External
  deriving DecidableEq, Repr

abbrev Scope := List (String × NativeType)

def lookupRecord (interface : Interface) (name : String) : Option Record :=
  interface.records.find? (fun record => record.name == name)

def lookupFunction (interface : Interface) (name : String) : Option Header :=
  (interface.functions.find? (fun header => header.name == name)).or
    ((interface.externals.find? (fun external => external.header.name == name)).map External.header)

def lookupField (interface : Interface) (record field : String) : Option NativeType := do
  let declaration ← lookupRecord interface record
  let member ← declaration.fields.find? (fun member => member.name == field)
  pure member.type

def validType (interface : Interface) : NativeType → Bool → Bool
  | .unit, storage => !storage
  | .word, _ | .byte, _ | .bool, _ => true
  | .named name, storage =>
      (lookupRecord interface name).isSome ||
        (!storage && interface.opaques.any (fun declaration => declaration.name == name))
  | .ref element, _ => validType interface element false
  | .array element, _ => validType interface element true && decide (element ≠ .unit)

inductive Unary where
  | not | complement | toWord | toByte
  deriving DecidableEq, Repr

inductive Binary where
  | word (operation : WordOp)
  | compare (operation : Comparison)
  | and | or
  deriving DecidableEq, Repr

inductive Expr where
  | word (value : Word)
  | byte (value : Byte)
  | bool (value : Bool)
  | variable (name : String)
  | zero (type : NativeType)
  | null (type : NativeType)
  | new (type : NativeType)
  | newArray (element : NativeType) (count : Expr)
  | field (base : Expr) (name : String)
  | index (array index : Expr)
  | length (array : Expr)
  | slice (array start count : Expr)
  | address (location : Expr)
  | load (reference : Expr)
  | call (function : String) (arguments : List Expr)
  | unary (operation : Unary) (operand : Expr)
  | binary (operation : Binary) (left right : Expr)
  deriving Repr

inductive Statement where
  | declare (name : String) (type : NativeType) (initializer : Expr)
  | set (location value : Expr)
  | branch (condition : Expr) (thenBody elseBody : List Statement)
  | while (condition : Expr) (body : List Statement)
  | switch (selector : Expr) (cases : List (Word × List Statement)) (default : List Statement)
  | break | continue
  | effect (expression : Expr)
  | free (expression : Expr)
  | return (expression : Option Expr)
  | block (body : List Statement)
  deriving Repr

structure Function where
  header : Header
  body : List Statement
  deriving Repr

structure Program where
  name : String
  interface : Interface
  functions : List Function
  deriving Repr

def unaryType : Unary → NativeType → Option NativeType
  | .not, .bool => some .bool
  | .complement, .word => some .word
  | .toWord, .byte => some .word
  | .toByte, .word => some .byte
  | _, _ => none

def binaryType : Binary → NativeType → Option NativeType
  | .word _, .word => some .word
  | .and, .bool | .or, .bool => some .bool
  | .compare .eq, .word | .compare .ne, .word
  | .compare .eq, .byte | .compare .ne, .byte
  | .compare .eq, .bool | .compare .ne, .bool
  | .compare .eq, .ref _ | .compare .ne, .ref _ => some .bool
  | .compare _, .word | .compare _, .byte => some .bool
  | _, _ => none

def locationForm (expression : Expr) : Bool :=
  match expression with
  | .variable _ | .field _ _ | .index _ _ | .load _ => true
  | _ => false

end Mettapedia.GSLT.LanguageDef.NativeOps
