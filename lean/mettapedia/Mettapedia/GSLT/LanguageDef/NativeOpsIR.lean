import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState

/-!
# Typed native control and data intermediate representation

Expressions lower to ordered temporary assignments. Context checks, pointer
checks, writes, lexical scopes, labels and jumps remain explicit operations.
This representation contains no raw C body, guest-name dispatch or semantic
template selector. Function and primitive names are references to the
separately admitted typed tables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeIR

inductive Atom where
  | temporary (identity : Nat) (type : NativeType)
  | iterationCounter (identity : Nat)
  | localAddress (name : String) (type : NativeType)
  | word (value : BitVec 64)
  | zero (type : NativeType)
  | unit
  deriving DecidableEq, Repr

def Atom.type : Atom → NativeType
  | .temporary _ type => type
  | .iterationCounter _ => .word
  | .localAddress _ type => .ref type
  | .word _ => .word
  | .zero type => type
  | .unit => .unit

/-- A helper can assign a pointer into an array value's `data` field. -/
inductive Place where
  | temporary (identity : Nat) (type : NativeType)
  | local (name : String) (type : NativeType)
  | arrayData (array : Atom) (element : NativeType)
  | arrayLength (array : Atom)
  deriving DecidableEq, Repr

def Place.type : Place → NativeType
  | .temporary _ type | .local _ type => type
  | .arrayData _ element => .ref element
  | .arrayLength _ => .word

inductive Condition where
  | value (value : Atom)
  | negated (value : Atom)
  deriving DecidableEq, Repr

inductive LabelKind where
  | entry | exit
  deriving DecidableEq, Repr

structure Label where
  kind : LabelKind
  identity : Nat
  deriving DecidableEq, Repr

/-- Pure C operations read already evaluated operands. -/
inductive PureOperation where
  | word (value : BitVec 64)
  | byte (value : BitVec 8)
  | bool (value : Bool)
  | zero (type : NativeType)
  | copy (value : Atom)
  | readLocal (name : String)
  | fieldValue (record : Atom) (recordType : String) (fieldIndex : Nat)
  | fieldAddress (reference : Atom) (recordType : String) (fieldIndex : Nat)
  | elementAddress (array index : Atom) (element : NativeType)
  | indirectRead (reference : Atom)
  | length (array : Atom)
  | unary (operation : Unary) (operand : Atom)
  | binary (operation : Binary) (left right : Atom)
  deriving Repr

/-- Calls to the checked shared data runtime. Size operands use the declared ABI layout. -/
inductive MemoryOperation where
  | reference (value : Atom)
  | index (array index : Atom) (element : NativeType)
  | slice (array start count : Atom) (element : NativeType)
  | allocate (count : Atom) (element : NativeType)
  | release (value : Atom) (element : NativeType)
  deriving Repr

inductive CallTarget where
  | function (name : String)
  | external (name : String)
  deriving DecidableEq, Repr

/-- A jump can leave several nested scopes, unlike a switch's ordinary arm exit. -/
inductive Instruction where
  | temporary (identity : Nat) (type : NativeType) (operation : PureOperation)
  | assign (destination : Place) (value : Atom)
  | helper (destination : Option Place) (operation : MemoryOperation)
  | call (destination : Option Place) (target : CallTarget) (arguments : List Atom)
  | checkContextExists
  | checkContext
  | checkedNumericGuard (operation : NativeWord64.WordOp) (right : Atom)
  | declareLocal (name : String) (type : NativeType) (value : Atom)
  | write (reference value : Atom)
  | writeElement (array index value : Atom)
  | forWord (counter : Nat) (bound : Atom) (body : List Instruction)
  | branch (condition : Condition) (whenTrue whenFalse : List Instruction)
  | switch (selector : Atom) (cases : List (BitVec 64 × List Instruction))
      (otherwise : List Instruction)
  | scope (body : List Instruction)
  | label (label : Label)
  | jump (label : Label)
  | return (value : Atom)
  deriving Repr

structure Function where
  header : Header
  body : List Instruction
  temporaryCount : Nat
  deriving Repr

structure Program where
  name : String
  interface : Interface
  functions : List Function
  deriving Repr

structure LoopLabels where
  entry : Label
  exit : Label
  deriving DecidableEq, Repr

/-- The temporary counter belongs to compilation and does not cap guest evaluation. -/
structure Supply where
  next : Nat
  deriving DecidableEq, Repr

def fresh (supply : Supply) : Nat × Supply := (supply.next + 1, ⟨supply.next + 1⟩)

theorem fresh_strict (supply : Supply) : supply.next < (fresh supply).1 := by
  simp [fresh]

theorem fresh_supply (supply : Supply) : (fresh supply).2.next = (fresh supply).1 := rfl

theorem consecutive_fresh_distinct (supply : Supply) :
    (fresh supply).1 ≠ (fresh (fresh supply).2).1 := by
  simp [fresh]

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeIR
