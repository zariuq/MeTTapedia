import Mettapedia.Machines.TIsa.Scalar
import Mettapedia.Machines.TIsa.Outcome

/-!
# Structured source data for the actual p1 export

This is the emitter's compilation presentation over the existing machine
resources. Instruction annotations retain the C type tag separately from the
region-aware type inferred by admission. Register, width, frame-slot, scale and
word fields have their actual finite domains. Semantic admission is separate:
the data can retain a zero FUND or an invalid return outcome for rejection.

The cost functions reproduce the natural bound and its overflow flag; they do
not move payment points. Source paths follow the live export's child convention.
No machine store or second execution authority is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1Source

abbrev Reg := Fin 12
abbrev Region := Fin 9

inductive TypeTag where
  | uninit | u64 | u32z | i32s | boolean | pointer
  deriving DecidableEq, Repr

inductive Width where
  | byte | word32 | word64
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .byte => 1 | .word32 => 4 | .word64 => 8

inductive Operand where
  | register (source : Reg)
  | immediate (value : Word)
  deriving DecidableEq, Repr

inductive Instr where
  | immediate (ty : TypeTag) (dst : Reg) (value : Word)
  | move (ty : TypeTag) (dst source : Reg)
  | binary (operation : Binary) (ty : TypeTag) (dst left right : Reg)
  | shift (operation : Shift) (ty : TypeTag) (dst source : Reg) (amount : Nat)
  | extract (ty : TypeTag) (dst source : Reg) (low width : Nat)
  | compare (condition : Comparison) (ty : TypeTag) (dst left : Reg) (right : Operand)
  | select (ty : TypeTag) (dst condition yes no : Reg)
  | address (region : Region) (dst base : Reg) (index : Option Reg) (scale : Fin 4) (displacement : BitVec 32)
  | load (ty : TypeTag) (width : Width) (region : Region) (dst base : Reg) (displacement : BitVec 32)
  | loadFrame (ty : TypeTag) (dst : Reg) (slot : Fin 24)
  | store (width : Width) (region : Region) (base : Reg) (displacement : BitVec 32) (source : Reg)
  deriving DecidableEq, Repr

inductive Stmt where
  | skip
  | instruction (value : Instr)
  | seq (first second : Stmt)
  | branch (condition : Reg) (yes no : Stmt)
  | counted (index bound : Reg) (cap : BitVec 32) (body : Stmt)
  | early (index bound continuation : Reg) (cap : BitVec 32) (body : Stmt)
  | ret (outcome : ExitStatus) (source : Reg)
  | fund (units : BitVec 32)
  deriving DecidableEq, Repr

inductive Mode where
  | absent | readOnly | readWrite
  deriving DecidableEq, Repr

structure RegionDecl where
  mode : Mode
  minimum : BitVec 32
  alignment : BitVec 32
  deriving DecidableEq, Repr

structure EntryReg where
  register : Reg
  ty : TypeTag
  region : Region
  deriving DecidableEq, Repr

structure Program where
  regions : List RegionDecl
  entry : List EntryReg
  body : Stmt
  deriving DecidableEq, Repr

def Instr.reads : Instr → List Reg
  | .immediate .. => []
  | .move _ _ source | .shift _ _ _ source _ | .extract _ _ source .. => [source]
  | .binary _ _ _ left right => [left, right]
  | .compare _ _ _ left (.register right) => [left, right]
  | .compare _ _ _ left (.immediate _) => [left]
  | .select _ _ condition yes no => [condition, yes, no]
  | .address _ _ base index _ _ => base :: index.toList
  | .load _ _ _ _ base _ => [base]
  | .loadFrame .. => [0]
  | .store _ _ base _ value => [base, value]

def Instr.destination? : Instr → Option Reg
  | .immediate _ dst _ | .move _ dst _ | .binary _ _ dst .. | .shift _ _ dst ..
  | .extract _ dst .. | .compare _ _ dst .. | .select _ dst ..
  | .address _ dst .. | .load _ _ _ dst .. | .loadFrame _ dst _ => some dst
  | .store .. => none

def Stmt.fundPoints : Stmt → Nat
  | .fund _ => 1
  | .seq first second | .branch _ first second => first.fundPoints + second.fundPoints
  | .counted _ _ _ body | .early _ _ _ _ body => body.fundPoints
  | _ => 0

def Stmt.costBound : Stmt → Nat
  | .fund units => units.toNat
  | .seq first second => first.costBound + second.costBound
  | .branch _ yes no => max yes.costBound no.costBound
  | .counted _ _ cap body | .early _ _ _ cap body => cap.toNat * body.costBound
  | _ => 0

def Stmt.boundFits (statement : Stmt) : Bool := decide (statement.costBound < 2 ^ 64)

def Stmt.reportedBound (statement : Stmt) : Word :=
  if statement.boundFits then BitVec.ofNat 64 statement.costBound else (0xffffffffffffffff#64)

theorem Stmt.reportedBound_exact (statement : Stmt) (fits : statement.boundFits = true) :
    statement.reportedBound.toNat = statement.costBound := by
  have bound : statement.costBound < 2 ^ 64 := of_decide_eq_true fits
  rw [reportedBound, if_pos fits]
  exact Nat.mod_eq_of_lt bound

def Stmt.atPath : Stmt → List Nat → Option Stmt
  | statement, [] => some statement
  | .seq first _, 0 :: rest => first.atPath rest
  | .seq _ second, 1 :: rest => second.atPath rest
  | .branch _ yes _, 1 :: rest => yes.atPath rest
  | .branch _ _ no, 2 :: rest => no.atPath rest
  | .counted _ _ _ body, 0 :: rest | .early _ _ _ _ body, 0 :: rest => body.atPath rest
  | _, _ => none
termination_by _ path => path.length

namespace Controls
private def maximum : Stmt :=
  .seq (.counted 1 2 (4294967295#32) (.fund (4294967295#32)))
    (.counted 3 4 (2#32) (.fund (4294967295#32)))

theorem exact_maximum_fits :
    maximum.boundFits = true ∧ maximum.reportedBound = (0xffffffffffffffff#64) := by decide

theorem overflowing_nested_bound :
    (Stmt.counted 1 2 (4294967295#32) (.counted 3 4 (4294967295#32) (.fund 2))).boundFits = false := by decide

theorem repeated_operands_share_register :
    (Instr.binary .add .u64 3 1 1).reads.toFinset = {1} := by decide
end Controls

end Mettapedia.Machines.TIsa.P1Source
