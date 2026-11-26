import Mettapedia.Machines.TIsa.Scalar
import Mettapedia.Machines.TIsa.Outcome

/-!
# Structured source data for the actual p1 export

This is the emitter's compilation presentation over the existing machine
resources. Instruction annotations retain the exported type tag separately from the
region-aware type inferred by admission. Register, width, frame-slot, scale and
word fields have their actual finite domains. Semantic admission is separate:
the data can retain a zero FUND or an invalid return outcome for rejection.

The cost functions reproduce the natural bound and its overflow flag; they do
not move payment points. Source paths follow the live export's child convention.
The word profile is the default. The Transform profile adds store operations
to this same instruction and statement syntax. The profile index excludes
store effects from word-only programs, rather than inventing a default result
for an unsupported operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1Source

universe u

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

/-- Operands of the Transform operations. A semantic instantiation supplies
its premise-role, pattern and guard types; a lowered one may use certified
descriptor indices instead. -/
inductive StoreOp (Role : Type) (Pattern Guard : Type u) where
  | size (dst : Reg)
  | «open» (level : ℕ)
  | premise (role : Role) (pattern : Pattern) (level : ℕ) (index dst : Reg)
  | test (guard : Guard) (level : ℕ) (dst : Reg)
  | take (level slot : ℕ)
  | make (level slot : ℕ)
  deriving DecidableEq, Repr

/-- A word instruction is available in either profile; only the Transform
profile can carry a store operation. -/
inductive Instruction (Effect : Type u) : Bool → Type u where
  | immediate {withStore : Bool} (ty : TypeTag) (dst : Reg) (value : Word) : Instruction Effect withStore
  | move {withStore : Bool} (ty : TypeTag) (dst source : Reg) : Instruction Effect withStore
  | binary {withStore : Bool} (operation : Binary) (ty : TypeTag) (dst left right : Reg) : Instruction Effect withStore
  | shift {withStore : Bool} (operation : Shift) (ty : TypeTag) (dst source : Reg) (amount : Nat) : Instruction Effect withStore
  | extract {withStore : Bool} (ty : TypeTag) (dst source : Reg) (low width : Nat) : Instruction Effect withStore
  | compare {withStore : Bool} (condition : Comparison) (ty : TypeTag) (dst left : Reg) (right : Operand) : Instruction Effect withStore
  | select {withStore : Bool} (ty : TypeTag) (dst condition yes no : Reg) : Instruction Effect withStore
  | address {withStore : Bool} (region : Region) (dst base : Reg) (index : Option Reg) (scale : Fin 4) (displacement : BitVec 32) : Instruction Effect withStore
  | load {withStore : Bool} (ty : TypeTag) (width : Width) (region : Region) (dst base : Reg) (displacement : BitVec 32) : Instruction Effect withStore
  | loadFrame {withStore : Bool} (ty : TypeTag) (dst : Reg) (slot : Fin 24) : Instruction Effect withStore
  | store {withStore : Bool} (width : Width) (region : Region) (base : Reg) (displacement : BitVec 32) (source : Reg) : Instruction Effect withStore
  | transform (operation : Effect) : Instruction Effect true
  deriving DecidableEq, Repr

inductive Statement (Effect : Type u) (withStore : Bool) where
  | skip
  | instruction (value : Instruction Effect withStore)
  | seq (first second : Statement Effect withStore)
  | branch (condition : Reg) (yes no : Statement Effect withStore)
  | counted (index bound : Reg) (cap : BitVec 32) (body : Statement Effect withStore)
  | early (index bound continuation : Reg) (cap : BitVec 32) (body : Statement Effect withStore)
  | ret (outcome : ExitStatus) (source : Reg)
  | fund (units : BitVec 32)
  deriving DecidableEq, Repr

/-- The existing word profile has no store payload and stays in `Type`.
The Transform compiler uses the same syntax at its own payload type. -/
abbrev Instr := Instruction (PEmpty : Type) false
abbrev Stmt := Statement (PEmpty : Type) false

namespace Instr
@[match_pattern] abbrev immediate := @Instruction.immediate (PEmpty : Type) false
@[match_pattern] abbrev move := @Instruction.move (PEmpty : Type) false
@[match_pattern] abbrev binary := @Instruction.binary (PEmpty : Type) false
@[match_pattern] abbrev shift := @Instruction.shift (PEmpty : Type) false
@[match_pattern] abbrev extract := @Instruction.extract (PEmpty : Type) false
@[match_pattern] abbrev compare := @Instruction.compare (PEmpty : Type) false
@[match_pattern] abbrev select := @Instruction.select (PEmpty : Type) false
@[match_pattern] abbrev address := @Instruction.address (PEmpty : Type) false
@[match_pattern] abbrev load := @Instruction.load (PEmpty : Type) false
@[match_pattern] abbrev loadFrame := @Instruction.loadFrame (PEmpty : Type) false
@[match_pattern] abbrev store := @Instruction.store (PEmpty : Type) false
end Instr

namespace Stmt
@[match_pattern] abbrev skip := @Statement.skip (PEmpty : Type) false
@[match_pattern] abbrev instruction := @Statement.instruction (PEmpty : Type) false
@[match_pattern] abbrev seq := @Statement.seq (PEmpty : Type) false
@[match_pattern] abbrev branch := @Statement.branch (PEmpty : Type) false
@[match_pattern] abbrev counted := @Statement.counted (PEmpty : Type) false
@[match_pattern] abbrev early := @Statement.early (PEmpty : Type) false
@[match_pattern] abbrev ret := @Statement.ret (PEmpty : Type) false
@[match_pattern] abbrev fund := @Statement.fund (PEmpty : Type) false
end Stmt

variable {Effect : Type u}

def Instruction.toStore : Instr → Instruction Effect true
  | .immediate ty dst v => .immediate ty dst v
  | .move ty dst source => .move ty dst source
  | .binary op ty dst left right => .binary op ty dst left right
  | .shift op ty dst source k => .shift op ty dst source k
  | .extract ty dst source low width => .extract ty dst source low width
  | .compare c ty dst left right => .compare c ty dst left right
  | .select ty dst c yes no => .select ty dst c yes no
  | .address region dst base index scale disp => .address region dst base index scale disp
  | .load ty width region dst base disp => .load ty width region dst base disp
  | .loadFrame ty dst slot => .loadFrame ty dst slot
  | .store width region base disp source => .store width region base disp source

def Instruction.view : Instruction Effect true → (Instr ⊕ Effect)
  | .immediate ty dst v => .inl (.immediate ty dst v)
  | .move ty dst source => .inl (.move ty dst source)
  | .binary op ty dst left right => .inl (.binary op ty dst left right)
  | .shift op ty dst source k => .inl (.shift op ty dst source k)
  | .extract ty dst source low width => .inl (.extract ty dst source low width)
  | .compare c ty dst left right => .inl (.compare c ty dst left right)
  | .select ty dst c yes no => .inl (.select ty dst c yes no)
  | .address region dst base index scale disp => .inl (.address region dst base index scale disp)
  | .load ty width region dst base disp => .inl (.load ty width region dst base disp)
  | .loadFrame ty dst slot => .inl (.loadFrame ty dst slot)
  | .store width region base disp source => .inl (.store width region base disp source)
  | .transform operation => .inr operation

@[simp] theorem Instruction.view_toStore (i : Instr) : (i.toStore (Effect := Effect)).view = .inl i := by
  cases i <;> rfl

theorem Instruction.view_rebuild (i : Instruction Effect true) :
    (match i.view with | .inl word => word.toStore | .inr effect => .transform effect) = i := by
  cases i <;> rfl

def Statement.toStore : Stmt → Statement Effect true
  | .skip => .skip
  | .instruction i => .instruction i.toStore
  | .seq first second => .seq first.toStore second.toStore
  | .branch c yes no => .branch c yes.toStore no.toStore
  | .counted index bound cap body => .counted index bound cap body.toStore
  | .early index bound k cap body => .early index bound k cap body.toStore
  | .ret outcome source => .ret outcome source
  | .fund units => .fund units

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

structure SourceProgram (Effect : Type u) (withStore : Bool) where
  regions : List RegionDecl
  entry : List EntryReg
  body : Statement Effect withStore
  deriving DecidableEq, Repr

abbrev Program := SourceProgram (PEmpty : Type) false

namespace Program
@[match_pattern] abbrev mk := @SourceProgram.mk (PEmpty : Type) false
abbrev regions (program : Program) := SourceProgram.regions program
abbrev entry (program : Program) := SourceProgram.entry program
abbrev body (program : Program) := SourceProgram.body program
end Program

def Instruction.reads : Instr → List Reg
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

def Instruction.destination? : Instr → Option Reg
  | .immediate _ dst _ | .move _ dst _ | .binary _ _ dst .. | .shift _ _ dst ..
  | .extract _ dst .. | .compare _ _ dst .. | .select _ dst ..
  | .address _ dst .. | .load _ _ _ dst .. | .loadFrame _ dst _ => some dst
  | .store .. => none

def Statement.fundPoints : Stmt → Nat
  | .fund _ => 1
  | .seq first second | .branch _ first second => first.fundPoints + second.fundPoints
  | .counted _ _ _ body | .early _ _ _ _ body => body.fundPoints
  | _ => 0

def Statement.costBound : Stmt → Nat
  | .fund units => units.toNat
  | .seq first second => first.costBound + second.costBound
  | .branch _ yes no => max yes.costBound no.costBound
  | .counted _ _ cap body | .early _ _ _ cap body => cap.toNat * body.costBound
  | _ => 0

def Statement.boundFits (statement : Stmt) : Bool := decide (statement.costBound < 2 ^ 64)

def Statement.reportedBound (statement : Stmt) : Word :=
  if statement.boundFits then BitVec.ofNat 64 statement.costBound else (0xffffffffffffffff#64)

theorem Statement.reportedBound_exact (statement : Stmt) (fits : statement.boundFits = true) :
    statement.reportedBound.toNat = statement.costBound := by
  have bound : statement.costBound < 2 ^ 64 := of_decide_eq_true fits
  rw [reportedBound, if_pos fits]
  exact Nat.mod_eq_of_lt bound

def Statement.atPath : Stmt → List Nat → Option Stmt
  | statement, [] => some statement
  | .seq first _, 0 :: rest => first.atPath rest
  | .seq _ second, 1 :: rest => second.atPath rest
  | .branch _ yes _, 1 :: rest => yes.atPath rest
  | .branch _ _ no, 2 :: rest => no.atPath rest
  | .counted _ _ _ body, 0 :: rest | .early _ _ _ _ body, 0 :: rest => body.atPath rest
  | _, _ => none
termination_by _ path => path.length

namespace Instr
export Instruction (reads destination?)
end Instr

namespace Stmt
export Statement (fundPoints costBound boundFits reportedBound reportedBound_exact atPath)
end Stmt

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
