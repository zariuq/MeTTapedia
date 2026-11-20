import Mettapedia.Machines.TIsa.RegisterCodeLowering
import Mettapedia.Machines.TIsa.X86P1ScalarLibrary
import Mettapedia.Machines.TIsa.X86LogicalRecipes

/-!
# Mixed RegisterCode word blocks through certified native components

The selector accepts copies, ADD/SUB, AND/OR/XOR and bounded U64 shifts.
Original RegisterCode execution and backward liveness determine source
results and availability. Register zero remains protected. Logical aliases
use the existing derived recipe; arithmetic uses the p1 template library.
Calls, other operations, structured control and public ABI need their
respective refinements.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86RegisterCodeScalar
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Values := RegisterCodeLowering.Values
abbrev SourceInstruction := RegisterCodeLowering.SourceInstruction
abbrev valuesAt := RegisterCodeLowering.valuesAt

inductive Instruction where
  | copy (instruction : X86CopyBlock.Copy)
  | arithmetic (instruction : X86P1ArithmeticCore.Instruction)
  | logical (instruction : X86LogicalRecipes.Instruction)
  | shift (instruction : X86ShiftBlock.Instruction)

def write : Instruction → RegisterProfile.Write
  | .copy i => ⟨i.destination.val,.copy,[.reg i.source.val]⟩
  | .arithmetic i => ⟨i.destination.val,.binary (X86ResourceBinary.binary i.operation),
      [.reg i.left.val,.reg i.right.val]⟩
  | .logical i => ⟨i.destination.val,.binary (X86LogicalLibrary.binary i.operation),
      [.reg i.left.val,.reg i.right.val]⟩
  | .shift i => ⟨i.destination.val,.shift i.operation i.amount.val,[.reg i.source.val]⟩

def source (instruction : Instruction) : SourceInstruction := (write instruction).source
def destination : Instruction → Fin 12
  | .copy i => i.destination | .arithmetic i => i.destination
  | .logical i => i.destination | .shift i => i.destination
def evaluate : Instruction → Values → Word
  | .copy i, values => values i.source
  | .arithmetic i, values => X86P1ArithmeticCore.evaluate i values
  | .logical i, values => X86LogicalRecipes.evaluate i values
  | .shift i, values => X86ShiftBlock.evaluate i values
def updated (instruction : Instruction) (values : Values) : Values :=
  Function.update values (destination instruction) (evaluate instruction values)

def copy? (d s : Nat) : Option Instruction :=
  if valid : d < 12 ∧ s < 12 ∧ d ≠ 0 then
    some (.copy ⟨⟨s,valid.2.1⟩,⟨d,valid.1⟩,fun same => valid.2.2 (congrArg Fin.val same)⟩)
  else none

def binary? (operation : Binary) (d l r : Nat) : Option Instruction :=
  if valid : d < 12 ∧ l < 12 ∧ r < 12 ∧ d ≠ 0 then
    let dst : Fin 12 := ⟨d,valid.1⟩
    let left : Fin 12 := ⟨l,valid.2.1⟩
    let right : Fin 12 := ⟨r,valid.2.2.1⟩
    let unlocked : dst ≠ 0 := fun same => valid.2.2.2 (congrArg Fin.val same)
    match operation with
    | .add => some (.arithmetic ⟨.add,dst,left,right,unlocked⟩)
    | .sub => some (.arithmetic ⟨.sub,dst,left,right,unlocked⟩)
    | .band => some (.logical ⟨.and,dst,left,right,unlocked⟩)
    | .bor => some (.logical ⟨.or,dst,left,right,unlocked⟩)
    | .bxor => some (.logical ⟨.xor,dst,left,right,unlocked⟩)
    | .mulLo => none
  else none

def shift? (operation : Shift) (amount d s : Nat) : Option Instruction :=
  if valid : d < 12 ∧ s < 12 ∧ amount < 64 ∧ d ≠ 0 then
    some (.shift ⟨operation,⟨d,valid.1⟩,⟨s,valid.2.1⟩,⟨amount,valid.2.2.1⟩,
      fun same => valid.2.2.2 (congrArg Fin.val same)⟩)
  else none

def lower? : SourceInstruction → Option Instruction
  | .op d .copy [.reg s] => copy? d s
  | .op d (.binary operation) [.reg l,.reg r] => binary? operation d l r
  | .op d (.shift operation amount) [.reg s] => shift? operation amount d s
  | _ => none

theorem copy?_source {d s : Nat} {instruction : Instruction}
    (accepted : copy? d s = some instruction) : source instruction = .op d .copy [.reg s] := by
  unfold copy? at accepted
  split at accepted
  · cases Option.some.inj accepted; rfl
  · cases accepted

theorem binary?_source {operation : Binary} {d l r : Nat} {instruction : Instruction}
    (accepted : binary? operation d l r = some instruction) :
    source instruction = .op d (.binary operation) [.reg l,.reg r] := by
  unfold binary? at accepted
  split at accepted
  · cases operation <;> simp only at accepted <;> try contradiction
    all_goals cases Option.some.inj accepted; rfl
  · cases accepted

theorem shift?_source {operation : Shift} {amount d s : Nat} {instruction : Instruction}
    (accepted : shift? operation amount d s = some instruction) :
    source instruction = .op d (.shift operation amount) [.reg s] := by
  unfold shift? at accepted
  split at accepted
  · cases Option.some.inj accepted; rfl
  · cases accepted

theorem lower?_source {input : SourceInstruction} {instruction : Instruction}
    (accepted : lower? input = some instruction) : source instruction = input := by
  unfold lower? at accepted
  split at accepted
  all_goals first | exact copy?_source accepted | exact binary?_source accepted |
    exact shift?_source accepted | cases accepted

theorem lower?_roundtrip (instruction : Instruction) : lower? (source instruction) = some instruction := by
  cases instruction with
  | copy i =>
    rcases i with ⟨input,dst,unlocked⟩
    have nonzero : dst.val ≠ 0 := fun same => unlocked (Fin.ext same)
    simp [source,write,RegisterProfile.Write.source,lower?,copy?,input.isLt,dst.isLt,nonzero]
  | arithmetic i =>
    rcases i with ⟨operation,dst,left,right,unlocked⟩
    have nonzero : dst.val ≠ 0 := fun same => unlocked (Fin.ext same)
    cases operation <;>
      simp [source,write,RegisterProfile.Write.source,lower?,binary?,X86ResourceBinary.binary,
        dst.isLt,left.isLt,right.isLt,nonzero]
  | logical i =>
    rcases i with ⟨operation,dst,left,right,unlocked⟩
    have nonzero : dst.val ≠ 0 := fun same => unlocked (Fin.ext same)
    cases operation <;>
      simp [source,write,RegisterProfile.Write.source,lower?,binary?,X86LogicalLibrary.binary,
        dst.isLt,left.isLt,right.isLt,nonzero]
  | shift i =>
    rcases i with ⟨operation,dst,input,amount,unlocked⟩
    have nonzero : dst.val ≠ 0 := fun same => unlocked (Fin.ext same)
    simp [source,write,RegisterProfile.Write.source,lower?,shift?,input.isLt,dst.isLt,amount.isLt,nonzero]

theorem computes (instruction : Instruction) (values : Values) :
    (write instruction).operation.evaluate
      ((write instruction).arguments.map (RegisterProfile.operandValue (valuesAt values))) =
      some (evaluate instruction values) := by
  cases instruction with
  | copy i => simp [write,evaluate,Scalar.evaluate,RegisterProfile.operandValue,RegisterCodeLowering.valuesAt_fin]
  | arithmetic i =>
    cases selected : i.operation <;>
      simp [write,evaluate,Scalar.evaluate,RegisterProfile.operandValue,RegisterCodeLowering.valuesAt_fin,
        X86ResourceBinary.binary,X86P1ArithmeticCore.evaluate,X86Arithmetic.result,Binary.evaluate,selected]
  | logical i =>
    cases selected : i.operation <;>
      simp [write,evaluate,Scalar.evaluate,RegisterProfile.operandValue,RegisterCodeLowering.valuesAt_fin,
        X86LogicalLibrary.binary,X86LogicalRecipes.evaluate,X86LogicalWord.result,Binary.evaluate,selected]
  | shift i =>
    simp [write,evaluate,Scalar.evaluate,RegisterProfile.operandValue,RegisterCodeLowering.valuesAt_fin,
      X86ShiftBlock.evaluate,i.amount.isLt]

theorem source_step (instruction : Instruction) (values : Values) :
    RegisterCode.step RegisterProfile.semantics (fun _ _ => none) (source instruction)
      (RegisterProfile.initialized (valuesAt values)) =
      some (.next (RegisterProfile.initialized (valuesAt (updated instruction values)))) := by
  rw [source,RegisterProfile.Write.source_step,computes,Option.map_some]
  have dst : (write instruction).destination = (destination instruction).val := by cases instruction <;> rfl
  rw [dst,←RegisterCodeLowering.valuesAt_update]
  rfl

def translation : RegisterCodeLowering.Translation Instruction where
  lower := lower?
  source := source
  update := updated
  source_exact := fun _ _ => lower?_source
  step := source_step

def lowerCode? := RegisterCodeLowering.lowerCode? lower?
def admit? := RegisterCodeLowering.admit? lower?
def finalValues := RegisterCodeLowering.finalValues translation

theorem lowerCode?_source {inputs : List SourceInstruction} {instructions : List Instruction}
    (accepted : lowerCode? inputs = some instructions) : instructions.map source = inputs :=
  RegisterCodeLowering.lowerCode?_source lower? source (fun _ _ => lower?_source) accepted

theorem admitted_source_exec (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word)
    (out : Finset Nat) (instructions : List Instruction)
    (accepted : admit? inputs registers out = some instructions) :
    ∃ following,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      ∀ register ∈ out, following register = some
        (valuesAt (finalValues instructions (RegisterCodeLowering.valuesOf registers)) register) :=
  RegisterCodeLowering.admitted_source_exec translation inputs registers out instructions accepted

def arithmetic (instruction : X86P1ArithmeticCore.Instruction) : X86P1Arithmetic.Instruction :=
  ⟨instruction,.u64,Or.inl rfl⟩

def injectScalar (instruction : X86ScalarLibrary.Instruction) : X86P1ScalarLibrary.Program :=
  Prog.prim (.inr (.inl instruction))

theorem injectScalar_wp (program : X86ScalarLibrary.Program)
    (post : Unit → X86WordLibrary.World → Prop) (world : X86WordLibrary.World) :
    (LibraryLowering.expand injectScalar program).wp X86P1ScalarLibrary.spec.action post world ↔
      program.wp X86ScalarLibrary.spec.action post world := by
  induction program generalizing post world with
  | ret answer => rfl
  | call instruction next ih =>
    simp only [LibraryLowering.expand,injectScalar,Prog.prim,Prog.call_bind,Prog.ret_bind,wp_call]
    change ((X86ScalarLibrary.spec.action instruction).Safe world ∧
      ∀ reply following, (X86ScalarLibrary.spec.action instruction).Step world reply following →
        (LibraryLowering.expand injectScalar (next reply)).wp X86P1ScalarLibrary.spec.action post following) ↔ _
    simp only [ih]

def implementation : Instruction → X86P1ScalarLibrary.Program
  | .copy i => injectScalar (.inl (.copy i))
  | .arithmetic i => Prog.prim (.inl (arithmetic i))
  | .logical i => LibraryLowering.expand injectScalar (X86LogicalRecipes.implementation i)
  | .shift i => Prog.prim (.inr (.inr (.inl i)))

theorem implementation_wp (instruction : Instruction) (values : Values)
    (post : Unit → X86WordLibrary.World → Prop)
    (expected : post () (Cells.encode Finset.univ (updated instruction values))) :
    (implementation instruction).wp X86P1ScalarLibrary.spec.action post
      (Cells.encode Finset.univ values) := by
  cases instruction with
  | copy i =>
    exact X86P1ScalarLibrary.source_wp_step (.inr (.inl (.inl (.copy i)))) values
      (values i.source) rfl post expected
  | arithmetic i =>
    apply X86P1ScalarLibrary.source_wp_step (.inl (arithmetic i)) values
      (evaluate (.arithmetic i) values) _ post expected
    simpa only [X86P1ScalarLibrary.p1,arithmetic,X86P1Arithmetic.evaluate,P1Scalar.normalize,evaluate]
      using X86P1Arithmetic.computes (arithmetic i) values
  | logical i =>
    apply (injectScalar_wp (X86LogicalRecipes.implementation i) post _).mpr
    apply wp_mono X86ScalarLibrary.spec.action _ (X86LogicalRecipes.implementation_wp i values)
    rintro ⟨⟩ world equal
    change world = Cells.encode Finset.univ (updated (.logical i) values) at equal
    subst world
    exact expected
  | shift i =>
    apply X86P1ScalarLibrary.source_wp_step (.inr (.inr (.inl i))) values
      (evaluate (.shift i) values) _ post expected
    exact X86ShiftLibrary.computes (.inl i) values

def program : List Instruction → X86P1ScalarLibrary.Program
  | [] => Prog.ret ()
  | instruction :: later => (implementation instruction).bind fun _ => program later

theorem program_wp (instructions : List Instruction) (values : Values) :
    (program instructions).wp X86P1ScalarLibrary.spec.action
      (fun _ following => following = Cells.encode Finset.univ (finalValues instructions values))
      (Cells.encode Finset.univ values) := by
  induction instructions generalizing values with
  | nil => exact ⟨trivial,by rintro ⟨⟩ following ⟨_,rfl⟩; rfl⟩
  | cons instruction later ih =>
    rw [program,wp_bind]
    apply implementation_wp
    exact ih (updated instruction values)

theorem compile_admitted_on (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word)
    (out : Finset Nat) (instructions : List Instruction)
    (accepted : admit? inputs registers out = some instructions) (values : Values)
    (known : ∀ register ∈ RegisterCodeLowering.available registers,
      registers register = some (valuesAt values register)) (native : State) (stop : Int)
    (input : X86BlockCompiler.At X86P1ScalarLibrary.spec stop (program instructions)
      (Cells.encode Finset.univ values) native) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      (∀ register ∈ out, following register = some
        (valuesAt (finalValues instructions values) register)) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86P1ScalarLibrary.spec (program instructions))).run
        native = .ok () after ∧
      X86StateFrame.Frame X86P1ScalarLibrary.spec.registerWrites X86P1ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86P1ScalarLibrary.spec stop ()
        (Cells.encode Finset.univ (finalValues instructions values)) after := by
  let : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨world,after,_ran,equal,executed,frame,observed⟩ := X86P1ScalarLibrary.compile_wp other extra vector
    stop (program instructions) _ native input _ (program_wp instructions values)
  subst world
  obtain ⟨following,sourceRun,agrees⟩ := RegisterCodeLowering.admitted_source_exec_on translation inputs registers out instructions accepted values known
  exact ⟨following,after,sourceRun,agrees,executed,frame,observed⟩

theorem compile_admitted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word)
    (out : Finset Nat) (instructions : List Instruction)
    (accepted : admit? inputs registers out = some instructions) (native : State) (stop : Int)
    (input : X86BlockCompiler.At X86P1ScalarLibrary.spec stop (program instructions)
      (Cells.encode Finset.univ (RegisterCodeLowering.valuesOf registers)) native) :
    letI : OtherOpcodeHandlers := X86TypedShiftBlock.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      (∀ register ∈ out, following register = some
        (valuesAt (finalValues instructions (RegisterCodeLowering.valuesOf registers)) register)) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86P1ScalarLibrary.spec (program instructions))).run
        native = .ok () after ∧
      X86StateFrame.Frame X86P1ScalarLibrary.spec.registerWrites X86P1ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86P1ScalarLibrary.spec stop ()
        (Cells.encode Finset.univ (finalValues instructions (RegisterCodeLowering.valuesOf registers))) after :=
  compile_admitted_on other extra vector inputs registers out instructions accepted
    (RegisterCodeLowering.valuesOf registers) (RegisterCodeLowering.available_readback registers)
    native stop input

namespace Controls

def mixed : List SourceInstruction :=
 [.op 4 .copy [.reg 1],
  .op 3 (.binary .add) [.reg 4,.reg 2],
  .op 2 (.binary .bxor) [.reg 1,.reg 2],
  .op 4 (.binary .sub) [.reg 1,.reg 4],
  .op 5 (.shift .rightUnsigned 1) [.reg 2]]
def registers (register : Nat) : Option Word :=
  if register = 1 then some 0xffffffffffffffff else if register = 2 then some 2 else none
def observed (code : List SourceInstruction) : Option (List (Option Word)) :=
  (RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) code registers).bind fun result =>
    match result with
    | .next after => some ([2,3,4,5].map after)
    | .ret _ => none

theorem admitted_mixed_block : (admit? mixed registers {2,3,4,5}).isSome = true := by decide

theorem mixed_source_results :
    observed mixed = some [some 0xfffffffffffffffd,some 1,some 0,some 0x7ffffffffffffffe] := by decide

theorem admission_controls :
    (lower? (.op 0 .copy [.reg 1])).isNone = true ∧
    (lower? (.op 12 .copy [.reg 1])).isNone = true ∧
    (lower? (.op 2 (.binary .add) [.reg 1,.reg 12])).isNone = true ∧
    (lower? (.op 2 (.binary .mulLo) [.reg 1,.reg 2])).isNone = true ∧
    (lower? (.op 2 (.binary .add) [.reg 1,.lit 2])).isNone = true ∧
    (lower? (.op 2 (.shift .left 64) [.reg 1])).isNone = true ∧
    (lower? (.op 2 (.shift .left 63) [.reg 1])).isSome = true := by decide

theorem missing_operand_rejected :
    admit? mixed (fun register => if register = 1 then some 0xffffffffffffffff else none) {2,3,4,5} = none ∧
    RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) mixed
      (fun register => if register = 1 then some 0xffffffffffffffff else none) = none := by decide

theorem arbitrary_dead_registers (value : Word) :
    ∀ register ∈ RegisterCodeLowering.available registers,
      registers register = some (valuesAt (fun r =>
        if r = 1 then 0xffffffffffffffff else if r = 2 then 2 else value) register) := by
  intro register present
  have choices : register = 1 ∨ register = 2 := by
    obtain ⟨_,initialized⟩ := Finset.mem_filter.mp present
    by_cases one : register = 1
    · exact Or.inl one
    · by_cases two : register = 2
      · exact Or.inr two
      · simp [registers,one,two] at initialized
  rcases choices with rfl | rfl <;> simp [registers,valuesAt,RegisterCodeLowering.valuesAt]

theorem exact_native_steps :
    (lowerCode? mixed).map (fun instructions =>
      X86BlockCompiler.steps X86P1ScalarLibrary.spec (program instructions)) = some 9 := by decide

theorem exact_native_bytes :
    (lowerCode? mixed).map (fun instructions =>
      X86BlockCompiler.code X86P1ScalarLibrary.spec (program instructions)) =
      some [0x49,0x89,0xf0, 0x4c,0x89,0xc1, 0x48,0x01,0xd1, 0x48,0x31,0xf2,
            0x49,0x89,0xf6, 0x4d,0x29,0xc6, 0x4d,0x89,0xf0, 0x49,0x89,0xd1, 0x49,0xc1,0xe9,1] := by decide

def wrongOperation : List SourceInstruction :=
 [.op 4 .copy [.reg 1],
  .op 3 (.binary .add) [.reg 4,.reg 2],
  .op 2 (.binary .bor) [.reg 1,.reg 2],
  .op 4 (.binary .sub) [.reg 1,.reg 4],
  .op 5 (.shift .rightUnsigned 1) [.reg 2]]

theorem wrong_operation_changes_result :
    observed wrongOperation = some [some 0xffffffffffffffff,some 1,some 0,some 0x7fffffffffffffff] ∧
    observed wrongOperation ≠ observed mixed := by decide

end Controls

#print axioms lower?_source
#print axioms lower?_roundtrip
#print axioms computes
#print axioms source_step
#print axioms admitted_source_exec
#print axioms injectScalar_wp
#print axioms implementation_wp
#print axioms program_wp
#print axioms compile_admitted_on
#print axioms compile_admitted
#print axioms Controls.admitted_mixed_block
#print axioms Controls.mixed_source_results
#print axioms Controls.admission_controls
#print axioms Controls.missing_operand_rejected
#print axioms Controls.arbitrary_dead_registers
#print axioms Controls.exact_native_steps
#print axioms Controls.exact_native_bytes
#print axioms Controls.wrong_operation_changes_result
end Mettapedia.Machines.TIsa.X86RegisterCodeScalar
