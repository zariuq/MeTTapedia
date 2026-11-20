import Mettapedia.Machines.TIsa.X86LogicalRecipes
import Mettapedia.Machines.TIsa.RegisterCodeLowering

/-!
# RegisterCode logical blocks through the native component compiler

The executable lowering accepts register-only U64 AND/OR/XOR instructions
within the existing twelve-register placement and protects register zero.
The source is RegisterCode's executor and its backward liveness check.
Admission computes availability from the actual source register file; unused
source registers may remain unset.
Accepted blocks expand through the certified alias-aware logical recipes.
Native placement, readiness, frames and exact fetched counts remain explicit.
Control, other scalar operations and the public ABI are separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86RegisterCodeLogical
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Instruction := X86LogicalRecipes.Instruction
abbrev Values := X86LogicalRecipes.Values
abbrev SourceInstruction := RegisterCode.Instr Word Scalar Nat Nat

def source (instruction : Instruction) : SourceInstruction :=
  .op instruction.destination.val (.binary (X86LogicalLibrary.binary instruction.operation))
    [.reg instruction.left.val,.reg instruction.right.val]

def kind? : Binary → Option X86LogicalWord.Kind
  | .band => some .and
  | .bor => some .or
  | .bxor => some .xor
  | _ => none

def select? (operation : Binary) (destination left right : Nat) : Option Instruction := do
  let kind ← kind? operation
  if fits : destination < 12 ∧ left < 12 ∧ right < 12 ∧ destination ≠ 0 then
    some ⟨kind,⟨destination,fits.1⟩,⟨left,fits.2.1⟩,⟨right,fits.2.2.1⟩,
      fun same => fits.2.2.2 (congrArg Fin.val same)⟩
  else none

def lower? : SourceInstruction → Option Instruction
  | .op destination (.binary operation) [.reg left,.reg right] =>
      select? operation destination left right
  | _ => none

theorem kind?_source {operation : Binary} {kind : X86LogicalWord.Kind}
    (accepted : kind? operation = some kind) : X86LogicalLibrary.binary kind = operation := by
  cases operation <;> simp [kind?] at accepted <;> subst kind <;> rfl

theorem select?_source {operation : Binary} {destination left right : Nat}
    {instruction : Instruction} (accepted : select? operation destination left right = some instruction) :
    source instruction = .op destination (.binary operation) [.reg left,.reg right] := by
  unfold select? at accepted
  cases selected : kind? operation with
  | none => simp [selected] at accepted
  | some kind =>
    simp only [selected] at accepted
    split at accepted
    · cases Option.some.inj accepted
      simp only [source,kind?_source selected]
    · cases accepted

theorem lower?_source {input : SourceInstruction} {instruction : Instruction}
    (accepted : lower? input = some instruction) : source instruction = input := by
  unfold lower? at accepted
  split at accepted
  · exact select?_source accepted
  · cases accepted

theorem lower?_roundtrip (instruction : Instruction) : lower? (source instruction) = some instruction := by
  rcases instruction with ⟨operation,destination,left,right,unlocked⟩
  have nonzero : destination.val ≠ 0 := fun same => unlocked (Fin.ext same)
  cases operation <;>
    simp [source,lower?,select?,kind?,X86LogicalLibrary.binary,
      destination.isLt,left.isLt,right.isLt,nonzero]

def lowerCode? : List SourceInstruction → Option (List Instruction) :=
  RegisterCodeLowering.lowerCode? lower?

theorem lowerCode?_source {inputs : List SourceInstruction} {instructions : List Instruction}
    (accepted : lowerCode? inputs = some instructions) : instructions.map source = inputs :=
  RegisterCodeLowering.lowerCode?_source lower? source (fun _ _ => lower?_source) accepted

theorem lowerCode?_roundtrip (instructions : List Instruction) :
    lowerCode? (instructions.map source) = some instructions :=
  RegisterCodeLowering.lowerCode?_roundtrip lower? source lower?_roundtrip instructions

def valuesAt : Values → Nat → Word := RegisterCodeLowering.valuesAt

theorem valuesAt_fin (values : Values) (register : Fin 12) :
    valuesAt values register.val = values register := RegisterCodeLowering.valuesAt_fin values register

theorem valuesAt_update (values : Values) (destination : Fin 12) (result : Word) :
    valuesAt (Function.update values destination result) =
      Function.update (valuesAt values) destination.val result :=
  RegisterCodeLowering.valuesAt_update values destination result

theorem source_step (instruction : Instruction) (values : Values) :
    RegisterCode.step RegisterProfile.semantics (fun _ _ => none) (source instruction)
      (RegisterProfile.initialized (valuesAt values)) =
      some (.next (RegisterProfile.initialized (valuesAt (X86LogicalRecipes.updated instruction values)))) := by
  let write : RegisterProfile.Write :=
    ⟨instruction.destination.val,.binary (X86LogicalLibrary.binary instruction.operation),
      [.reg instruction.left.val,.reg instruction.right.val]⟩
  change RegisterCode.step RegisterProfile.semantics (fun _ _ => none) write.source _ = _
  rw [RegisterProfile.Write.source_step]
  have computed : write.operation.evaluate (write.arguments.map (RegisterProfile.operandValue (valuesAt values))) =
      some (X86LogicalRecipes.evaluate instruction values) := by
    rcases instruction with ⟨operation,destination,left,right,unlocked⟩
    cases operation <;> simp [write,Scalar.evaluate,Binary.evaluate,RegisterProfile.operandValue,
      X86LogicalLibrary.binary,X86LogicalRecipes.evaluate,X86LogicalWord.result,valuesAt_fin]
  rw [computed]
  simp only [Option.map_some,X86LogicalRecipes.updated,valuesAt_update]
  rfl

def translation : RegisterCodeLowering.Translation Instruction where
  lower := lower?
  source := source
  update := X86LogicalRecipes.updated
  source_exact := fun _ _ => lower?_source
  step := source_step

def finalValues (instructions : List Instruction) (values : Values) : Values :=
  instructions.foldl (fun before instruction => X86LogicalRecipes.updated instruction before) values

theorem source_exec (instructions : List Instruction) (values : Values) :
    RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) (instructions.map source)
      (RegisterProfile.initialized (valuesAt values)) =
      some (.next (RegisterProfile.initialized (valuesAt (finalValues instructions values)))) :=
  RegisterCodeLowering.source_exec translation instructions values

def program : List Instruction → X86LogicalRecipes.Program
  | [] => Prog.ret ()
  | instruction :: later => (Prog.prim instruction).bind fun _ => program later

theorem program_wp (instructions : List Instruction) (values : Values) :
    (program instructions).wp X86LogicalRecipes.action
      (fun _ following => following = finalValues instructions values) values := by
  induction instructions generalizing values with
  | nil => exact ⟨trivial,by rintro ⟨⟩ following ⟨_,rfl⟩; rfl⟩
  | cons instruction later ih =>
    change (Prog.call instruction (fun _ => program later)).wp X86LogicalRecipes.action _ values
    refine ⟨⟨X86LogicalRecipes.computes instruction values,?_⟩,?_⟩
    · rintro ⟨⟩ following rfl
      exact (ih (X86LogicalRecipes.updated instruction values)).1
    · rintro ⟨⟩ following ⟨⟨⟩,middle,rfl,run⟩
      exact (ih (X86LogicalRecipes.updated instruction values)).2 () following run

theorem source_exec_live (instructions : List Instruction) (values : Values) (initializedKeys out : Finset Nat)
    (checked : RegisterProfile.initialCheck (instructions.map source) initializedKeys out = true) :
    ∃ registers,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) (instructions.map source)
        (RegisterProfile.initializedOn initializedKeys (valuesAt values)) = some (.next registers) ∧
      ∀ register ∈ out, registers register = some (valuesAt (finalValues instructions values) register) := by
  have related := RegisterProfile.partial_initialization_live (instructions.map source)
    initializedKeys out (valuesAt values) checked
  rw [source_exec] at related
  cases execution : RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) (instructions.map source)
      (RegisterProfile.initializedOn initializedKeys (valuesAt values)) with
  | none => rw [execution] at related; cases related
  | some result =>
    rw [execution] at related
    cases related with
    | some agrees =>
      cases result with
      | ret value => cases agrees
      | next registers => exact ⟨registers,rfl,fun register present => (agrees register present).symm⟩

theorem compile (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (inputs : List SourceInstruction) (instructions : List Instruction)
    (accepted : lowerCode? inputs = some instructions) (values : Values) (native : State) (stop : Int)
    (input : X86BlockCompiler.At X86ScalarLibrary.spec stop
      (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions))
      (Cells.encode Finset.univ values) native) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs
        (RegisterProfile.initialized (valuesAt values)) =
        some (.next (RegisterProfile.initialized (valuesAt (finalValues instructions values)))) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86ScalarLibrary.spec
        (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions)))).run native = .ok () after ∧
      X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86ScalarLibrary.spec stop ()
        (Cells.encode Finset.univ (finalValues instructions values)) after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,after,_ran,equal,executed,frame,observed⟩ :=
    X86LogicalRecipes.compile_wp other vector stop (program instructions) values native input _
      (program_wp instructions values)
  subst following
  refine ⟨after,?_,executed,frame,observed⟩
  rw [← lowerCode?_source accepted]
  exact source_exec instructions values

theorem compile_live (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (inputs : List SourceInstruction) (instructions : List Instruction)
    (accepted : lowerCode? inputs = some instructions) (values : Values) (native : State) (stop : Int)
    (initializedKeys out : Finset Nat)
    (checked : RegisterProfile.initialCheck inputs initializedKeys out = true)
    (input : X86BlockCompiler.At X86ScalarLibrary.spec stop
      (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions))
      (Cells.encode Finset.univ values) native) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ registers after,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs
        (RegisterProfile.initializedOn initializedKeys (valuesAt values)) = some (.next registers) ∧
      (∀ register ∈ out, registers register = some (valuesAt (finalValues instructions values) register)) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86ScalarLibrary.spec
        (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions)))).run native = .ok () after ∧
      X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86ScalarLibrary.spec stop ()
        (Cells.encode Finset.univ (finalValues instructions values)) after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,_full,executed,frame,observed⟩ := compile other vector inputs instructions accepted values native stop input
  have same := lowerCode?_source accepted
  rw [← same] at checked
  obtain ⟨registers,executedSource,agrees⟩ := source_exec_live instructions values initializedKeys out checked
  exact ⟨registers,after,by simpa only [same] using executedSource,agrees,executed,frame,observed⟩

def available : RegisterCode.Regs Word → Finset Nat := RegisterCodeLowering.available

def valuesOf : RegisterCode.Regs Word → Values := RegisterCodeLowering.valuesOf

def admit? (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word) (out : Finset Nat) :
    Option (List Instruction) := RegisterCodeLowering.admit? lower? inputs registers out

theorem admit?_checks {inputs : List SourceInstruction} {registers : RegisterCode.Regs Word}
    {out : Finset Nat} {instructions : List Instruction}
    (accepted : admit? inputs registers out = some instructions) :
    lowerCode? inputs = some instructions ∧
      RegisterProfile.initialCheck inputs (available registers) out = true :=
  RegisterCodeLowering.admit?_checks lower? accepted

theorem available_readback (registers : RegisterCode.Regs Word) (register : Nat)
    (present : register ∈ available registers) :
    registers register = some (valuesAt (valuesOf registers) register) :=
  RegisterCodeLowering.available_readback registers register present

theorem admitted_source_exec (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word)
    (out : Finset Nat) (instructions : List Instruction)
    (accepted : admit? inputs registers out = some instructions) :
    ∃ following,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      ∀ register ∈ out,
        following register = some (valuesAt (finalValues instructions (valuesOf registers)) register) :=
  RegisterCodeLowering.admitted_source_exec translation inputs registers out instructions accepted

theorem compile_admitted (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (inputs : List SourceInstruction) (registers : RegisterCode.Regs Word) (out : Finset Nat)
    (instructions : List Instruction) (accepted : admit? inputs registers out = some instructions)
    (native : State) (stop : Int)
    (input : X86BlockCompiler.At X86ScalarLibrary.spec stop
      (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions))
      (Cells.encode Finset.univ (valuesOf registers)) native) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ following after,
      RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) inputs registers = some (.next following) ∧
      (∀ register ∈ out,
        following register = some (valuesAt (finalValues instructions (valuesOf registers)) register)) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps X86ScalarLibrary.spec
        (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions)))).run native = .ok () after ∧
      X86StateFrame.Frame X86ScalarLibrary.spec.registerWrites X86ScalarLibrary.spec.byteWrites native after ∧
      X86BlockCompiler.Observed X86ScalarLibrary.spec stop ()
        (Cells.encode Finset.univ (finalValues instructions (valuesOf registers))) after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,_full,executed,frame,observed⟩ := compile other vector inputs instructions
    (admit?_checks accepted).1 (valuesOf registers) native stop input
  obtain ⟨following,executedSource,agrees⟩ := admitted_source_exec inputs registers out instructions accepted
  exact ⟨following,after,executedSource,agrees,executed,frame,observed⟩

namespace Controls

def aliasXor : SourceInstruction := .op 2 (.binary .bxor) [.reg 1,.reg 2]

theorem admission_controls :
    (lower? aliasXor).isSome = true ∧
    (lower? (.op 0 (.binary .bxor) [.reg 1,.reg 2])).isNone = true ∧
    (lower? (.op 12 (.binary .bxor) [.reg 1,.reg 2])).isNone = true ∧
    (lower? (.op 2 (.binary .bxor) [.reg 1,.reg 12])).isNone = true ∧
    (lower? (.op 2 (.binary .bxor) [.reg 1,.lit 2])).isNone = true ∧
    (lower? (.op 2 (.binary .sub) [.reg 1,.reg 2])).isNone = true := by decide

theorem live_input_controls :
    RegisterProfile.initialCheck [aliasXor] {1,2} {2} = true ∧
    RegisterProfile.initialCheck [aliasXor] {1} {2} = false := by decide

theorem missing_source_operand :
    RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) [aliasXor]
      (RegisterProfile.initializedOn {1} (fun _ => 7)) = none := by decide

theorem admission_reads_actual_registers :
    (admit? [aliasXor] (fun register =>
      if register = 1 then some 1 else if register = 2 then some 2 else none) {2}).isSome = true ∧
    admit? [aliasXor] (fun register => if register = 1 then some 1 else none) {2} = none := by decide

theorem alias_native_bytes :
    (lowerCode? [aliasXor]).map (fun instructions =>
      X86BlockCompiler.code X86ScalarLibrary.spec
        (LibraryLowering.expand X86LogicalRecipes.implementation (program instructions))) =
      some [0x48,0x31,0xf2] := by decide

theorem exact_alias_result :
    RegisterCode.exec RegisterProfile.semantics (fun _ _ => none) [aliasXor]
      (RegisterProfile.initialized (fun register => if register = 1 then 1 else if register = 2 then 2 else 0)) =
      some (.next (RegisterProfile.initialized (fun register =>
        if register = 2 then 3 else if register = 1 then 1 else 0))) := by
  simp only [RegisterCode.exec,aliasXor,RegisterCode.step,RegisterCode.readAll,RegisterCode.read,
    RegisterProfile.initialized,RegisterProfile.semantics,Scalar.evaluate,Binary.evaluate,
    Option.bind_some,Option.map_some,RegisterCode.andThen]
  congr 2
  funext register
  by_cases two : register = 2 <;> by_cases one : register = 1 <;>
    simp [Function.update,RegisterProfile.initialized,two,one]

end Controls

#print axioms lower?_source
#print axioms lower?_roundtrip
#print axioms lowerCode?_source
#print axioms lowerCode?_roundtrip
#print axioms valuesAt_update
#print axioms source_step
#print axioms source_exec
#print axioms program_wp
#print axioms source_exec_live
#print axioms compile
#print axioms compile_live
#print axioms admit?_checks
#print axioms available_readback
#print axioms admitted_source_exec
#print axioms compile_admitted
#print axioms Controls.admission_controls
#print axioms Controls.live_input_controls
#print axioms Controls.missing_source_operand
#print axioms Controls.admission_reads_actual_registers
#print axioms Controls.alias_native_bytes
#print axioms Controls.exact_alias_result
end Mettapedia.Machines.TIsa.X86RegisterCodeLogical
