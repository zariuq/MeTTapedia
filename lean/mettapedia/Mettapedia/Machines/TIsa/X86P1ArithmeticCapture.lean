import Mettapedia.Machines.TIsa.X86P1Arithmetic
import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Tools.KernelReflexivity

/-!
# Actual p1 ADD/SUB output across the admitted finite operand domain

The exporter calls the original p1 instruction emitter for both operations,
all three supported tags and every non-frame destination/source tuple. The
captured output is checked against the independently proved native templates.
This is finite byte conformance, not whole C compiler or host correctness.
-/

set_option autoImplicit false
set_option Elab.async false
namespace Mettapedia.Machines.TIsa.X86P1ArithmeticCapture
open _root_.X86Registers X86RegisterRefinement

noncomputable def captured : List Nat × List NativeImage.TemplateSample :=
  tisa_template_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/P1ArithmeticHelper.json"

def tag (kind : Fin 3) : P1Source.TypeTag :=
  if kind.val = 0 then .u64 else if kind.val = 1 then .u32z else .i32s

theorem tag_supported : ∀ kind : Fin 3, X86P1Arithmetic.Supported (tag kind) := by decide

def operation (kind : Fin 2) : X86Arithmetic.DefinedOperation := if kind.val = 0 then .add else .sub

def build (kind : Fin 3) (op : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0) :
    X86P1Arithmetic.Instruction :=
  ⟨⟨operation op,destination,left,right,unlocked⟩,tag kind,tag_supported kind⟩

def decode? : List Nat → Option X86P1Arithmetic.Instruction
  | [kind,op,destination,left,right] =>
      if valid : kind < 3 ∧ op < 2 ∧ destination < 12 ∧ left < 12 ∧ right < 12 ∧ destination ≠ 0 then
        some (build ⟨kind,valid.1⟩ ⟨op,valid.2.1⟩ ⟨destination,valid.2.2.1⟩
          ⟨left,valid.2.2.2.1⟩ ⟨right,valid.2.2.2.2.1⟩
          (by intro zero; exact valid.2.2.2.2.2 (congrArg Fin.val zero)))
      else none
  | _ => none

def scratchMask (instruction : X86P1Arithmetic.Instruction) : Nat :=
  if instruction.core.operation = .sub ∧ instruction.core.destination = instruction.core.right ∧
      instruction.core.destination ≠ instruction.core.left then 1 else 0

def sampleCheck (sample : NativeImage.TemplateSample) : Bool :=
  match decode? sample.inputs with
  | none => false
  | some instruction =>
      sample.bytes.all (fun byte => decide (byte < 256)) &&
      (NativeImage.spanEnd? 0 sample.spans == some sample.bytes.length) &&
      (sample.spans.map NativeImage.Span.kind == ["BIN"]) &&
      (sample.scratchMask == scratchMask instruction) &&
      (sample.body "BIN" == some (X86P1Arithmetic.bytes instruction))

def inventory : List (List Nat) :=
  (List.range 3).flatMap fun kind =>
    (List.range 2).flatMap fun op =>
      (List.range 11).flatMap fun position =>
        (List.range 12).flatMap fun left =>
          (List.range 12).map fun right => [kind,op,position+1,left,right]

theorem register_map_exact : captured.1 = (Registers.canonical .x86_64).registers := by kernel_reflexivity

theorem row_count : captured.2.length = 9504 := by kernel_reflexivity

theorem row_inventory : captured.2.map NativeImage.TemplateSample.inputs = inventory := by
  have checked : (captured.2.map NativeImage.TemplateSample.inputs == inventory) = true := by kernel_reflexivity
  exact beq_iff_eq.mp checked

theorem every_sample_checked : captured.2.all sampleCheck = true := by kernel_reflexivity

theorem decode_build (kind : Fin 3) (op : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0) :
    decode? [kind.val,op.val,destination.val,left.val,right.val] = some (build kind op destination left right unlocked) := by
  have nonzero : destination.val ≠ 0 := by
    intro zero
    exact unlocked (Fin.ext zero)
  have valid : kind.val < 3 ∧ op.val < 2 ∧ destination.val < 12 ∧
      left.val < 12 ∧ right.val < 12 ∧ destination.val ≠ 0 :=
    ⟨kind.isLt,op.isLt,destination.isLt,left.isLt,right.isLt,nonzero⟩
  rw [decode?,dif_pos valid]

theorem sample_present (kind : Fin 3) (op : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0) :
    ∃ sample ∈ captured.2, sample.inputs = [kind.val,op.val,destination.val,left.val,right.val] := by
  have positive : 0 < destination.val := by
    have nonzero : destination.val ≠ 0 := by intro zero;exact unlocked (Fin.ext zero)
    omega
  have included : [kind.val,op.val,destination.val,left.val,right.val] ∈ inventory := by
    simp only [inventory,List.mem_flatMap,List.mem_map,List.mem_range]
    refine ⟨kind.val,kind.isLt,op.val,op.isLt,destination.val-1,?_,left.val,left.isLt,right.val,right.isLt,?_⟩
    · have := destination.isLt;omega
    · simp only [Nat.sub_add_cancel (by omega : 1 ≤ destination.val)]
  rw [←row_inventory] at included
  exact List.mem_map.mp included

theorem checked_body (sample : NativeImage.TemplateSample) (member : sample ∈ captured.2) :
    ∃ instruction, decode? sample.inputs = some instruction ∧ sample.body "BIN" = some (X86P1Arithmetic.bytes instruction) := by
  have checked := List.all_eq_true.mp every_sample_checked sample member
  cases decoded : decode? sample.inputs with
  | none => simp [sampleCheck,decoded] at checked
  | some instruction =>
    refine ⟨instruction,rfl,?_⟩
    simp only [sampleCheck,decoded,Bool.and_eq_true,beq_iff_eq] at checked
    tauto

theorem emitted_body (kind : Fin 3) (op : Fin 2) (destination left right : Fin 12) (unlocked : destination ≠ 0) :
    ∃ sample ∈ captured.2,
      sample.inputs = [kind.val,op.val,destination.val,left.val,right.val] ∧
      sample.body "BIN" = some (X86P1Arithmetic.bytes (build kind op destination left right unlocked)) := by
  obtain ⟨sample,member,inputs⟩ := sample_present kind op destination left right unlocked
  obtain ⟨instruction,decoded,body⟩ := checked_body sample member
  rw [inputs,decode_build kind op destination left right unlocked] at decoded
  have same : instruction = build kind op destination left right unlocked := Option.some.inj decoded.symm
  exact ⟨sample,member,inputs,same ▸ body⟩

private def first : NativeImage.TemplateSample :=
  ⟨[0,0,1,0,0],[0x48,0x89,0xfe,0x48,0x01,0xfe],[⟨0,6,"BIN"⟩],0⟩

theorem first_sample_exact : captured.2.head? = some first := by kernel_reflexivity

theorem opcode_mutation_refused :
    sampleCheck { first with bytes := [0x48,0x89,0xfe,0x48,0x29,0xfe] } = false := by kernel_reflexivity

theorem sign_extension_mutation_refused : sampleCheck
    ⟨[2,0,1,1,2],[0x48,0x01,0xd6,0x48,0x89,0xf6],[⟨0,6,"BIN"⟩],0⟩ = false := by kernel_reflexivity

#print axioms emitted_body
#print axioms opcode_mutation_refused
#print axioms sign_extension_mutation_refused
#print axioms register_map_exact
#print axioms row_inventory
#print axioms every_sample_checked
end Mettapedia.Machines.TIsa.X86P1ArithmeticCapture
