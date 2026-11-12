import Mettapedia.Machines.TIsa.P1JsonImport
import Mettapedia.Machines.TIsa.ImportedTheory
import Mettapedia.Tools.KernelReflexivity

/-!
# Kernel checks of the current p1 source/image boundary

The current p1-v2 bundle supplies every source constructor, region and entry
field alongside its raw image. These checks preserve that association and the
span-to-source paths. They do not assert C printer correctness, semantic
admission, source specialization correctness or complete native execution.
The old p0 bundle and its branch certificates remain distinct.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.ImportedP1

open P1Capture P1Source

noncomputable def captured : Bundle :=
  tisa_p1_bundle% "../../../tcalc/tisa/manifests/tisa_x86_p1_programs_v2.json"

noncomputable def programs : List P1Capture.Program := captured.programs

theorem abi_boundary_checked : captured.boundary.check = true := by kernel_reflexivity

theorem exact_count : captured.declaredCount = 15 ∧ programs.length = 15 := by
  constructor <;> kernel_reflexivity

theorem export_ids : programs.map P1Capture.Program.id = List.range 15 := by kernel_reflexivity

/-- Source rule names associate the eleven premise rows; export positions are not rule IDs. -/
theorem premise_name_inventory :
    (programs.take 11).map P1Capture.Program.name =
      (ImportedTheory.entries.filter fun entry => entry.role == .premise).map TheoryData.Entry.name := by
  kernel_reflexivity

theorem all_source_fields_checked : programs.all P1Capture.Program.sourceCheck = true := by kernel_reflexivity

theorem all_image_layouts_checked : programs.all P1Capture.Program.imageCheck = true := by kernel_reflexivity

theorem exact_byte_count : (programs.map P1Capture.Program.size).sum = 19373 := by kernel_reflexivity

theorem all_source_spellings_exact (program : P1Capture.Program) (member : program ∈ programs) :
    P1Source.encodeProgram program.source = some program.printed :=
  program.printed_exact (List.all_eq_true.mp all_source_fields_checked program member)

theorem all_cost_fields_exact (program : P1Capture.Program) (member : program ∈ programs) :
    program.source.body.fundPoints = program.fundPoints ∧
      program.source.body.reportedBound = program.maximumReceipt ∧
      program.source.body.boundFits = program.maximumFits :=
  program.cost_exact (List.all_eq_true.mp all_source_fields_checked program member)

private def wrongCondition (values : List P1Capture.Program) : Bool :=
  match values with
  | [] => true
  | program :: _ => match program.source.body with
    | .seq first (.branch condition yes no) =>
        let source := { program.source with body := .seq first (.branch (condition + 1) yes no) }
        ({ program with source := source } : P1Capture.Program).sourceCheck
    | _ => true

theorem changed_condition_rejected : wrongCondition programs = false := by kernel_reflexivity

private def wrongRegion (values : List P1Capture.Program) : Bool :=
  match values with
  | [] => true
  | program :: _ => match program.regions with
    | [] => true
    | region :: later =>
        ({ program with regions := { region with minimum := region.minimum + 1 } :: later } :
          P1Capture.Program).sourceCheck

theorem changed_region_rejected : wrongRegion programs = false := by kernel_reflexivity

private def wrongCost (values : List P1Capture.Program) : Bool :=
  match values with
  | [] => true
  | program :: _ => ({ program with maximumReceipt := program.maximumReceipt + 1 } :
      P1Capture.Program).sourceCheck

theorem changed_cost_rejected : wrongCost programs = false := by kernel_reflexivity

private def wrongPath (values : List P1Capture.Program) : Bool :=
  match values with
  | [] => true
  | program :: _ => match program.spans with
    | first :: second :: later =>
        ({ program with spans := first :: { second with path := some [1] } :: later } :
          P1Capture.Program).imageCheck
    | _ => true

theorem changed_path_rejected : wrongPath programs = false := by kernel_reflexivity

private def wrongWrapper (values : List P1Capture.Program) : Bool :=
  match values with
  | [] => true
  | program :: _ =>
      let view : NativeImage.View := ⟨program.size, fun offset =>
        if offset = 0 then some 0x90 else program.view.read offset⟩
      program.imageCheckOn view

theorem changed_wrapper_byte_rejected : wrongWrapper programs = false := by kernel_reflexivity

theorem changed_abi_map_rejected :
    ({ captured.boundary with registers := ["rax", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11", "rdi", "rbx", "r12", "r13"] } :
      Boundary).check = false := by kernel_reflexivity

#print axioms all_source_fields_checked
#print axioms all_image_layouts_checked
#print axioms premise_name_inventory
#print axioms all_source_spellings_exact
#print axioms all_cost_fields_exact

end Mettapedia.Machines.TIsa.ImportedP1
