import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Tools.KernelReflexivity

/-!
# Kernel checks of the actual exported native branch fields

All byte images come from the emitter's program manifest. The checks inspect
actual opcode/displacement bytes, wrapper bytes and span extents. No complete
native instruction semantics or generic emitter correctness is claimed here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace Mettapedia.Machines.TIsa.ImportedImages

open NativeImage

noncomputable def images : List Image := tisa_images% "../../../tcalc/tisa/manifests/tisa_x86_programs_v1.json"

noncomputable def hosting : List (Nat × List String × List String) :=
  tisa_hosting_inventory% "../../../tcalc/tisa/manifests/tisa_x86_programs_v1.json"

def carrierNames : List String := (List.range 10).map fun index => "R_TISA_EDGE_" ++ toString index
def controlNames : List String := (List.range 3).map fun index => "R_TISA_CTRL_" ++ toString index

def hostingCheck (entries : List (Nat × List String × List String)) : Bool :=
  entries.all fun entry => entry.2.1 == carrierNames && entry.2.2 == controlNames

theorem hosting_program_inventory : hosting.map Prod.fst = images.map Image.id := by kernel_reflexivity

theorem hosting_inventory_exact : hostingCheck hosting = true := by kernel_reflexivity

private def missingCarrier (entries : List (Nat × List String × List String)) :=
  match entries with
  | [] => []
  | (id, carriers, controls) :: later => (id, carriers.take 4, controls) :: later

theorem stale_four_carrier_inventory_rejected : hostingCheck (missingCarrier hosting) = false := by
  kernel_reflexivity

theorem image_count : images.length = 15 := by kernel_reflexivity

theorem program_inventory : images.map Image.id =
    [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 1, 1000, 1001] := by kernel_reflexivity

theorem byte_count : (images.map Image.size).sum = 46769 := by kernel_reflexivity

theorem branch_count : (images.map fun image => image.branches.length).sum = 2277 := by kernel_reflexivity

theorem all_layouts_checked : images.all Image.layoutCheck = true := by kernel_reflexivity

theorem all_branch_targets_exact (image : Image) (member : image ∈ images)
    (branch : Patch) (branchMember : branch ∈ image.branches) :
    ∃ bytes, readFour? image.view branch.fieldOffset = some bytes ∧
      RelativeBranch.decodedTarget branch.fieldOffset bytes = (branch.target : Int) :=
  image.branch_target_exact (List.all_eq_true.mp all_layouts_checked image member) branch branchMember

private def firstDisplacementCorrupted (values : List Image) : Bool :=
  match values with
  | [] => true
  | image :: _ => match image.branches with
    | [] => true
    | branch :: _ =>
        let changed : View := ⟨image.view.size, fun offset =>
          if offset = branch.fieldOffset then (image.view.read offset).map (· ^^^ 1)
          else image.view.read offset⟩
        image.layoutCheckOn changed

theorem altered_displacement_rejected : firstDisplacementCorrupted images = false := by kernel_reflexivity

#print axioms all_layouts_checked
#print axioms all_branch_targets_exact

end Mettapedia.Machines.TIsa.ImportedImages
