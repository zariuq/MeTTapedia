import Mettapedia.Machines.TIsa.JsonImport

/-!
# The actual native manifest's layout and register boundary

The importer quotes ordinary data; the kernel checks its concrete properties.
These theorems concern exported structure. Wrapper instruction semantics and
the correspondence to a running native leaf remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.ImportedBoundary

def actual : NativeBoundary :=
  tisa_boundary% "../../../tcalc/tisa/manifests/lean_tcalc_theory_v1.json"

theorem checked : actual.check = true := by decide

theorem actual_layouts_admitted : actual.frame.admitted ∧ actual.tuple.admitted :=
  actual.layouts_admitted checked

theorem x86_mapping : actual.x86 = Registers.canonical .x86_64 := by decide
theorem aarch64_mapping : actual.aarch64 = Registers.canonical .aarch64 := by decide
theorem rv64_mapping : actual.rv64 = Registers.canonical .rv64 := by decide

theorem x86_injective : Function.Injective actual.x86.resolve := by
  rw [x86_mapping]
  exact (Registers.canonical .x86_64).resolve_injective .x86_64
    (Registers.canonical_admitted .x86_64)

theorem wrapper_entry_image : actual.wrapperEntry =
    [83, 65, 84, 65, 85, 65, 86, 65, 87] := by decide

theorem wrapper_exit_image : actual.wrapperExit =
    [65, 95, 65, 94, 65, 93, 65, 92, 91, 195] := by decide

namespace Controls

example : ({ actual with frame := { actual.frame with size := 184 } }).check = false := by decide

example : ({ actual with x86 := { actual.x86 with wrapperSaved := [3, 12, 13] } }).check = false := by decide

end Controls

#print axioms checked
#print axioms actual_layouts_admitted
#print axioms x86_injective

end Mettapedia.Machines.TIsa.ImportedBoundary
