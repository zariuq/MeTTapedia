import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedAdmission
import Mettapedia.Languages.OCaml.Examples

/-! Executable preparation checks for the six standard O0 programs and
four semantic controls. Universal prepared-program admission is proved
separately; native whole-program results and costs need their own gates.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.PreparedAdmissionControls

open Mettapedia.Languages

#guard (prepare OCaml.Examples.recursion).toOption.isSome
#guard (prepare OCaml.Examples.lists).toOption.isSome
#guard (prepare OCaml.Examples.mutualRecursion).toOption.isSome
#guard (prepare OCaml.Examples.variants).toOption.isSome
#guard (prepare OCaml.Examples.closures).toOption.isSome
#guard (prepare OCaml.Examples.sorting).toOption.isSome
#guard (prepare OCaml.Examples.priority).toOption.isSome
#guard (prepare OCaml.Examples.matchFailure).toOption.isSome
#guard (prepare OCaml.Examples.rightToLeftFault).toOption.isSome
#guard (prepare OCaml.Examples.shortCircuit).toOption.isSome

theorem free_entry_refused : (prepare ({code := #[.variable 0], entry := 0} : OCaml.Program)).toOption = none := by cbv
theorem missing_entry_refused : (prepare ({code := #[], entry := 0} : OCaml.Program)).toOption = none := by cbv

#print axioms free_entry_refused
#print axioms missing_entry_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.PreparedAdmissionControls
