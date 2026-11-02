import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! The authored vocabulary and structural transitions of the indexed OCaml
machine. Code dispatch and pattern requests are installed by the program
compiler. Primitive queries retain their explicit provider interface. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace OCamlMachineAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_tree "../../../../../../metta/gslt/module/OCamlMachine.module" as Machine
#module_roundtrip OCamlIR
#module_roundtrip OCamlMachine
end OCamlMachineAuthoring

namespace OCamlCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def baseLanguage? : Option LanguageDef := OCamlMachineAuthoring.Machine.language.toOption
def baseLanguage : LanguageDef := module_language_view% baseLanguage?
theorem baseLanguage_exact : baseLanguage? = some baseLanguage := by decide +kernel

#guard baseLanguage.validate.isEmpty
#guard baseLanguage.rewrites.length == 27
#guard baseLanguage.equations.isEmpty

#print axioms baseLanguage_exact

end OCamlCompilation
end Mettapedia.GSLT.LanguageDef.ModuleFormat
