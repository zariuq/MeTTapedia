import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! Authored structural transitions for the indexed Erlang machine. Program
dispatch and positive pattern rules are installed by the arena compiler.
Primitive, guard and exhausted-pattern services have declared query ports;
their source/native correspondence is a separate qualification obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace ErlangSequentialAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_tree "../../../../../../metta/gslt/module/ErlangSequentialMachine.module" as Machine
#module_roundtrip ErlangSequentialIR
#module_roundtrip ErlangSequentialMachine
end ErlangSequentialAuthoring

namespace ErlangCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def baseLanguage? : Option LanguageDef := ErlangSequentialAuthoring.Machine.language.toOption
def baseLanguage : LanguageDef := module_language_view% baseLanguage?
theorem baseLanguage_exact : baseLanguage? = some baseLanguage := by decide +kernel

#guard baseLanguage.validate.isEmpty
#guard baseLanguage.equations.isEmpty
#guard baseLanguage.rewrites.length == 52

end ErlangCompilation
end Mettapedia.GSLT.LanguageDef.ModuleFormat
