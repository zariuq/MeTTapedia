import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! Compositional source-independent CHR program data. Ground data and
resource transactions are shared with `CHRGroundKernel`; no Prolog grammar
is imported into the IR. Indices and arities have a nonnegative admission
condition when decoded into the source calculus. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace CHRProgramAuthoring
#module_tree "../../../../../../metta/gslt/module/CHRProgram.module" as Program
end CHRProgramAuthoring

namespace CHRProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := CHRProgramAuthoring.Program.language.toOption
def language : LanguageDef := module_language_view% language?

theorem language_exact : language? = some language := by decide +kernel

#guard language.validate.isEmpty
#guard language.terms.any (fun declaration => declaration.label == "ChrProgram")
#guard language.terms.any (fun declaration => declaration.label == "ChrRule")

end CHRProgram
end Mettapedia.GSLT.LanguageDef.ModuleFormat
