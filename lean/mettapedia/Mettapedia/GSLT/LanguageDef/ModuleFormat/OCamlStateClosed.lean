import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodedShapes

/-! Successfully encoded source states have no free pattern metavariables.
This follows from their declaration-derived typing in the empty free context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem state?_closed (pool : List OCaml.MatchPattern) (state : OCaml.MachineState) (encoded : Pattern)
    (found : state? pool state = some encoded) : encoded.freeFvarNames = [] := by
  have typed := state?_open baseLanguage rfl FreeTypeContext.empty [] pool state encoded found
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨type, impossible⟩ := typed.1.freeType_of_mem_freeFvarNames_of_isObjectPattern typed.2.2.1 present
  cases impossible

#print axioms state?_closed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
