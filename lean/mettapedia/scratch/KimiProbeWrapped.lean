import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem kimi_probe_drop_mem_wrappedConstructors :
    (⟨rhoCalc.terms[1], by
        change rhoCalc.terms[1] ∈ rhoCalc.terms
        exact List.getElem_mem (by simp [rhoCalc])⟩ :
      AuthoredConstructor rhoIGSLT.presentation.presentation) ∈
      rhoContinuationRetyping.wrappedConstructors := by
  rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
  constructor <;> decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
