import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply
import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-! # Scope allocation realizes the existing ordered alpha-variant judgment -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

theorem fresh_variant (state : Supply) (signature : Atom) :
    TypeCandidateAlphaVariantRel state.used signature (fresh state signature).1 :=
  EquationFreshening.instantiateTypeSignature_variant state.next signature (fun _ member => member)

theorem freshList_variants (state : Supply) (signatures : List Atom) :
    ArgumentAlphaVariantsRel state.used signatures (freshList state signatures).1 := by
  rw [freshList_existing]
  exact EquationFreshening.instantiateTypeSignatures_variants state.next signatures (fun _ member => member)

theorem later_list_avoids_earlier (state : Supply) (first second : List Atom) (name : String)
    (earlier : name ∈ atomListVariables (freshList state first).1) :
    name ∉ atomListVariables (freshList (freshList state first).2 second).1 := by
  intro later
  exact freshList_avoids _ _ _ later (freshList_output_remembers state first earlier)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupply
