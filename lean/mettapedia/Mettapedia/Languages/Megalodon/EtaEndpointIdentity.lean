import Mettapedia.Languages.Megalodon.EndpointIdentity
import Mettapedia.Languages.Megalodon.EtaConversionKernel

/-!
# Megalodon eta conversion versus endpoint identity

Eta conversion is semantic evidence relating two structurally different
terms.  NIK must check that evidence without redefining endpoint identity as
conversion equivalence.  This module records both facts for the exact
Megalodon eta document.
-/

namespace Mettapedia.Languages.Megalodon.EtaEndpointIdentity

open Mettapedia.Languages.Megalodon

/-- The function and its eta expansion remain different exact endpoints. -/
theorem eta_expansion_is_not_endpoint_identity :
    EndpointIdentity.termIdentity.identify
        EtaConversionKernel.etaExpansion ≠
      EndpointIdentity.termIdentity.identify
        EtaConversionKernel.etaFunctionTerm := by
  intro sameIdentity
  have sameTerm :=
    EndpointIdentity.termIdentity.identify_injective sameIdentity
  exact (by decide :
    EtaConversionKernel.etaExpansion ≠
      EtaConversionKernel.etaFunctionTerm) sameTerm

/-- The declared and synthesized propositions in the real eta specimen are
also structurally different endpoints. -/
theorem eta_propositions_are_structurally_distinct :
    EndpointIdentity.termIdentity.identify
        EtaConversionKernel.etaDeclaredProposition ≠
      EndpointIdentity.termIdentity.identify
        EtaConversionKernel.etaSynthesizedProposition := by
  intro sameIdentity
  have sameTerm :=
    EndpointIdentity.termIdentity.identify_injective sameIdentity
  exact (by decide :
    EtaConversionKernel.etaDeclaredProposition ≠
      EtaConversionKernel.etaSynthesizedProposition) sameTerm

/-- The coGSLT checker accepts the eta-conversion article while exact
endpoint identity continues to distinguish the related propositions. -/
theorem eta_article_acceptance_preserves_intensional_identity :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        EtaConversionKernel.validated EtaConversionKernel.etaDocumentGoal
          EtaConversionKernel.etaDocumentArticle = true ∧
      EndpointIdentity.termIdentity.identify
          EtaConversionKernel.etaDeclaredProposition ≠
        EndpointIdentity.termIdentity.identify
          EtaConversionKernel.etaSynthesizedProposition := by
  exact ⟨EtaConversionKernel.eta_document_article_accepted,
    eta_propositions_are_structurally_distinct⟩

end Mettapedia.Languages.Megalodon.EtaEndpointIdentity
