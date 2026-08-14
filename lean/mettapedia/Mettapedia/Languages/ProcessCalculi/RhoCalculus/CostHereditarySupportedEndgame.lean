import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportCrown
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportedIterationObstruction

/-!
# Provider-indexed rho Cost endgame

The finite-support hereditary Cost one object and its exact compact Cost two
obstruction share one remaining semantic input: the per-colour static-pair
cut provider.  This module records both consequences at that common waist.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open CostIterationObstruction

/-- The compact Cost two obstruction for the exact domain object selected by
the provider-indexed hereditary Cost one construction. -/
theorem rhoHereditaryCostOneDomainObject_not_compactCostNormalizationCoherent_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color) :
    ¬ CompactCostNormalizationCoherent
      (rhoHereditaryCostOneDomainObject_ofProvider provider
        ).compactOutput.toCIGSLT := by
  exact rhoHereditarySupportedCostOne_not_compactCostNormalizationCoherent
    (rhoHereditaryCostOneObjectLaws_ofProvider provider)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
