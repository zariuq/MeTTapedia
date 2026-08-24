import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportedIterationObstruction

/-!
# Provider-indexed rho Cost endgame

The finite-support hereditary cost layer and its exact compact iteration
obstruction share one remaining semantic input: the per-colour static-pair
cut provider.  This module records both consequences at that common waist.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open CostIterationObstruction

/-- The compact-iteration obstruction for the exact domain object selected by
the provider-indexed hereditary cost layer construction. -/
theorem rhoHereditaryCostLayer_not_compactCostNormalizationCoherent_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPair.HasSemanticCut color) :
    ¬ CompactCostNormalizationCoherent
      (rhoHereditaryCostLayer_ofProvider provider
        ).compactOutput.toCIGSLT := by
  exact rhoHereditarySupportedCostLayer_not_compactCostNormalizationCoherent
    (rhoHereditaryCompactOpenNormalizerLaws_ofProvider provider)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
