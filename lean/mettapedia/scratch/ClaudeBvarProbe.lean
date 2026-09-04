import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **The one-endpoint restore-to-payload-normal equality fails at nonempty
availability: the parent thinning shifts an ambient bvar while the payload's
own normal keeps it.**  Core computation of the refutation. -/
theorem thicken_shifts_bvar_under_nonempty_bound :
    (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base
        [.base (costBaseSortName "Name")]).thickenAmbientBVars 0 (.bvar 0) ≠
      .bvar 0 := by
  simp [CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticBinderThinning.embedIndexAt,
    CostStaticBinderThinning.ofTargetThinning]

/-- Control: under the empty bound the thinning is the identity on the bvar —
which is exactly why the Quote-root (support-reset) version is true. -/
theorem thicken_id_bvar_under_nil_bound :
    (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base
        []).thickenAmbientBVars 0 (.bvar 0) = .bvar 0 := by
  simp [CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticBinderThinning.embedIndexAt,
    CostStaticBinderThinning.ofTargetThinning]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
