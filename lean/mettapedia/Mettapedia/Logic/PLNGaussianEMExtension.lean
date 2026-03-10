import Mettapedia.Logic.EvidenceWeightedNormalGamma
import Mettapedia.Logic.WeightedNormalGammaSurface
import Mettapedia.Logic.PLNGaussianEM

/-!
# Advanced Gaussian WM Extensions

Curated front door for the weighted Gaussian evidence / one-step E/M lane.

This module is intentionally *not* part of `PLNCore`. It packages the advanced
weighted and soft-assignment development separately:

- `EvidenceWeightedNormalGamma` gives the weighted sufficient-statistics carrier
- `WeightedNormalGammaSurface` connects that carrier to the generic WM layer
- `PLNGaussianEM` adds a finite one-step Gaussian-mixture E/M layer

Main entry points:

- `WeightedNormalGammaEvidence`
- `WeightedNormalGammaPrior`
- `GaussianMixtureState`
- `GaussianMStepResult`
- `SufficientStatisticSurface.weightedGaussianStatistic`
- `SufficientStatisticSurface.indicatorGaussianStatistic_aggregate_eq_ofDiscrete_filter`
- `SufficientStatisticSurface.indicatorGaussianStatistic_posterior_eq_gaussian_filter`
- `GaussianMixtureState.mStepPosterior_unit_eq_gaussian`

This is a real WM/PLN extension, not a full EM convergence development.

Existing source-labeled Gaussian demos such as widget-factory, steel-fault, and
gas-sensor classification fit this layer as hard-label M-step instances: their
per-class posteriors are exactly the indicator-responsibility reduction of the
weighted surface.
-/

namespace Mettapedia.Logic

abbrev WeightedNormalGammaEvidence :=
  Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence

abbrev WeightedNormalGammaPrior :=
  Mettapedia.Logic.EvidenceWeightedNormalGamma.NormalGammaPrior

abbrev GaussianMixtureState :=
  Mettapedia.Logic.PLNGaussianEM.GaussianMixtureState

abbrev GaussianMStepResult :=
  Mettapedia.Logic.PLNGaussianEM.GaussianMixtureState.MStepResult

abbrev hardLabelWeightedAggregate_eq_gaussianFilter :=
  @Mettapedia.Logic.SufficientStatisticSurface.indicatorGaussianStatistic_aggregate_eq_ofDiscrete_filter

abbrev hardLabelWeightedPosterior_eq_gaussianFilter :=
  @Mettapedia.Logic.SufficientStatisticSurface.indicatorGaussianStatistic_posterior_eq_gaussian_filter

abbrev gaussianEM_unit_mStep_eq_gaussian :=
  @Mettapedia.Logic.PLNGaussianEM.GaussianMixtureState.mStepPosterior_unit_eq_gaussian

end Mettapedia.Logic
