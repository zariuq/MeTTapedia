import Mettapedia.CategoryTheory.DeFinettiExports

/-! # De Finetti Smoke Test
Type-checks that headline aliases and key API theorems resolve correctly. -/

namespace Mettapedia.CategoryTheory

-- Headline aliases
#check @deFinetti_kleisliGiry
#check @deFinetti_measure

-- Negative results
#check @deFinettiExport_not_allSourcesKleisli_unrestricted
#check @deFinettiExport_not_commutesToMarkovBridge_unrestricted
#check @deFinettiExport_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening

-- Finite-mass equivalence
#check @deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly

-- Cone-level API
#check @deFinettiExport_globalIIDConeMediatorUnique_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
#check @deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_finiteMass

-- Solomonoff bridge
#check @deFinettiExport_restrictedSolomonoff_prefixLaw_implies_unique_latentThetaMediator

-- Categorical ↔ PLN bridge
#check @deFinettiExport_categorical_pln_sufficiency
#check @deFinettiExport_categoricalProductPMF_fin2_eq_bernoulliProductPMF

end Mettapedia.CategoryTheory
