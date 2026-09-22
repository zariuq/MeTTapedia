import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateCostInterface
import Mettapedia.Languages.MeTTa.PrimeCandidates.SelectedCostLayerIterationBoundary

/-!
# The reflective-rho Cost annex for candidate

This import gate supplies candidate's abstract Cost interface with the
unconditional reflective-rho cost layer domain object and its selected cost-layer iteration
cache/replay boundary.  It is intentionally separate from the
language-independent interface so candidate and dependent type theory can develop
against Cost contracts without importing a concrete language provider.
-/

#check Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostLayer
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostLayer
