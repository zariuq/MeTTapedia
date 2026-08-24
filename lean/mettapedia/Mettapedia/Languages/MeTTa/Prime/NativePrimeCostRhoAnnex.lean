import Mettapedia.Languages.MeTTa.Prime.NativePrimeCostInterface
import Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary

/-!
# The reflective-rho Cost annex for Prime

This import gate supplies Prime's abstract Cost interface with the
unconditional reflective-rho cost layer domain object and its selected cost-layer iteration
cache/replay boundary.  It is intentionally separate from the
language-independent interface so Prime and dependent type theory can develop
against Cost contracts without importing a concrete language provider.
-/

#check Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostLayer
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostLayer
