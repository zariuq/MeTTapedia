import Mettapedia.Languages.MeTTa.Prime.NativePrimeCostInterfaceCrown
import Mettapedia.Languages.MeTTa.Prime.CostTwoSelectedDisplayedBoundary

/-!
# The reflective-rho Cost annex for Prime

This import gate supplies Prime's abstract Cost interface with the
unconditional reflective-rho Cost₁ domain object and its selected Cost²
cache/replay boundary.  It is intentionally separate from the
language-independent interface so Prime and dependent type theory can develop
against Cost contracts without importing a concrete language provider.
-/

#check Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostOneDomainObject
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostOneDomainObject
