import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.Languages.ProcessCalculi.RhoCalculus

-- The seal consumer: what does the chain rest on, apart from the provider?
#print axioms rhoHereditaryCostOneDomainObject_ofBuiltProvider
#print axioms rhoHereditaryCostOneObjectLaws_ofBuiltProvider
-- and the two structural exclusions
#print axioms CostHereditaryExposureClosure.no_structural_apply_at_rhoName
#print axioms CostHereditaryExposureClosure.no_structural_partner_of_emptyParallel
