import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObjectReduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrencePathSupport

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- ROUTE CHECK: the BUILT provider alone yields the seal. -/
noncomputable def sealFromBuilt
    (built : ∀ color, RhoCanonicalStaticPairSemanticCutProviderInDomainBuilt color) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_of
    (rhoCostOpenGeneratorTreeAlignable_of_staticClosures (fun color =>
      CostCanonicalStaticPairClosedInDomain.of_step
        (by exact List.mem_cons_self)
        (RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain
          (RhoCanonicalStaticPairSemanticCutsInDomain.of_provider_built (built color)))))
    (rhoHereditaryReflectiveSupportPreserving_of
      rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path)

#print axioms sealFromBuilt
