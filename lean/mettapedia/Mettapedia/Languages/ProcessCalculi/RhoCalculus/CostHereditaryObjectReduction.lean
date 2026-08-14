import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryReflectiveSupportTransport

/-!
# The rho Cost₁ object over its two node-local semantic obligations

Both open hypotheses of the rho Cost₁ object admit proved reductions to
node-local semantic laws:

* **alignability** — `rhoCostOpenGeneratorTreeAlignable_of_staticClosures`
  reduces generator tree alignability to per-colour static pair closure over
  the recursive type domain, `CostCanonicalStaticPairClosedInDomain.of_step`
  reduces that closure to one syntax-directed step via the generic symmetric
  well-founded elaborator, and
  `RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain_of_provider`
  reduces the step to the per-colour semantic-cut provider — a per-node case
  analysis whose recursion is injected through its strictly-smaller callback;

* **reflective support** — `rhoHereditaryReflectiveSupportPreserving_of`
  reduces the supported-executor preservation obligation to the local
  static-node law for the hereditary static kernel.

This module records the composed reductions, so the Cost₁ object assembles
from exactly two remaining semantic inputs, each about a single node:
`RhoCanonicalStaticPairSemanticCutProviderInDomain` for each static colour,
and `RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer`.
No executor, region-tree, or coeffect-boundary reasoning remains in either
obligation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Generator tree alignability for the hereditary kernel follows from the
per-colour semantic-cut provider alone.  The elaboration recursion, the
static-step interface, and the domain closure are all discharged by proved
generic theorems. -/
theorem rhoCostOpenGeneratorTreeAlignable_of_provider
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color) :
    CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel :=
  rhoCostOpenGeneratorTreeAlignable_of_staticClosures (fun color =>
    CostCanonicalStaticPairClosedInDomain.of_step
      (by exact List.mem_cons_self)
      (RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain_of_provider
        (provider color)))

/-- The rho Cost₁ object laws over the two node-local semantic obligations. -/
def rhoHereditaryCostOneObjectLaws_ofSemanticLaws
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneObjectLaws_of
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

/-- The normalizer-indexed rho Cost₁ domain object over the same two
node-local semantic obligations. -/
def rhoHereditaryCostOneDomainObject_ofSemanticLaws
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_of
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
