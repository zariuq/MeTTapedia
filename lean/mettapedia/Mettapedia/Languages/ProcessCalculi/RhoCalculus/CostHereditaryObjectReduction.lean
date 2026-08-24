import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryReflectiveSupportTransport

/-!
# The rho cost layer object over its two node-local semantic obligations

Both open hypotheses of the rho cost layer object have proved reductions to
node-local semantic laws:

* **alignability** — `rhoCostOpenGeneratorTreeAlignable_of_staticClosures`
  reduces generator tree alignability to per-colour static pair closure over
  the recursive type domain, `CostCanonicalStaticPair.IsClosedIn.of_step`
  reduces that closure to one syntax-directed step via the generic symmetric
  well-founded elaborator, and
  `RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain_of_provider`
  reduces the step to the per-colour semantic-cut provider — a per-node case
  analysis whose recursion is injected through its strictly-smaller callback;

* **reflective support** — `rhoHereditaryReflectiveSupportPreserving_of`
  reduces the supported-executor preservation obligation to the local
  static-node law for the hereditary static kernel.

This module records the composed reductions, so the cost layer object assembles
from exactly two remaining semantic inputs, each about a single node:
`RhoCanonicalStaticPair.HasSemanticCut` for each static colour,
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
      RhoCanonicalStaticPair.HasSemanticCut color) :
    CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel :=
  rhoCostOpenGeneratorTreeAlignable_of_staticClosures (fun color =>
    CostCanonicalStaticPair.IsClosedIn.of_step
      (by exact List.mem_cons_self)
      (RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain_of_provider
        (provider color)))

/-- The rho cost layer object laws over the two node-local semantic obligations. -/
def rhoHereditaryCompactOpenNormalizerLaws_ofSemanticLaws
    (provider : ∀ color,
      RhoCanonicalStaticPair.HasSemanticCut color)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_of
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

/-- The normalizer-indexed rho cost layer domain object over the same two
node-local semantic obligations. -/
def rhoHereditaryCostLayer_ofSemanticLaws
    (provider : ∀ color,
      RhoCanonicalStaticPair.HasSemanticCut color)
    (staticPreserves :
      RhoCostStaticReflectiveSupportPreserving rhoHereditaryStaticNormalizer) :
    Cost.Layer :=
  rhoHereditaryCostLayer_of
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)
    (rhoHereditaryReflectiveSupportPreserving_of staticPreserves)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
