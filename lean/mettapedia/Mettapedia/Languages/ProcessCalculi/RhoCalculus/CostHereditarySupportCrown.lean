import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrencePathSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObjectReduction

/-!
# The rho reflective-support crown, closed

The finite-support hereditary executor preserves every caller-relative
reflective support.  The proof composes three finished layers:

* the local static-node law
  (`rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path`), proved by
  path-indexed binder-free substitution over the canonical target frame with
  per-occurrence ancestry certificates;
* the structural whole-tree theorem and compact-executor endpoint
  (`rhoCostNormalizeOpenWithStatic_preservesReflectiveSupport`);
* the supported-executor context transport
  (`rhoHereditaryReflectiveSupportPreserving_of`).

With this crown closed, the rho Cost₁ object assembles from generator tree
alignability alone — equivalently, from the per-colour semantic-cut provider
alone.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The support crown: the finite-support hereditary executor preserves every
caller-relative reflective support. -/
theorem rhoHereditaryReflectiveSupportPreserving :
    RhoHereditaryReflectiveSupportPreserving :=
  rhoHereditaryReflectiveSupportPreserving_of
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- The rho Cost₁ object laws from generator tree alignability alone. -/
def rhoHereditaryCostOneObjectLaws_ofAlignable
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel) :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneObjectLaws_of alignable
    rhoHereditaryReflectiveSupportPreserving

/-- The normalizer-indexed rho Cost₁ domain object from alignability alone. -/
def rhoHereditaryCostOneDomainObject_ofAlignable
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_of alignable
    rhoHereditaryReflectiveSupportPreserving

/-- The rho Cost₁ object laws from the per-colour semantic-cut provider
alone — the single remaining open obligation of the Cost₁ chain. -/
def rhoHereditaryCostOneObjectLaws_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color) :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneObjectLaws_ofAlignable
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)

/-- The normalizer-indexed rho Cost₁ domain object from the per-colour
semantic-cut provider alone. -/
def rhoHereditaryCostOneDomainObject_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPairSemanticCutProviderInDomain color) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_ofAlignable
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
