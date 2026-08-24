import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrencePathSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObjectReduction

/-!
# Reflective-support closure for rho

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

With this theorem, the rho cost layer assembles from generator-tree
alignability alone — equivalently, from the per-colour semantic-cut provider
alone.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The support closure: the finite-support hereditary executor preserves every
caller-relative reflective support. -/
theorem rhoHereditaryReflectiveSupportPreserving :
    RhoHereditaryReflectiveSupportPreserving :=
  rhoHereditaryReflectiveSupportPreserving_of
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- The rho cost layer object laws from generator tree alignability alone. -/
def rhoHereditaryCompactOpenNormalizerLaws_ofAlignable
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_of alignable
    rhoHereditaryReflectiveSupportPreserving

/-- The normalizer-indexed rho cost layer domain object from alignability alone. -/
def rhoHereditaryCostLayer_ofAlignable
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel) :
    Cost.Layer :=
  rhoHereditaryCostLayer_of alignable
    rhoHereditaryReflectiveSupportPreserving

/-- The rho cost layer object laws from the per-colour semantic-cut provider
alone — the single remaining open obligation of the cost layer chain. -/
def rhoHereditaryCompactOpenNormalizerLaws_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPair.HasSemanticCut color) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_ofAlignable
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)

/-- The normalizer-indexed rho cost layer domain object from the per-colour
semantic-cut provider alone. -/
def rhoHereditaryCostLayer_ofProvider
    (provider : ∀ color,
      RhoCanonicalStaticPair.HasSemanticCut color) :
    Cost.Layer :=
  rhoHereditaryCostLayer_ofAlignable
    (rhoCostOpenGeneratorTreeAlignable_of_provider provider)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
