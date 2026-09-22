import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedCoherentConnection
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataOSLFConnection

/-!
# A proof-qualified mathematical connection with presented operations

The connected HOL/DTT/HOTG construction and the mixed native operational
presentation meet here.  The mathematical side retains the source proof,
dependent consumer, trace interpretation, semantic quotient, and generated
map-fusion observation.  The operational side is no longer an abstract step
relation: it is the GSLT and OSLF mechanically generated from executable
`LanguageDef` rules.

The connection deliberately keeps universe-head equality at a separate
semantic interface.  The finite rule presentation is exact for computation;
it is neither asked nor allowed to masquerade as an enumeration of semantic
universe equality.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedPresentedConnection

universe u

/-- The current integrated boundary: a nontrivial mathematical inhabitant,
an equation-respecting semantic quotient, and an exact presentation-derived
operational interface with its universe-equality limit retained. -/
structure PresentedConnection : Prop where
  coherent : HOLLeibnizNativeQualifiedCoherentConnection.CoherentConnection.{u}
  equationFree : HOLNativeMixedRuleData.language.isEquationFree = true
  operationalStep : ∀ {n : Nat} (source target : Presentation.Tower.Tm n),
    HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
        (HOLNativeMixedRuleData.compute (HOLNativeMixedRuleData.encoded source))
        (HOLNativeMixedRuleData.encoded target) ↔
      HOLNativeMixedOperationalDecomposition.ComputationalStep source target
  generatedNativeType : ∀ {n : Nat} (source target : Presentation.Tower.Tm n),
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT
        HOLNativeMixedRuleData.language)).satisfies
        (HOLNativeMixedRuleData.compute (HOLNativeMixedRuleData.encoded source))
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT
            HOLNativeMixedRuleData.language)
          (HOLNativeMixedRuleData.encoded target)).pred ↔
      HOLNativeMixedOperationalDecomposition.ComputationalStep source target
  betaObserved : ∀ {n : Nat} (body : Presentation.Tower.Tm (n + 1))
      (argument : Presentation.Tower.Tm n),
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT
        HOLNativeMixedRuleData.language)).satisfies
        (HOLNativeMixedRuleData.compute
          (HOLNativeMixedRuleData.encoded (.app (.lam body) argument)))
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT
            HOLNativeMixedRuleData.language)
          (HOLNativeMixedRuleData.encoded
            (Presentation.inst0 argument body))).pred
  universeBoundary : ∀ {n : Nat},
    let left : Presentation.Tower.Tm n :=
      .head (.sort (.max (.param 0) (.param 0)))
    let right : Presentation.Tower.Tm n := .head (.sort (.param 0))
    HOLNativeMixedOperationalDecomposition.FullStep left right ∧
      ¬ HOLNativeMixedRuleDataOSLFConnection.presentationTheory.Step
        (HOLNativeMixedRuleData.compute (HOLNativeMixedRuleData.encoded left))
        (HOLNativeMixedRuleData.encoded right)

/-- All fields are inhabited by the retained map-fusion mathematical package
and the exact rule-data/OSLF correspondence. -/
theorem current : PresentedConnection.{u} where
  coherent := HOLLeibnizNativeQualifiedCoherentConnection.current
  equationFree := HOLNativeMixedRuleDataOSLFConnection.language_equation_free
  operationalStep := HOLNativeMixedRuleDataOSLFConnection.presentation_step_iff
  generatedNativeType := HOLNativeMixedRuleDataOSLFConnection.satisfies_exact_target_iff
  betaObserved := HOLNativeMixedRuleDataOSLFConnection.beta_satisfies_generated_oslf
  universeBoundary :=
    HOLNativeMixedRuleDataOSLFConnection.universe_head_equality_outside_presentation

#print axioms current

end HOLLeibnizNativeQualifiedPresentedConnection
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
