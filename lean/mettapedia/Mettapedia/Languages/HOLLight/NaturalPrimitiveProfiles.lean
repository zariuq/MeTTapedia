import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.NaturalModelCategoricity
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Logic.HOL.HOLLightBooleanConversions
import Mettapedia.Logic.HOL.NaturalRecursionProofs

/-!
# Natural-number source profiles through shared checked transport

The number carrier, zero and successor are arbitrary typed source operations.
Separation uses one retained negation contraction. Injectivity needs only
checked definition unfolding and the exact quantifier image. Neither profile
supplies the source laws; actual source cache entries remain required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.NaturalPrimitiveProfiles

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL HOL.ContextualTrinity CachedSourceProfileTransport

abbrev Signature := NaturalModelCategoricity.Signature

private theorem falsity_image {Γ : Ctx AtomicTy} (environment : ReverseTranslation.VarEnv Γ) :
    ReverseTranslation.reverseTermWith environment (weakenCtx Γ HOLLightBooleanDefinitions.falsity) =
      ReverseTranslation.reverseTermWith environment (ImpredicativeConnectives.falsity : Formula Symbol Γ) := by
  rw [ReverseTranslation.reverseTermWith_weakenCtx]
  rfl

def separationComparison (signature : Signature) : Formula Symbol [signature.number] :=
  .eq (.app (weakenCtx _ signature.successor) (.var .vz)) (weakenCtx _ signature.zero)

def separationUnfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.applyClosed HOLLightBooleanDefinitions.negation (separationComparison signature))

def separationReduced (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.imp (separationComparison signature)
    (weakenCtx _ HOLLightBooleanDefinitions.falsity))

def separationNative (signature : Signature) : ClosedFormula Symbol :=
  .all (.not (separationComparison signature))

@[irreducible] def separationStep (signature : Signature) :
    BetaStep (separationUnfolded signature) (separationReduced signature) :=
  HOLLightBooleanConversions.allStep (HOLLightBooleanConversions.negationStep (separationComparison signature))

def separationProof (signature : Signature) :
    ProofSyntax Symbol [separationUnfolded signature] (separationReduced signature) :=
  HOLLightBooleanConversions.transport ((separationStep signature).proof _) (.hyp ⟨0, by simp⟩)

theorem separationProof_free (signature : Signature) :
    (separationProof signature).FunctionExtensionalityFree :=
  HOLLightBooleanConversions.transport_free _ _ ((separationStep signature).proof_free _) trivial

theorem separation_image (signature : Signature) :
    CachedSourceExpansion.encode (separationReduced signature) =
      CachedSourceExpansion.encode (separationNative signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, separationReduced, separationNative,
    HOLLightBooleanConversions.expand_all, HOLLightBooleanConversions.expand_imp,
    ImpredicativeConnectives.expand, HOLLightBooleanConversions.expand_weakenCtx,
    HOLLightBooleanConversions.expand_falsity]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    BooleanDefinitionAlignment.implication_application, ReverseTranslation.reverseTermWith, falsity_image]

def separation (signature : Signature) : Profile where
  source := signature.successorSeparation
  unfolded := separationUnfolded signature
  target := separationReduced signature
  native := separationNative signature
  conversion := separationProof signature
  conversionFree := separationProof_free signature
  nativeImage := separation_image signature

def injectivityComparison (signature : Signature) : Formula Symbol [signature.number, signature.number] :=
  .eq (.eq (.app (weakenCtx _ signature.successor) (.var (.vs .vz)))
      (.app (weakenCtx _ signature.successor) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))

def injectivityUnfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (injectivityComparison signature))

def injectivityNative (signature : Signature) : ClosedFormula Symbol :=
  .all (.all (injectivityComparison signature))

theorem injectivity_image (signature : Signature) :
    CachedSourceExpansion.encode (injectivityUnfolded signature) =
      CachedSourceExpansion.encode (injectivityNative signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, injectivityUnfolded, injectivityNative,
    HOLLightBooleanConversions.expand_all, ImpredicativeConnectives.expand]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    ReverseTranslation.reverseTermWith]

def injectivity (signature : Signature) : Profile where
  source := signature.successorInjective
  unfolded := injectivityUnfolded signature
  target := injectivityUnfolded signature
  native := injectivityNative signature
  conversion := .hyp ⟨0, by simp⟩
  conversionFree := by simp only [ProofSyntax.FunctionExtensionalityFree]
  nativeImage := injectivity_image signature

def inductionBase (signature : Signature) : Formula Symbol [signature.number ⇒ .prop] :=
  .app (.var .vz) (weakenCtx _ signature.zero)

def inductionAt (signature : Signature) : Formula Symbol [signature.number, signature.number ⇒ .prop] :=
  .app (.var (.vs .vz)) (.var .vz)

def inductionNext (signature : Signature) : Formula Symbol [signature.number, signature.number ⇒ .prop] :=
  .app (.var (.vs .vz)) (.app (weakenCtx _ signature.successor) (.var .vz))

def inductionStep (signature : Signature) : Formula Symbol [signature.number ⇒ .prop] :=
  HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.imp (inductionAt signature) (inductionNext signature))

def inductionResult (signature : Signature) : Formula Symbol [signature.number ⇒ .prop] :=
  HOLLightBooleanDefinitions.all (inductionAt signature)

def inductionUnfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.imp
    (HOLLightBooleanDefinitions.conj (inductionBase signature) (inductionStep signature))
    (inductionResult signature))

def inductionTarget (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.imp
    (.and (inductionBase signature) (inductionStep signature)) (inductionResult signature))

def inductionNative (signature : Signature) : ClosedFormula Symbol :=
  .all (.imp (.and (inductionBase signature)
    (.all (.imp (inductionAt signature) (inductionNext signature)))) (.all (inductionAt signature)))

@[irreducible] def inductionEquation (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    ProofSyntax Symbol assumptions (.eq (inductionUnfolded signature) (inductionTarget signature)) :=
  HOLLightBooleanConversions.allCongruence
    (HOLLightBooleanConversions.implicationCongruence
      (HOLLightBooleanConversions.conjunctionEquation (inductionBase signature) (inductionStep signature))
      (.eqRefl (inductionResult signature)))

theorem inductionEquation_free (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    (inductionEquation signature assumptions).FunctionExtensionalityFree := by
  unfold inductionEquation
  apply HOLLightBooleanConversions.allCongruence_free
  exact HOLLightBooleanConversions.implicationCongruence_free _ _
    (HOLLightBooleanConversions.conjunctionEquation_free _ _) trivial

def inductionProof (signature : Signature) :
    ProofSyntax Symbol [inductionUnfolded signature] (inductionTarget signature) :=
  HOLLightBooleanConversions.transport (inductionEquation signature _) (.hyp ⟨0, by simp⟩)

theorem inductionProof_free (signature : Signature) : (inductionProof signature).FunctionExtensionalityFree :=
  HOLLightBooleanConversions.transport_free _ _ (inductionEquation_free signature _) trivial

theorem induction_image (signature : Signature) :
    CachedSourceExpansion.encode (inductionTarget signature) =
      CachedSourceExpansion.encode (inductionNative signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, inductionTarget, inductionNative,
    inductionStep, inductionResult, HOLLightBooleanConversions.expand_all,
    HOLLightBooleanConversions.expand_imp, ImpredicativeConnectives.expand]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    BooleanDefinitionAlignment.implication_application, ReverseTranslation.reverseTermWith]

theorem induction_is_principle (signature : Signature) :
    inductionNative signature = NaturalRecursionProofs.inductionPrinciple signature.zero signature.successor := by
  simp [inductionNative, inductionBase, inductionAt, inductionNext,
    NaturalRecursionProofs.inductionPrinciple, weakenCtx]

def induction (signature : Signature) : Profile where
  source := signature.induction
  unfolded := inductionUnfolded signature
  target := inductionTarget signature
  native := inductionNative signature
  conversion := inductionProof signature
  conversionFree := inductionProof_free signature
  nativeImage := induction_image signature

#print axioms separationProof_free
#print axioms separation_image
#print axioms separation
#print axioms injectivity_image
#print axioms injectivity
#print axioms inductionEquation_free
#print axioms induction_image
#print axioms induction_is_principle
#print axioms induction

end Mettapedia.Languages.HOLLight.NaturalPrimitiveProfiles
