import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Logic.HOL.HOLLightBooleanConversions
import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment

/-!
# Retained conversion of the constructor-separation profile

The source declaration uses three named universal quantifiers and named
negation. After checked definition unfolding, one beta contraction under
their three binders connects the equality/lambda presentation to the native
logical profile. The constructor and bottom operations remain parameters.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ConstructorSeparationProfile

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL HOL.ContextualTrinity

theorem falsity_image {Γ : Ctx AtomicTy} (environment : ReverseTranslation.VarEnv Γ) :
    ReverseTranslation.reverseTermWith environment (weakenCtx Γ HOLLightBooleanDefinitions.falsity) =
      ReverseTranslation.reverseTermWith environment (ImpredicativeConnectives.falsity : Formula Symbol Γ) := by
  rw [ReverseTranslation.reverseTermWith_weakenCtx]
  rfl


abbrev Signature := RecursiveSpaceModelComparison.Signature

def context (signature : Signature) : Ctx AtomicTy :=
  [signature.number ⇒ signature.space, signature.payload, signature.number]

def comparison (signature : Signature) : Formula Symbol (context signature) :=
  .eq (signature.applyConstructor (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
    (weakenCtx _ signature.bottom)

def unfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.applyClosed HOLLightBooleanDefinitions.negation (comparison signature))))

def reduced (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.imp (comparison signature)
      (weakenCtx _ HOLLightBooleanDefinitions.falsity))))

def primitive (signature : Signature) : ClosedFormula Symbol :=
  .all (.all (.all (.not (comparison signature))))

@[irreducible] def step (signature : Signature) : BetaStep (unfolded signature) (reduced signature) :=
  HOLLightBooleanConversions.allStep (HOLLightBooleanConversions.allStep (HOLLightBooleanConversions.allStep (HOLLightBooleanConversions.negationStep (comparison signature))))

def proof (signature : Signature) : ProofSyntax Symbol [unfolded signature] (reduced signature) :=
  HOLLightBooleanConversions.transport ((step signature).proof [unfolded signature]) (.hyp ⟨0, by simp⟩)

theorem proof_free (signature : Signature) : (proof signature).FunctionExtensionalityFree := by
  exact HOLLightBooleanConversions.transport_free _ _ ((step signature).proof_free [unfolded signature]) trivial

theorem reduced_image (signature : Signature) :
    CachedSourceExpansion.encode (reduced signature) = CachedSourceExpansion.encode (primitive signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, reduced, primitive, HOLLightBooleanConversions.expand_all,
    HOLLightBooleanConversions.expand_imp, ImpredicativeConnectives.expand, HOLLightBooleanConversions.expand_weakenCtx, HOLLightBooleanConversions.expand_falsity]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    BooleanDefinitionAlignment.implication_application, ReverseTranslation.reverseTermWith, falsity_image]


def profile (signature : Signature) : CachedSourceProfileTransport.Profile where
  source := signature.constructorSeparation
  unfolded := unfolded signature
  target := reduced signature
  native := primitive signature
  conversion := proof signature
  conversionFree := proof_free signature
  nativeImage := reduced_image signature

#print axioms step
#print axioms proof_free
#print axioms reduced_image
#print axioms profile

end Mettapedia.Languages.HOLLight.ConstructorSeparationProfile
