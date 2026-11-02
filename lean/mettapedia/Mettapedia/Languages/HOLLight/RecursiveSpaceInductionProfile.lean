import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Logic.HOL.HOLLightBooleanConversions

/-!
# The recursive-space induction source profile

The predicate, constructor fields and child slot retain their original
binding scopes. Checked conjunction conversion connects the original base
and method hypothesis to the native induction formula. The induction theorem
itself must still be supplied by the checked source cache.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.RecursiveSpaceInductionProfile

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL

abbrev Signature := RecursiveSpaceModelComparison.Signature

def base (signature : Signature) : Formula Symbol [signature.space ⇒ .prop] :=
  .app (.var .vz) (weakenCtx _ signature.bottom)

def child (signature : Signature) :
    Formula Symbol [signature.number, signature.number ⇒ signature.space,
      signature.payload, signature.number, signature.space ⇒ .prop] :=
  .app (.var (.vs (.vs (.vs (.vs .vz))))) (.app (.var (.vs .vz)) (.var .vz))

def resultAt (signature : Signature) :
    Formula Symbol [signature.number ⇒ signature.space, signature.payload,
      signature.number, signature.space ⇒ .prop] :=
  .app (.var (.vs (.vs (.vs .vz))))
    (signature.applyConstructor (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))

def method (signature : Signature) : Formula Symbol [signature.space ⇒ .prop] :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.imp (HOLLightBooleanDefinitions.all (child signature)) (resultAt signature))))

def conclusionAt (signature : Signature) : Formula Symbol [signature.space, signature.space ⇒ .prop] :=
  .app (.var (.vs .vz)) (.var .vz)

def result (signature : Signature) : Formula Symbol [signature.space ⇒ .prop] :=
  HOLLightBooleanDefinitions.all (conclusionAt signature)

def unfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.imp
    (HOLLightBooleanDefinitions.conj (base signature) (method signature)) (result signature))

def target (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.imp
    (.and (base signature) (method signature)) (result signature))

def nativeMethod (signature : Signature) : Formula Symbol [signature.space ⇒ .prop] :=
  .all (.all (.all (.imp (.all (child signature)) (resultAt signature))))

def native (signature : Signature) : ClosedFormula Symbol :=
  .all (.imp (.and (base signature) (nativeMethod signature)) (.all (conclusionAt signature)))

@[irreducible] def equation (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    ProofSyntax Symbol assumptions (.eq (unfolded signature) (target signature)) :=
  HOLLightBooleanConversions.allCongruence
    (HOLLightBooleanConversions.implicationCongruence
      (HOLLightBooleanConversions.conjunctionEquation (base signature) (method signature))
      (.eqRefl (result signature)))

theorem equation_free (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    (equation signature assumptions).FunctionExtensionalityFree := by
  unfold equation
  apply HOLLightBooleanConversions.allCongruence_free
  exact HOLLightBooleanConversions.implicationCongruence_free _ _
    (HOLLightBooleanConversions.conjunctionEquation_free _ _) trivial

def proof (signature : Signature) : ProofSyntax Symbol [unfolded signature] (target signature) :=
  HOLLightBooleanConversions.transport (equation signature _) (.hyp ⟨0, by simp⟩)

theorem proof_free (signature : Signature) : (proof signature).FunctionExtensionalityFree :=
  HOLLightBooleanConversions.transport_free _ _ (equation_free signature _) trivial

theorem target_image (signature : Signature) :
    CachedSourceExpansion.encode (target signature) = CachedSourceExpansion.encode (native signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, target, native, method, result, nativeMethod,
    HOLLightBooleanConversions.expand_all, HOLLightBooleanConversions.expand_imp,
    ImpredicativeConnectives.expand]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    BooleanDefinitionAlignment.implication_application, ReverseTranslation.reverseTermWith]

def profile (signature : Signature) : CachedSourceProfileTransport.Profile where
  source := signature.induction
  unfolded := unfolded signature
  target := target signature
  native := native signature
  conversion := proof signature
  conversionFree := proof_free signature
  nativeImage := target_image signature

#print axioms equation_free
#print axioms proof_free
#print axioms target_image
#print axioms profile

end Mettapedia.Languages.HOLLight.RecursiveSpaceInductionProfile
