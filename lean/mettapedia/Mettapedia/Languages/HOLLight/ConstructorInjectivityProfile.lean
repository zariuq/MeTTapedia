import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.RecursiveSpaceModelComparison
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Logic.HOL.HOLLightBooleanConversions
import Mettapedia.Logic.HOL.ConstructorInjectivity

/-!
# Constructor injectivity through the shared source-profile transport

The six source binders and all three field equalities retain their positions.
Both source conjunctions are converted by the retained selector proof before
the result enters the native logical profile. Constructor laws remain actual
source premises, rather than assumptions of the conversion itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ConstructorInjectivityProfile

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL

abbrev Signature := RecursiveSpaceModelComparison.Signature

def context (signature : Signature) : Ctx AtomicTy :=
  [signature.number ⇒ signature.space, signature.payload, signature.number,
    signature.number ⇒ signature.space, signature.payload, signature.number]

def imageEquality (signature : Signature) : Formula Symbol (context signature) :=
  .eq (signature.applyConstructor (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
      (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz)))))
    (signature.applyConstructor (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))

def tagEquality (signature : Signature) : Formula Symbol (context signature) :=
  .eq (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs .vz)))

def payloadEquality (signature : Signature) : Formula Symbol (context signature) :=
  .eq (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs .vz))

def childrenEquality (signature : Signature) : Formula Symbol (context signature) :=
  .eq (.var (.vs (.vs (.vs .vz)))) (.var .vz)

def sourceBody (signature : Signature) : Formula Symbol (context signature) :=
  .eq (imageEquality signature) (HOLLightBooleanDefinitions.conj (tagEquality signature)
    (HOLLightBooleanDefinitions.conj (payloadEquality signature) (childrenEquality signature)))

def targetBody (signature : Signature) : Formula Symbol (context signature) :=
  .eq (imageEquality signature) (.and (tagEquality signature)
    (.and (payloadEquality signature) (childrenEquality signature)))

def unfolded (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
      (sourceBody signature))))))

def target (signature : Signature) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
      (targetBody signature))))))

def native (signature : Signature) : ClosedFormula Symbol :=
  .all (.all (.all (.all (.all (.all (targetBody signature))))))

def bodyEquation (signature : Signature) {assumptions : List (Formula Symbol (context signature))} :
    ProofSyntax Symbol assumptions (.eq (sourceBody signature) (targetBody signature)) :=
  ProofSyntax.eqCongr (.eqRefl (imageEquality signature))
    (HOLLightBooleanConversions.conjunctionMap (.eqRefl (tagEquality signature))
      (HOLLightBooleanConversions.conjunctionEquation (payloadEquality signature) (childrenEquality signature)))

theorem bodyEquation_free (signature : Signature)
    {assumptions : List (Formula Symbol (context signature))} :
    (bodyEquation signature (assumptions := assumptions)).FunctionExtensionalityFree := by
  apply (ProofSyntax.eqCongr_free _ _).mpr
  exact ⟨trivial, HOLLightBooleanConversions.conjunctionMap_free _ _ trivial
    (HOLLightBooleanConversions.conjunctionEquation_free _ _)⟩

@[irreducible] def equation (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    ProofSyntax Symbol assumptions (.eq (unfolded signature) (target signature)) :=
  HOLLightBooleanConversions.allCongruence (HOLLightBooleanConversions.allCongruence
    (HOLLightBooleanConversions.allCongruence (HOLLightBooleanConversions.allCongruence
      (HOLLightBooleanConversions.allCongruence (HOLLightBooleanConversions.allCongruence
        (bodyEquation signature))))))

theorem equation_free (signature : Signature) (assumptions : List (ClosedFormula Symbol)) :
    (equation signature assumptions).FunctionExtensionalityFree := by
  unfold equation
  repeat apply HOLLightBooleanConversions.allCongruence_free
  exact bodyEquation_free signature

def proof (signature : Signature) : ProofSyntax Symbol [unfolded signature] (target signature) :=
  HOLLightBooleanConversions.transport (equation signature _) (.hyp ⟨0, by simp⟩)

theorem proof_free (signature : Signature) : (proof signature).FunctionExtensionalityFree :=
  HOLLightBooleanConversions.transport_free _ _ (equation_free signature _) trivial

theorem target_image (signature : Signature) :
    CachedSourceExpansion.encode (target signature) = CachedSourceExpansion.encode (native signature) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, target, native,
    HOLLightBooleanConversions.expand_all, ImpredicativeConnectives.expand]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    ReverseTranslation.reverseTermWith]

theorem native_is_statement (signature : Signature) :
    native signature = ConstructorInjectivity.statement signature.construct := by
  simp [native, targetBody, imageEquality, tagEquality, payloadEquality, childrenEquality,
    RecursiveSpaceModelComparison.Signature.applyConstructor, ConstructorInjectivity.statement,
    ConstructorInjectivity.atImage, ConstructorProjections.apply, context, weakenCtx, weaken,
    rename, rename_comp, Rename.weaken]

def profile (signature : Signature) : CachedSourceProfileTransport.Profile where
  source := signature.constructorInjective
  unfolded := unfolded signature
  target := target signature
  native := native signature
  conversion := proof signature
  conversionFree := proof_free signature
  nativeImage := target_image signature

#print axioms bodyEquation_free
#print axioms equation_free
#print axioms target_image
#print axioms native_is_statement
#print axioms profile

end Mettapedia.Languages.HOLLight.ConstructorInjectivityProfile
