import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.ModelInterpretation
import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics
import Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
import Mettapedia.Logic.HOL.HOLLightBooleanConversions
import Mettapedia.Logic.HOL.SelectionProofs

/-!
# Exact source selection instances for retained recovery programs

The source selection constant retains its actual operand type. Boolean
definition unfolding connects the cached source statement to the retained
selection principle. The profile converts supplied source evidence; it does
not introduce a selection axiom or certify a cache entry by its name.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceSelectionProfile
open Mettapedia.Logic Mettapedia.Languages.OpenTheory HOL

def selection (operand : Ty) : ClosedTerm Symbol (SelectionProofs.Selection operand.toHOL) :=
  .const (.constant ModelInterpretation.selectionConstant (ModelInterpretation.selectionType operand)
    (ModelInterpretation.selectionType_toHOL operand))

def premise (operand : Ty) : Formula Symbol [operand.toHOL,operand.toHOL ⇒ .prop] :=
  .app (.var (.vs .vz)) (.var .vz)

def consequence (operand : Ty) : Formula Symbol [operand.toHOL,operand.toHOL ⇒ .prop] :=
  .app (.var (.vs .vz)) (.app (weakenCtx _ (selection operand)) (.var (.vs .vz)))

def source (operand : Ty) : ClosedFormula Symbol :=
  ReferenceBooleanSemantics.universal (ReferenceBooleanSemantics.universal
    (ReferenceBooleanSemantics.implication (premise operand) (consequence operand)))

def unfolded (operand : Ty) : ClosedFormula Symbol :=
  HOLLightBooleanDefinitions.all (HOLLightBooleanDefinitions.all
    (HOLLightBooleanDefinitions.imp (premise operand) (consequence operand)))

def native (operand : Ty) : ClosedFormula Symbol :=
  .all (.all (.imp (premise operand) (consequence operand)))

theorem native_is_principle (operand : Ty) : native operand = SelectionProofs.principle (selection operand) := by
  simp only [native, premise, consequence, SelectionProofs.principle, SelectionProofs.instanceFormula,
    weakenCtx, weaken, rename, Rename.weaken]

theorem native_is_source_formula (operand : Ty) : native operand = ModelInterpretation.selectionFormula operand := rfl

theorem native_image (operand : Ty) :
    CachedSourceExpansion.encode (unfolded operand) = CachedSourceExpansion.encode (native operand) := by
  apply CanonicalTerm.ext_term
  simp only [CachedSourceExpansion.encode, ReverseTranslation.reverseCanonical_term,
    ReverseTranslation.reverseTerm_eq_reverseTermOpen, unfolded, native,
    HOLLightBooleanConversions.expand_all, HOLLightBooleanConversions.expand_imp, ImpredicativeConnectives.expand]
  simp only [ReverseTranslation.reverseTermOpen, BooleanDefinitionAlignment.universal_application,
    BooleanDefinitionAlignment.implication_application, ReverseTranslation.reverseTermWith]

def profile (operand : Ty) : CachedSourceProfileTransport.Profile where
  source := source operand
  unfolded := unfolded operand
  target := unfolded operand
  native := native operand
  conversion := .hyp ⟨0,by simp⟩
  conversionFree := by simp only [ProofSyntax.FunctionExtensionalityFree]
  nativeImage := native_image operand

#print axioms native_is_principle
#print axioms native_image
end Mettapedia.Languages.HOLLight.SourceSelectionProfile
