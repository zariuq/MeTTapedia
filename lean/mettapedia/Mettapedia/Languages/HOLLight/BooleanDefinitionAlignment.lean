import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives

/-!
# Native images of the original Boolean definition bodies

The independently specified HOL Light bodies and the retained translator's
native connective programs are compared at their actual typed syntax. This
comparison concerns definition bodies, not registered source constants.
Replacing a source constant still requires its checked defining equation;
impredicative expansion has its separate proof obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation

theorem truth_body : reverseTermOpen (HOL.HOLLightBooleanDefinitions.truth (Const := Symbol)) =
    PrimitiveSentences.truthDB := rfl

theorem conjunction_body :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.conjunction (Const := Symbol)) = ExcludedMiddle.andDB := rfl

theorem implication_body :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.implication (Const := Symbol)) = ExcludedMiddle.impDB := rfl

theorem universal_body (type : HOL.Ty AtomicTy) :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.universal type (Const := Symbol)) =
      ExcludedMiddle.forallDB (reverseTy type) := rfl

theorem falsity_body :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.falsity (Const := Symbol)) =
      ExcludedMiddle.falsityDefinitionDB := rfl

theorem negation_body :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.negation (Const := Symbol)) = ExcludedMiddle.notDB := rfl

theorem universal_application {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (environment : VarEnv Γ) (body : HOL.Formula Symbol (type :: Γ)) :
    reverseTermWith environment (HOL.HOLLightBooleanDefinitions.all body) =
      reverseTermWith environment (.all body) := by
  simp only [HOL.HOLLightBooleanDefinitions.all, HOL.HOLLightBooleanDefinitions.applyClosed,
    reverseTermWith, reverseTermWith_weakenCtx, universal_body]

theorem implication_application {Γ : HOL.Ctx AtomicTy} (environment : VarEnv Γ)
    (left right : HOL.Formula Symbol Γ) :
    reverseTermWith environment (HOL.HOLLightBooleanDefinitions.imp left right) =
      reverseTermWith environment (.imp left right) := by
  simp only [HOL.HOLLightBooleanDefinitions.imp, HOL.HOLLightBooleanDefinitions.applyClosed,
    reverseTermWith, reverseTermWith_weakenCtx, implication_body, ExcludedMiddle.impAppDB]

theorem expanded_falsity :
    reverseTermOpen (HOL.ImpredicativeConnectives.expand (.bot : HOL.ClosedFormula Symbol)) =
      reverseTermOpen (HOL.HOLLightBooleanDefinitions.falsity (Const := Symbol)) := rfl

theorem expanded_universal {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (environment : VarEnv Γ) (body : HOL.Formula Symbol (type :: Γ)) :
    reverseTermWith environment (HOL.ImpredicativeConnectives.expand (.all body)) =
      reverseTermWith environment (HOL.HOLLightBooleanDefinitions.all (HOL.ImpredicativeConnectives.expand body)) :=
  (universal_application environment _).symm

theorem expanded_implication {Γ : HOL.Ctx AtomicTy} (environment : VarEnv Γ)
    (left right : HOL.Formula Symbol Γ) :
    reverseTermWith environment (HOL.ImpredicativeConnectives.expand (.imp left right)) =
      reverseTermWith environment (HOL.HOLLightBooleanDefinitions.imp
        (HOL.ImpredicativeConnectives.expand left) (HOL.ImpredicativeConnectives.expand right)) :=
  (implication_application environment _ _).symm

def negationBody : DBTerm := ExcludedMiddle.impAppDB (.bound 0) ExcludedMiddle.falsityDefinitionDB

theorem negationBody_checked : negationBody.inferType [Ty.bool] = some Ty.bool :=
  DerivedRules.inferType_impAppDB (by simp) DerivedRules.inferType_falsityDefinitionDB

def negationExpansion (argument : CanonicalTerm) (boolean : argument.IsBool) : PrimitiveTransport.BetaExpansion :=
  PrimitiveTransport.betaExpansion Ty.bool negationBody Ty.bool negationBody_checked argument boolean

theorem negation_redex (argument : CanonicalTerm) (boolean : argument.IsBool) :
    (PrimitiveTransport.betaRedex Ty.bool negationBody Ty.bool negationBody_checked argument boolean).term =
      .app ExcludedMiddle.notDB argument.term := rfl

theorem negation_reduced (argument : CanonicalTerm) (boolean : argument.IsBool) :
    (PrimitiveTransport.betaReduced Ty.bool negationBody Ty.bool negationBody_checked argument boolean).term =
      ExcludedMiddle.impAppDB argument.term ExcludedMiddle.falsityDefinitionDB := by
  simp [PrimitiveTransport.betaReduced, negationBody, ExcludedMiddle.impAppDB,
    DBTerm.instantiateAt, DerivedRules.instantiateAt_impDB, DerivedRules.instantiateAt_falsityDefinitionDB]

theorem negation_block_checked (policy : AxiomPolicy) [DecidablePred policy]
    (argument : CanonicalTerm) (boolean : argument.IsBool) (origin : ProofExecution.Origin) :
    GraphExpansion.BlockChecked policy [] (negationExpansion argument boolean).conclusion
      (PrimitiveTransport.betaBlock (negationExpansion argument boolean) origin) :=
  PrimitiveTransport.betaBlock_checked policy _ origin

/-- Equal Boolean meanings do not identify the two conjunction encodings. -/
theorem conjunction_expansion_differs :
    reverseTermOpen (HOL.HOLLightBooleanDefinitions.conj (.top : HOL.ClosedFormula Symbol) .bot) ≠
      reverseTermOpen (HOL.ImpredicativeConnectives.expand (.and (.top : HOL.ClosedFormula Symbol) .bot)) := by
  intro same
  cases same

#print axioms truth_body
#print axioms conjunction_body
#print axioms implication_body
#print axioms universal_body
#print axioms falsity_body
#print axioms negation_body
#print axioms universal_application
#print axioms implication_application
#print axioms expanded_falsity
#print axioms expanded_universal
#print axioms expanded_implication
#print axioms negation_reduced
#print axioms negation_block_checked
#print axioms conjunction_expansion_differs
end Mettapedia.Languages.HOLLight.BooleanDefinitionAlignment
