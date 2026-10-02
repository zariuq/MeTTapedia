import Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation
import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.GSLT.LanguageDef.BinderTypingInversion

/-!
# Lambda controls for literal source insertion

The actual lambda cut retypes an abstraction's binder and result to wrapped
terms, while application's function position remains base.  Consequently a
uniform base-symbol translation of the admitted self-application abstraction
does not type.  Duplicating each source variable into two local environments
does type the local application, but adding a second target binder does not
fit the authored one-binder abstraction parameter.

There is nevertheless a typed wrapped-to-base term context: apply the
generated identity abstraction to the wrapped argument.  It inserts a beta
redex.  Its erased authored syntax is not statically equal to the variable,
and its funded/unfunded controls retain the existing activation requirement.
Thus this module rejects specific literal insertion routes, not all possible
compilers or context interpretations.  A semantic account projection requires
its own authored-operation and resource comparison.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.LambdaInstance
open LambdaContinuedInteraction WellSorted

set_option autoImplicit false

def sourceSelfApplication : Pattern :=
  .apply "Lam" [.lambda none (.apply "App" [.bvar 0, .bvar 0])]

/-- This counterexample belongs to the actual validated source grammar. -/
theorem source_self_application_typed :
    HasSort lambdaCalc FreeTypeContext.empty [] sourceSelfApplication "Term" :=
  checkHasType_sound (by decide +kernel)

def literalBaseTranslation : Pattern :=
  mapPattern costBaseLanguageDefSymbolMap sourceSelfApplication

/-- The literal declaration-symbol action fails on a concrete closed source
term, after the selected continuation's domain has changed to wrapped. -/
theorem literal_base_translation_not_typed :
    ¬ HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty []
      literalBaseTranslation (costBaseSortName "Term") := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType lambdaCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] literalBaseTranslation
      (.base (costBaseSortName "Term")) = false := by decide +kernel
  rw [rejected] at checked
  contradiction

/-- An outer signed unit cannot repair an ill-typed body. -/
theorem signed_literal_translation_not_typed :
    ¬ HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (.apply costSignedConstructorName
        [literalBaseTranslation, .apply costSignatureUnitConstructorName []])
      costWrappedSortName := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType lambdaCIGSLT.costWholeLanguage
      FreeTypeContext.empty []
      (.apply costSignedConstructorName
        [literalBaseTranslation, .apply costSignatureUnitConstructorName []])
      (.base costWrappedSortName) = false := by decide +kernel
  rw [rejected] at checked
  contradiction

/-- A single local wrapped binder cannot also provide the base variable. -/
theorem wrapped_variable_not_base :
    ¬ HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty
      [.base costWrappedSortName] (.bvar 0) (costBaseSortName "Term") := by
  intro typed
  have lookup := typed.bvar_inv
  exact costBaseSortName_ne_wrapped "Term" (by
    simpa only [List.getElem?_cons_zero, Option.some.injEq, TypeExpr.base.injEq] using lookup.symm)

def twoEnvironmentApplication : Pattern :=
  .apply (costBaseConstructorName "App") [.bvar 1, .bvar 0]

/-- Two independent environments solve the local typing mismatch. -/
theorem two_environment_application_typed :
    HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty
      [.base costWrappedSortName, .base (costBaseSortName "Term")]
      twoEnvironmentApplication (costBaseSortName "Term") :=
  checkHasType_sound (by decide +kernel)

def twoBinderAbstraction : Pattern :=
  .apply (costBaseConstructorName "Lam")
    [.lambda none (.lambda none
      (.apply costSignedConstructorName
        [twoEnvironmentApplication, .apply costSignatureUnitConstructorName []]))]

/-- The authored abstraction has one binder, so this local remedy does not
by itself yield a closed translation of the original one-binder source term. -/
theorem two_binder_abstraction_not_typed :
    ¬ HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty []
      twoBinderAbstraction (costBaseSortName "Term") := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType lambdaCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] twoBinderAbstraction
      (.base (costBaseSortName "Term")) = false := by decide +kernel
  rw [rejected] at checked
  contradiction

/-- A literal wrapped-to-base adapter exists, using the generated beta cut. -/
def identityAdapter (argument : Pattern) : Pattern :=
  FiniteLambdaActivation.betaRedex (.bvar 0) argument

theorem identity_adapter_typed :
    HasSort lambdaCIGSLT.costWholeLanguage FreeTypeContext.empty
      [.base costWrappedSortName] (identityAdapter (.bvar 0))
      (costBaseSortName "Term") :=
  checkHasType_sound (by decide +kernel)

def erasedIdentityAdapter : Pattern :=
  .apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]

theorem identity_adapter_erasure :
    CostAuthoredAtomKey.eraseColor .base (identityAdapter (.bvar 0)) =
      erasedIdentityAdapter := by decide +kernel

/-- This adapter does not preserve the variable's source static equation
class.  Beta is a transition in this presentation, not a static equation. -/
theorem adapter_not_source_equivalent_to_variable :
    ¬ EquationSemantics.EquationEquiv defaultBasePremises lambdaCalc
      erasedIdentityAdapter (.bvar 0) := by
  intro equivalent
  have equality := (EquationSemantics.equationEquiv_iff_eq_of_no_generators
    (base := defaultBasePremises) (language := lambdaCalc) (by rfl)
    erasedIdentityAdapter (.bvar 0)).mp equivalent
  cases equality

/-- The identity adapter can be activated with actual funding, but its
empty-purse version retains the generated no-firing boundary. -/
theorem adapter_requires_funded_activation :
    Step (engineBasePremises RelationEnv.empty)
        FiniteLambdaActivation.profile.costWholeRedexLanguage
        FiniteLambdaActivation.identitySource FiniteLambdaActivation.identityTarget ∧
      ∀ result, ¬ Step (engineBasePremises RelationEnv.empty)
        FiniteLambdaActivation.profile.costWholeRedexLanguage
        FiniteLambdaActivation.unfundedIdentity result :=
  ⟨FiniteLambdaActivation.funded_identity_fires,
    FiniteLambdaActivation.unfunded_identity_no_step (engineBasePremises RelationEnv.empty)⟩

#print axioms source_self_application_typed
#print axioms literal_base_translation_not_typed
#print axioms signed_literal_translation_not_typed
#print axioms wrapped_variable_not_base
#print axioms two_environment_application_typed
#print axioms two_binder_abstraction_not_typed
#print axioms identity_adapter_typed
#print axioms adapter_not_source_equivalent_to_variable
#print axioms adapter_requires_funded_activation

end Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary
