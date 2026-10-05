import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteraction
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteContinuationControls

/-!
# Finite Cost interaction controls

The same generated Cost apparatus validates for lambda calculus, asynchronous
rho, and synchronous rho's three-payload continuation profile.  The two-slot
instances recover the existing Cost cores exactly.  The synchronous example
retains the extra sent-process payload and its distinct local typing context.
An actual funded synchronous interaction consumes one matching head, retains
its nonempty tail, substitutes the quoted sent payload, and releases the
output continuation. Empty or mismatched authority does not enable a step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

abbrev lambdaProfile :=
  ContinuationDecorationProfile.ofRetypingPlan
    LambdaContinuedInteraction.lambdaCIGSLT.continuationRetyping

abbrev asynchronousProfile :=
  ContinuationDecorationProfile.ofRetypingPlan rhoCIGSLT.continuationRetyping

theorem lambda_core_valid : lambdaProfile.costCoreLanguage.validate = [] :=
  lambdaProfile.costCoreLanguage_validate
    LambdaContinuedInteraction.lambdaCIGSLT.continuationRetyping.noDuplicates

theorem asynchronous_core_valid : asynchronousProfile.costCoreLanguage.validate = [] :=
  asynchronousProfile.costCoreLanguage_validate rhoCIGSLT.continuationRetyping.noDuplicates

theorem synchronous_core_valid :
    Synchronous.communicationDecoration.costCoreLanguage.validate = [] :=
  Synchronous.communicationDecoration.costCoreLanguage_validate
    Synchronous.rhoSyncContinuationRetyping.noDuplicates

theorem lambda_core_legacy :
    lambdaProfile.costCoreLanguage = LambdaContinuedInteraction.lambdaCIGSLT.costCoreLanguage :=
  ContinuationDecorationProfile.ofRetypingPlan_costCoreLanguage _

theorem asynchronous_core_legacy :
    asynchronousProfile.costCoreLanguage = rhoCIGSLT.costCoreLanguage :=
  ContinuationDecorationProfile.ofRetypingPlan_costCoreLanguage _

/-- Appending funding apparatus retains both output payload positions at the
wrapped sort, independently of the input body's local name binder. -/
theorem synchronous_output_retained :
    ∃ constructor ∈ Synchronous.communicationDecoration.costCoreLanguage.terms,
      constructor.label = costBaseConstructorName "POutputK" ∧
      constructor.params =
        [.simple "n" (.base (costBaseSortName "Name")),
          .simple "q" (.base costWrappedSortName),
          .simple "k" (.base costWrappedSortName)] := by
  refine ⟨Synchronous.communicationDecoration.baseConstructor Synchronous.rhoSyncOutputRule,
    List.mem_append_left _ (Synchronous.communicationDecoration.baseConstructor_mem _
      Synchronous.rhoSyncOutputConstructor.2), rfl, ?_⟩
  exact Synchronous.communicationDecoration_output_parameters

/-- The core extension retains a concrete closed redex with all three
continuations, including the input-local binder occurrence. -/
theorem synchronous_redex_in_core :
    HasType Synchronous.communicationDecoration.costCoreLanguage FreeTypeContext.empty []
      (Synchronous.decoratedRedex
        (.apply (costWrappedConstructorName "NQuote")
          [Synchronous.FiniteContinuationControls.zero])
        Synchronous.FiniteContinuationControls.localBody
        Synchronous.FiniteContinuationControls.zero
        Synchronous.FiniteContinuationControls.zero)
      (.base (costBaseSortName "Proc")) :=
  Synchronous.communicationDecoration.hasType_costCoreLanguage
    Synchronous.FiniteContinuationControls.actual_redex_typed

/-- The instantiated three-payload contractum remains admitted after the
apparatus extension.  This statement supplies no operational funding. -/
theorem synchronous_contractum_in_core :
    HasType Synchronous.communicationDecoration.costCoreLanguage FreeTypeContext.empty []
      (Synchronous.instantiatedContractum
        Synchronous.FiniteContinuationControls.localBody
        Synchronous.FiniteContinuationControls.zero
        Synchronous.FiniteContinuationControls.zero)
      (.base costWrappedSortName) :=
  Synchronous.communicationDecoration.hasType_costCoreLanguage
    Synchronous.FiniteContinuationControls.actual_contractum_typed

theorem lambda_rule_sorted :
    HasSort lambdaProfile.costCoreLanguage lambdaProfile.costWholeRedexFreeContext []
      lambdaProfile.costWholeRedexSource costWrappedSortName ∧
    HasSort lambdaProfile.costCoreLanguage lambdaProfile.costWholeRedexFreeContext []
      lambdaProfile.costWholeRedexTarget costWrappedSortName :=
  ⟨lambdaProfile.costWholeRedexSource_hasType
      ((ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
        LambdaContinuedInteraction.lambdaCIGSLT.redexRetypable),
    lambdaProfile.costWholeRedexTarget_hasType
      ((ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr
        LambdaContinuedInteraction.lambdaCIGSLT.wrappable)⟩

theorem asynchronous_rule_sorted :
    HasSort asynchronousProfile.costCoreLanguage asynchronousProfile.costWholeRedexFreeContext []
      asynchronousProfile.costWholeRedexSource costWrappedSortName ∧
    HasSort asynchronousProfile.costCoreLanguage asynchronousProfile.costWholeRedexFreeContext []
      asynchronousProfile.costWholeRedexTarget costWrappedSortName :=
  ⟨asynchronousProfile.costWholeRedexSource_hasType
      ((ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
        rhoCIGSLT.redexRetypable),
    asynchronousProfile.costWholeRedexTarget_hasType
      ((ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr rhoCIGSLT.wrappable)⟩

theorem synchronous_rule_sorted :
    HasSort Synchronous.communicationDecoration.costCoreLanguage
      Synchronous.communicationDecoration.costWholeRedexFreeContext []
      Synchronous.communicationDecoration.costWholeRedexSource costWrappedSortName ∧
    HasSort Synchronous.communicationDecoration.costCoreLanguage
      Synchronous.communicationDecoration.costWholeRedexFreeContext []
      Synchronous.communicationDecoration.costWholeRedexTarget costWrappedSortName :=
  ⟨Synchronous.communicationDecoration.costWholeRedexSource_hasType
      Synchronous.communicationDecoration_redexRetypable,
    Synchronous.communicationDecoration.costWholeRedexTarget_hasType
      Synchronous.communicationDecoration_wrappable⟩

namespace FundedSynchronous

open Synchronous.FiniteContinuationControls

def unitSignature : Pattern := .apply costSignatureUnitConstructorName []
def emptyStack : Pattern := .apply costTokenStackEmptyConstructorName []
def retainedTail : Pattern := .apply costTokenStackConsConstructorName [unitSignature, emptyStack]
def afterOutput : Pattern := .collection .hashBag [zero, zero] none

/-- The same closed redex is supplied each candidate stack. -/
def sourceWithStack (stack : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [Synchronous.decoratedRedex (.apply (costWrappedConstructorName "NQuote") [zero])
        localBody zero afterOutput, unitSignature],
      .apply costFundingConstructorName [stack]]

def source : Pattern := sourceWithStack
  (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])

def target : Pattern := .apply costContactConstructorName
  [Synchronous.instantiatedContractum localBody zero afterOutput,
    .apply costFundingConstructorName [retainedTail]]

def wrongHead : Pattern := .apply costSignatureProductConstructorName [unitSignature, unitSignature]
def mismatched : Pattern := sourceWithStack
  (.apply costTokenStackConsConstructorName [wrongHead, retainedTail])

theorem source_typed :
    HasSort Synchronous.communicationDecoration.costWholeRedexLanguage FreeTypeContext.empty []
      source costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem target_typed :
    HasSort Synchronous.communicationDecoration.costWholeRedexLanguage FreeTypeContext.empty []
      target costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem empty_stack_typed :
    HasSort Synchronous.communicationDecoration.costWholeRedexLanguage FreeTypeContext.empty []
      (sourceWithStack emptyStack) costWrappedSortName :=
  checkHasType_sound (by decide +kernel)

theorem mismatched_head_typed :
    HasSort Synchronous.communicationDecoration.costWholeRedexLanguage FreeTypeContext.empty []
      mismatched costWrappedSortName := checkHasType_sound (by decide +kernel)

/-- The executable one-layer matcher has precisely the displayed reduct. -/
theorem reducts_exact :
    rewriteAt (engineBasePremises RelationEnv.empty)
      Synchronous.communicationDecoration.costWholeRedexLanguage 1 source = [target] := by
  decide +kernel

/-- The selected generated rule performs the real matcher substitution and
leaves the second authority cell available in the retained tail. -/
theorem fires : Step (engineBasePremises RelationEnv.empty)
    Synchronous.communicationDecoration.costWholeRedexLanguage source target :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by rw [reducts_exact]; exact List.mem_singleton_self _⟩

theorem empty_stack_no_match :
    matchPatternForRule Synchronous.communicationDecoration.costWholeRedexLanguage
      Synchronous.communicationDecoration.costWholeRedexRewrite
      (sourceWithStack emptyStack) = [] := by
  decide +kernel

theorem mismatched_head_no_match :
    matchPatternForRule Synchronous.communicationDecoration.costWholeRedexLanguage
      Synchronous.communicationDecoration.costWholeRedexRewrite mismatched = [] := by
  decide +kernel

/-- A sorted redex with an empty adjacent stack has no funded step, for any
choice of external premise evaluator. -/
theorem empty_stack_no_step (base : BasePremiseEvaluator) (result : Pattern) :
    ¬ Step base Synchronous.communicationDecoration.costWholeRedexLanguage
      (sourceWithStack emptyStack) result := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have same : rule = Synchronous.communicationDecoration.costWholeRedexRewrite :=
    List.mem_singleton.mp member
  subst rule
  exact empty_stack_no_match

/-- Merely having an adjacent stack head is insufficient: its exact signature
must agree with the signature on the signed redex. -/
theorem mismatched_head_no_step (base : BasePremiseEvaluator) (result : Pattern) :
    ¬ Step base Synchronous.communicationDecoration.costWholeRedexLanguage mismatched result := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have same : rule = Synchronous.communicationDecoration.costWholeRedexRewrite :=
    List.mem_singleton.mp member
  subst rule
  exact mismatched_head_no_match

end FundedSynchronous

end Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls
