import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionValidation
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Binder-local activation in the finite Cost lambda calculus

Beta's input body is typed below its own wrapped-variable binder, while its
argument is typed in the ambient context.  Actual binder elimination preserves
the wrapped result sort.  A funded identity application exercises the ordinary
rule matcher with precisely this local body, which cannot be represented as an
ambient-closed free-variable assignment image.

The generated language is the selected beta fragment.  The results do not
assert arbitrary contextual reduction or identify structural free-variable
substitution with the runtime matcher.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.LambdaInstance
open LambdaContinuedInteraction WellSorted

abbrev profile := ContinuationDecorationProfile.ofRetypingPlan lambdaContinuationRetyping

theorem language_valid : profile.costWholeRedexLanguage.validate = [] :=
  profile.costWholeRedexLanguage_validate lambdaContinuationRetyping.noDuplicates
    ((ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      lambdaContinuationRetyping_redexRetypable)
    ((ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr
      lambdaContinuationRetyping_wrappable)

def abstraction (body : Pattern) : Pattern :=
  .apply (costBaseConstructorName "Lam") [.lambda none body]

def betaRedex (body argument : Pattern) : Pattern :=
  .apply (costBaseConstructorName "App") [abstraction body, argument]

private theorem abstraction_parameters :
    (profile.baseConstructor lambdaCalc.terms[1]).params =
      [.abstraction "body"
        (.arrow (.base costWrappedSortName) (.base costWrappedSortName))] := by
  simpa only [profile, ContinuationDecorationProfile.ofRetypingPlan_baseConstructor]
    using lambda_costBaseAbstraction_params

private theorem application_parameters :
    (profile.baseConstructor lambdaCalc.terms[0]).params =
      [.simple "f" (.base (costBaseSortName "Term")),
        .simple "a" (.base costWrappedSortName)] := by
  simpa only [profile, ContinuationDecorationProfile.ofRetypingPlan_baseConstructor]
    using lambda_costBaseApplication_params

theorem abstraction_typed {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (bodyTyped : HasSort profile.costCoreLanguage free
      (.base costWrappedSortName :: bound) body costWrappedSortName) :
    HasSort profile.costCoreLanguage free bound (abstraction body) (costBaseSortName "Term") := by
  apply HasType.constructor (rule := profile.baseConstructor lambdaCalc.terms[1])
  · exact List.mem_append_left _ (profile.baseConstructor_mem _ lambdaAbstractionConstructor.2)
  · simp [UsesBareCollection]
  · rw [abstraction_parameters]
    exact .cons trivial rfl (.lambda bodyTyped) .nil

theorem betaRedex_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {body argument : Pattern}
    (bodyTyped : HasSort profile.costCoreLanguage free
      (.base costWrappedSortName :: bound) body costWrappedSortName)
    (argumentTyped : HasSort profile.costCoreLanguage free bound argument costWrappedSortName) :
    HasSort profile.costCoreLanguage free bound (betaRedex body argument)
      (costBaseSortName "Term") := by
  apply HasType.constructor (rule := profile.baseConstructor lambdaCalc.terms[0])
  · exact List.mem_append_left _ (profile.baseConstructor_mem _ lambdaApplicationConstructor.2)
  · simp [UsesBareCollection]
  · rw [application_parameters]
    exact .cons trivial rfl (abstraction_typed bodyTyped)
      (.cons trivial rfl argumentTyped .nil)

/-- This uses the actual binder-eliminating substitution and admits arbitrary
ambient contexts, including arguments containing ambient variables. -/
theorem activatedContractum_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {body argument : Pattern}
    (bodyTyped : HasSort profile.costCoreLanguage free
      (.base costWrappedSortName :: bound) body costWrappedSortName)
    (argumentTyped : HasSort profile.costCoreLanguage free bound argument costWrappedSortName) :
    HasSort profile.costCoreLanguage free bound
      (instantiateBVar argument body) costWrappedSortName :=
  bodyTyped.instantiateBVar argumentTyped

def fundedSource (body argument signature stack : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName [betaRedex body argument, signature],
      .apply costFundingConstructorName [stack]]

def fundedTarget (body argument tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [instantiateBVar argument body, .apply costFundingConstructorName [tail]]

/-- Sorted local continuations and exact signature/stack inputs suffice to
type both sides of the funded beta instance, with its local binder retained. -/
theorem funded_local_beta_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {body argument signature tail : Pattern}
    (bodyTyped : HasSort profile.costCoreLanguage free
      (.base costWrappedSortName :: bound) body costWrappedSortName)
    (argumentTyped : HasSort profile.costCoreLanguage free bound argument costWrappedSortName)
    (signatureTyped : HasSort profile.costCoreLanguage free bound signature costSignatureSortName)
    (tailTyped : HasSort profile.costCoreLanguage free bound tail costTokenStackSortName) :
    HasSort profile.costCoreLanguage free bound
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) costWrappedSortName ∧
    HasSort profile.costCoreLanguage free bound
      (fundedTarget body argument tail) costWrappedSortName := by
  have declared := profile.apparatus_mem_costCore
  constructor
  · exact CostApparatus.contact_hasType (declared _ (by simp [costCoreConstructors]))
      (CostApparatus.signed_hasType (declared _ (by
          change costSignedConstructor "Term" ∈ costCoreConstructors "Term"
          simp [costCoreConstructors]))
        (betaRedex_typed bodyTyped argumentTyped) signatureTyped)
      (CostApparatus.funding_hasType (declared _ (by simp [costCoreConstructors]))
        (CostApparatus.stackCons_hasType (declared _ (by simp [costCoreConstructors]))
          signatureTyped tailTyped))
  · exact CostApparatus.contact_hasType (declared _ (by simp [costCoreConstructors]))
      (activatedContractum_typed bodyTyped argumentTyped)
      (CostApparatus.funding_hasType (declared _ (by simp [costCoreConstructors])) tailTyped)

def unitSignature : Pattern := .apply costSignatureUnitConstructorName []
def emptyStack : Pattern := .apply costTokenStackEmptyConstructorName []
def retainedTail : Pattern := .apply costTokenStackConsConstructorName [unitSignature, emptyStack]

/-- A signed, binder-containing identity abstraction is a closed wrapped
argument.  Its body really uses its local wrapped-variable binder. -/
def identityArgument : Pattern :=
  .apply costSignedConstructorName [abstraction (.bvar 0), unitSignature]

def identitySource : Pattern := fundedSource (.bvar 0) identityArgument unitSignature
  (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])

def identityTarget : Pattern := fundedTarget (.bvar 0) identityArgument retainedTail

def unfundedIdentity : Pattern := fundedSource (.bvar 0) identityArgument unitSignature emptyStack

def mismatchedIdentity : Pattern := fundedSource (.bvar 0) identityArgument unitSignature
  (.apply costTokenStackConsConstructorName
    [.apply costSignatureProductConstructorName [unitSignature, unitSignature], retainedTail])

theorem identity_source_typed : HasSort profile.costWholeRedexLanguage FreeTypeContext.empty []
    identitySource costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem identity_target_typed : HasSort profile.costWholeRedexLanguage FreeTypeContext.empty []
    identityTarget costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem unfunded_identity_typed : HasSort profile.costWholeRedexLanguage FreeTypeContext.empty []
    unfundedIdentity costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem mismatched_identity_typed : HasSort profile.costWholeRedexLanguage FreeTypeContext.empty []
    mismatchedIdentity costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem identity_target_eq : identityTarget =
    .apply costContactConstructorName
      [identityArgument, .apply costFundingConstructorName [retainedTail]] := by
  decide +kernel

theorem identity_reducts_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) profile.costWholeRedexLanguage 1
      identitySource = [identityTarget] := by
  decide +kernel

theorem funded_identity_fires : Step (engineBasePremises RelationEnv.empty)
    profile.costWholeRedexLanguage identitySource identityTarget :=
  exists_mem_rewriteAt_iff_step.mp
    ⟨1, by rw [identity_reducts_exact]; exact List.mem_singleton_self _⟩

theorem unfunded_identity_no_step (base : BasePremiseEvaluator) (result : Pattern) :
    ¬ Step base profile.costWholeRedexLanguage unfundedIdentity result := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  obtain rfl := List.mem_singleton.mp member
  decide +kernel

theorem mismatched_identity_no_step (base : BasePremiseEvaluator) (result : Pattern) :
    ¬ Step base profile.costWholeRedexLanguage mismatchedIdentity result := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  obtain rfl := List.mem_singleton.mp member
  decide +kernel

/-- This input body is admitted in its local context. -/
theorem identity_body_local : HasSort profile.costCoreLanguage FreeTypeContext.empty
    [.base costWrappedSortName] (.bvar 0) costWrappedSortName :=
  .bvar rfl

theorem identity_body_not_ambient_closed : ¬ HasSort profile.costCoreLanguage
    FreeTypeContext.empty [] (.bvar 0) costWrappedSortName := by
  intro typed
  cases typed with
  | bvar lookup => cases lookup

theorem body_variable_lookup :
    profile.costWholeRedexFreeContext (costSourceSchemaName "body") =
      some (.base costWrappedSortName) := by
  decide +kernel

/-- A globally typed free-variable assignment cannot represent this valid
binder-local match.  Its image would have to type the local index at depth zero. -/
theorem local_body_not_closed_assignment
    (assignment : TypedAssignment profile.costCoreLanguage
      profile.costWholeRedexFreeContext FreeTypeContext.empty []) :
    assignment.assignment (costSourceSchemaName "body") ≠ .bvar 0 := by
  intro same
  have typed := assignment.typed body_variable_lookup
  rw [same] at typed
  exact identity_body_not_ambient_closed typed

#print axioms language_valid
#print axioms funded_local_beta_typed
#print axioms funded_identity_fires
#print axioms unfunded_identity_no_step
#print axioms mismatched_identity_no_step
#print axioms local_body_not_closed_assignment

end Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation
