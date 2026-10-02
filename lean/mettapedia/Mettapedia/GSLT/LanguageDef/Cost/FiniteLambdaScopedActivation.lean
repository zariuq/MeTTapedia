import Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation
import Mettapedia.GSLT.LanguageDef.Cost.FiniteActivePair
import Mettapedia.GSLT.LanguageDef.Cost.CodeAuthority
import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

/-!
# Funded lambda activation with contextual bodies

Binding metadata is elaborated on the existing authored beta rule and
transported through its finite Cost decoration. The generated patterns are
unchanged. Matching retains the body's local wrapped-variable dependency
separately from the caller's ambient context, then the existing executable
substitution computes the contractum. No ambient-closed body assignment is
required.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaScopedActivation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.Substitution
open WellSorted FiniteLambdaActivation

/-- The ordinary beta body has one declared dependency at both occurrences. -/
def sourceBindingSpec : RuleBindingSpec where
  dependencies := [("body", [.base "Term"]), ("arg", [])]
  occurrences :=
    [{ name := "body", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
     { name := "body", site := .right, path := [0], arguments := [.bvar 0] }]

def sourceAnnotatedRule : RewriteRule :=
  { LambdaContinuedInteraction.lambdaIGSLT.presentation.interactionRewrite.1 with
    bindings := some sourceBindingSpec }

theorem source_binding_admitted : admittedFor sourceAnnotatedRule sourceBindingSpec = true := by
  decide +kernel

theorem source_patterns_preserved :
    sourceAnnotatedRule.left = LambdaContinuedInteraction.lambdaBetaRewrite.1.left ∧
    sourceAnnotatedRule.right = LambdaContinuedInteraction.lambdaBetaRewrite.1.right ∧
    sourceAnnotatedRule.premises = LambdaContinuedInteraction.lambdaBetaRewrite.1.premises :=
  ⟨rfl, rfl, rfl⟩

def bindingSpec : RuleBindingSpec := profile.costActivePairBindingSpec sourceBindingSpec

def rule : RewriteRule := { profile.costActivePairRewrite with bindings := some bindingSpec }

def language : LanguageDef := { profile.costWholeRedexLanguage with rewrites := [rule] }

theorem binding_admitted : admittedFor rule bindingSpec = true := by decide +kernel

theorem generated_patterns_preserved :
    rule.left = profile.costWholeRedexRewrite.left ∧
    rule.right = profile.costWholeRedexRewrite.right ∧
    rule.typeContext = profile.costWholeRedexRewrite.typeContext ∧
    rule.premises = profile.costWholeRedexRewrite.premises := ⟨rfl, rfl, rfl, rfl⟩

theorem language_valid : language.validate = [] := by
  change profile.costWholeRedexLanguage.validate = []
  exact FiniteLambdaActivation.language_valid

/-- Elaborating binding metadata does not change constructor typing. -/
theorem typed_iff_core {free : FreeTypeContext} {ambient : List TypeExpr}
    {term : Pattern} {type : TypeExpr} :
    HasType language free ambient term type ↔ HasType profile.costCoreLanguage free ambient term type :=
  ⟨HasType.weakenTerms (fun _ member => member), HasType.weakenTerms (fun _ member => member)⟩

def assignment (ambient : List TypeExpr) (body argument signature tail : Pattern) : Assignment :=
  [(costAdministrativeSchemaName "stack-tail", ⟨[], ambient.length, tail⟩),
   (costAdministrativeSchemaName "signature", ⟨[], ambient.length, signature⟩),
   (costSourceSchemaName "arg", ⟨[], ambient.length, argument⟩),
   (costSourceSchemaName "body", ⟨[.base costWrappedSortName], ambient.length, body⟩)]

private theorem left_shape : rule.left = fundedSource
    (.fvar (costSourceSchemaName "body")) (.fvar (costSourceSchemaName "arg"))
    (.fvar (costAdministrativeSchemaName "signature"))
    (.apply costTokenStackConsConstructorName
      [.fvar (costAdministrativeSchemaName "signature"),
       .fvar (costAdministrativeSchemaName "stack-tail")]) := rfl

private theorem right_shape : rule.right = .apply costContactConstructorName
    [.subst (.fvar (costSourceSchemaName "body")) (.fvar (costSourceSchemaName "arg")),
     .apply costFundingConstructorName [.fvar (costAdministrativeSchemaName "stack-tail")]] := rfl

/-- All four actual captures, including the one-dependency local body. -/
theorem match_funded_beta (ambient : List TypeExpr) (body argument signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (argumentScoped : argument.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    matchRuleAt rule bindingSpec ambient.length
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) =
      [assignment ambient body argument signature tail] := by
  have bodyRecovery : recoverValue? [.base costWrappedSortName] ambient.length 1 [.bvar 0] body =
      some ⟨[.base costWrappedSortName], ambient.length, body⟩ :=
    RestAwareTyping.recoverValue?_fullSpine _ ambient body bodyScoped
  have deps_body : dependencies? bindingSpec (costSourceSchemaName "body") =
      some [.base costWrappedSortName] := by decide +kernel
  have deps_arg : dependencies? bindingSpec (costSourceSchemaName "arg") = some [] := by decide +kernel
  have deps_sig : dependencies? bindingSpec (costAdministrativeSchemaName "signature") = some [] := by decide +kernel
  have deps_tail : dependencies? bindingSpec (costAdministrativeSchemaName "stack-tail") = some [] := by decide +kernel
  have args_body : arguments? rule bindingSpec (costSourceSchemaName "body") .left
      [0, 0, 0, 0, 0] = some [.bvar 0] := by decide +kernel
  have args_arg : arguments? rule bindingSpec (costSourceSchemaName "arg") .left
      [0, 0, 1] = some [] := by decide +kernel
  have args_sig1 : arguments? rule bindingSpec (costAdministrativeSchemaName "signature") .left
      [0, 1] = some [] := by decide +kernel
  have args_sig2 : arguments? rule bindingSpec (costAdministrativeSchemaName "signature") .left
      [1, 0, 0] = some [] := by decide +kernel
  have args_tail : arguments? rule bindingSpec (costAdministrativeSchemaName "stack-tail") .left
      [1, 0, 1] = some [] := by decide +kernel
  simp only [matchRuleAt, matchRuleWithAt, left_shape]
  simp [fundedSource, betaRedex, abstraction, matchAtWith, matchArgsAtWith, capture?,
    deps_body, deps_arg, deps_sig, deps_tail, args_body, args_arg, args_sig1, args_sig2,
    args_tail, bodyRecovery, RestAwareTyping.recoverValue?_root_empty,
    argumentScoped, signatureScoped, tailScoped, assign, lookup, assignment]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag]

/-- The captured values are instantiated before eliminating beta's binder. -/
theorem reduct_funded_beta (ambient : List TypeExpr) (body argument signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (argumentScoped : argument.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    reduct? rule bindingSpec ambient.length (assignment ambient body argument signature tail) =
      some (fundedTarget body argument tail) := by
  have bodyInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_fullSpine [.base costWrappedSortName] ambient body bodyScoped)
  change instantiateValue? ⟨[.base costWrappedSortName], ambient.length, body⟩
    ambient.length 1 [.bvar 0] = some body at bodyInst
  have argInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length argument argumentScoped)
  have tailInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length tail tailScoped)
  have args_body : arguments? rule bindingSpec (costSourceSchemaName "body") .right
      [0, 0] = some [.bvar 0] := by decide +kernel
  have args_arg : arguments? rule bindingSpec (costSourceSchemaName "arg") .right
      [0, 1] = some [] := by decide +kernel
  have args_tail : arguments? rule bindingSpec (costAdministrativeSchemaName "stack-tail") .right
      [1, 0] = some [] := by decide +kernel
  simp only [reduct?, right_shape]
  simp [instantiateAt?, instantiateWith?, instantiateArgsWith?, lookup, assignment,
    args_body, args_arg, args_tail, fundedTarget]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag] at *
  simp_all

/-- Exact execution for arbitrary local bodies and arbitrary caller contexts. -/
theorem scoped_funded_beta (ambient : List TypeExpr) (body argument signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (argumentScoped : argument.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length rule
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) =
      [fundedTarget body argument tail] := by
  simp only [applyRuleAt, applyRuleWithAt, applyRuleComparedWithAt,
    show rule.bindings = some bindingSpec from rfl, binding_admitted, if_true]
  rw [matchRuleWithAt_literal, match_funded_beta ambient body argument signature tail
    bodyScoped argumentScoped signatureScoped tailScoped]
  have noPremises : rule.premises = [] := rfl
  simp [completeAssignments, noPremises,
    reduct_funded_beta ambient body argument signature tail bodyScoped argumentScoped tailScoped]

/-- The actual executor and the independent constructor typing laws agree
for every typed local body, argument, signature and remaining stack. -/
theorem typed_scoped_funded_beta {free : FreeTypeContext} (ambient : List TypeExpr)
    (body argument signature tail : Pattern)
    (bodyTyped : HasSort language free (.base costWrappedSortName :: ambient) body costWrappedSortName)
    (argumentTyped : HasSort language free ambient argument costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    HasSort language free ambient
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) costWrappedSortName ∧
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length rule
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) =
      [fundedTarget body argument tail] ∧
    HasSort language free ambient (fundedTarget body argument tail) costWrappedSortName := by
  have endpoints := funded_local_beta_typed (typed_iff_core.mp bodyTyped)
    (typed_iff_core.mp argumentTyped) (typed_iff_core.mp signatureTyped) (typed_iff_core.mp tailTyped)
  refine ⟨typed_iff_core.mpr endpoints.1,
    scoped_funded_beta ambient body argument signature tail ?_
      argumentTyped.isWellScopedAt signatureTyped.isWellScopedAt tailTyped.isWellScopedAt,
    typed_iff_core.mpr endpoints.2⟩
  simpa [Nat.add_comm] using bodyTyped.isWellScopedAt

/-- Duplicable code admission, unlike wrapped typing alone, excludes purse
authority from the whole activated body. The actual execution still returns
exactly the supplied external stack tail. -/
theorem typed_code_scoped_funded_beta {free : FreeTypeContext} (ambient : List TypeExpr)
    (body argument signature tail : Pattern)
    (bodyTyped : HasSort language free (.base costWrappedSortName :: ambient) body costWrappedSortName)
    (argumentTyped : HasSort language free ambient argument costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName)
    (bodyCode : CurrentLayerCode body) (argumentCode : CurrentLayerCode argument) :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length rule
      (fundedSource body argument signature
        (.apply costTokenStackConsConstructorName [signature, tail])) =
      [fundedTarget body argument tail] ∧
    HasSort language free ambient (fundedTarget body argument tail) costWrappedSortName ∧
    CurrentLayerCode (instantiateBVar argument body) := by
  have checked := typed_scoped_funded_beta ambient body argument signature tail
    bodyTyped argumentTyped signatureTyped tailTyped
  exact ⟨checked.2.1, checked.2.2, bodyCode.instantiateBVarAt argumentCode 0⟩

/-- The generated beta rule participates in the language's real scoped
rewrite enumeration, rather than merely being passed to a rule evaluator. -/
theorem scoped_language_firing (ambient : List TypeExpr) (body argument signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (argumentScoped : argument.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    fundedTarget body argument tail ∈
      rewriteStepAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length
        (fundedSource body argument signature
          (.apply costTokenStackConsConstructorName [signature, tail])) := by
  apply (mem_rewriteStepAt_iff _ _ _ _ _).mpr
  refine ⟨rule, by simp [language], ?_⟩
  rw [scoped_funded_beta ambient body argument signature tail
    bodyScoped argumentScoped signatureScoped tailScoped]
  exact List.mem_singleton_self _

/-- The body refers past beta's local variable to the caller's variable.
The caller's index survives binder elimination without capture. -/
theorem ambient_body_preserved :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language 1 rule
      (fundedSource (.bvar 1) identityArgument unitSignature
        (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])) =
      [.apply costContactConstructorName [.bvar 0, .apply costFundingConstructorName [retainedTail]]] := by
  simpa [fundedTarget, instantiateBVar, instantiateBVarAt] using
    scoped_funded_beta [.base costWrappedSortName] (.bvar 1) identityArgument
      unitSignature retainedTail (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- Duplicating signed code does not duplicate the outer purse or its tail. -/
theorem duplicated_code_single_purse :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language 0 rule
      (fundedSource (.apply costContactConstructorName [.bvar 0, .bvar 0])
        identityArgument unitSignature
        (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])) =
      [.apply costContactConstructorName
        [.apply costContactConstructorName [identityArgument, identityArgument],
         .apply costFundingConstructorName [retainedTail]]] := by
  decide +kernel

/-- A signed argument containing a beta redex is discarded by a body using
only the caller's variable. It causes no additional purse consumption. -/
def unevaluatedArgument : Pattern := .apply costSignedConstructorName
  [betaRedex (.bvar 0) identityArgument, unitSignature]

theorem discarded_redex_is_not_executed :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language 1 rule
      (fundedSource (.bvar 1) unevaluatedArgument unitSignature
        (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])) =
      [.apply costContactConstructorName [.bvar 0, .apply costFundingConstructorName [retainedTail]]] := by
  decide +kernel

theorem controls_are_typed :
    HasSort language FreeTypeContext.empty [.base costWrappedSortName]
      (fundedSource (.bvar 1) unevaluatedArgument unitSignature
        (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])) costWrappedSortName ∧
    HasSort language FreeTypeContext.empty []
      (fundedSource (.apply costContactConstructorName [.bvar 0, .bvar 0])
        identityArgument unitSignature
        (.apply costTokenStackConsConstructorName [unitSignature, retainedTail])) costWrappedSortName := by
  constructor <;> exact checkHasType_sound (by decide +kernel)

theorem missing_or_different_purse_rejected :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language 0 rule
      unfundedIdentity = [] ∧
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language 0 rule
      mismatchedIdentity = [] := by
  constructor <;> decide +kernel

end Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaScopedActivation
