import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePair

/-!
# Scoped matching for the funded synchronous active pair

The declared input dependency is retained separately from arbitrary ambient
variables. These results concern the existing syntactic scoped matcher.
Reflective channel equality and reflective substitution remain a separate
interpretation; no equality of the two interpreters is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePair

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- The source contains exactly the selected pair, with identical channels
and signature occurrences. Payloads may contain ambient bound variables. -/
def fundedPair (channel body sent after signature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [decoratedRedex channel body sent after, signature],
      .apply costFundingConstructorName
        [.apply costTokenStackConsConstructorName [signature, tail]]]

def fundedResidual (body sent after tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [instantiatedContractum body sent after,
      .apply costFundingConstructorName [tail]]

private theorem left_shape : rule.left = fundedPair
    (.fvar (costSourceSchemaName "n")) (.fvar (costSourceSchemaName "p"))
    (.fvar (costSourceSchemaName "q")) (.fvar (costSourceSchemaName "k"))
    (.fvar (costAdministrativeSchemaName "signature"))
    (.fvar (costAdministrativeSchemaName "stack-tail")) := rfl

/-- This is the exact assignment order produced by the existing matcher. -/
def pairAssignment (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern) : Assignment :=
  [(costAdministrativeSchemaName "stack-tail", ⟨[], ambient.length, tail⟩),
   (costAdministrativeSchemaName "signature", ⟨[], ambient.length, signature⟩),
   (costSourceSchemaName "k", ⟨[], ambient.length, after⟩),
   (costSourceSchemaName "q", ⟨[], ambient.length, sent⟩),
   (costSourceSchemaName "p", ⟨[.base (costBaseSortName "Name")], ambient.length, body⟩),
   (costSourceSchemaName "n", ⟨[], ambient.length, channel⟩)]

/-- Matching captures the actual local input body and all ambient payloads,
without representing the body by an ambient-closed assignment. -/
theorem scoped_match_pair (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelScoped : channel.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    matchRuleAt rule bindingSpec ambient.length
      (fundedPair channel body sent after signature tail) =
      [pairAssignment ambient channel body sent after signature tail] := by
  have bodyRecovery : recoverValue? [.base (costBaseSortName "Name")]
      ambient.length 1 [.bvar 0] body =
      some ⟨[.base (costBaseSortName "Name")], ambient.length, body⟩ :=
    RestAwareTyping.recoverValue?_fullSpine _ ambient body bodyScoped
  have deps_n : dependencies? bindingSpec (costSourceSchemaName "n") = some [] := by decide +kernel
  have deps_p : dependencies? bindingSpec (costSourceSchemaName "p") = some [.base (costBaseSortName "Name")] := by decide +kernel
  have deps_q : dependencies? bindingSpec (costSourceSchemaName "q") = some [] := by decide +kernel
  have deps_k : dependencies? bindingSpec (costSourceSchemaName "k") = some [] := by decide +kernel
  have deps_sig : dependencies? bindingSpec (costAdministrativeSchemaName "signature") = some [] := by decide +kernel
  have deps_tail : dependencies? bindingSpec (costAdministrativeSchemaName "stack-tail") = some [] := by decide +kernel
  have args_n1 : arguments? rule bindingSpec (costSourceSchemaName "n") .left [0, 0, 0, 0] = some [] := by decide +kernel
  have args_p : arguments? rule bindingSpec (costSourceSchemaName "p") .left [0, 0, 0, 1, 0] = some [.bvar 0] := by decide +kernel
  have args_n2 : arguments? rule bindingSpec (costSourceSchemaName "n") .left [0, 0, 1, 0] = some [] := by decide +kernel
  have args_q : arguments? rule bindingSpec (costSourceSchemaName "q") .left [0, 0, 1, 1] = some [] := by decide +kernel
  have args_k : arguments? rule bindingSpec (costSourceSchemaName "k") .left [0, 0, 1, 2] = some [] := by decide +kernel
  have args_sig1 : arguments? rule bindingSpec (costAdministrativeSchemaName "signature") .left [0, 1] = some [] := by decide +kernel
  have args_sig2 : arguments? rule bindingSpec (costAdministrativeSchemaName "signature") .left [1, 0, 0] = some [] := by decide +kernel
  have args_tail : arguments? rule bindingSpec (costAdministrativeSchemaName "stack-tail") .left [1, 0, 1] = some [] := by decide +kernel
  simp only [matchRuleAt, matchRuleWithAt, left_shape]
  simp [fundedPair, decoratedRedex, matchAtWith, matchArgsAtWith, matchBagAtWith,
    capture?, deps_n, deps_p, deps_q, deps_k, deps_sig, deps_tail,
    args_n1, args_p, args_n2, args_q, args_k, args_sig1, args_sig2, args_tail,
    bodyRecovery, RestAwareTyping.recoverValue?_root_empty,
    channelScoped, sentScoped, afterScoped, signatureScoped, tailScoped,
    assign, lookup, pairAssignment]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag, costBaseConstructorName]

private theorem right_shape : rule.right =
    .apply costContactConstructorName
      [.collection .hashBag
        [.subst (.fvar (costSourceSchemaName "p"))
          (.apply (costWrappedConstructorName "NQuote") [.fvar (costSourceSchemaName "q")]),
         .fvar (costSourceSchemaName "k")] none,
       .apply costFundingConstructorName [.fvar (costAdministrativeSchemaName "stack-tail")]] := rfl

/-- Every occurrence is instantiated from its retained context; only then
is the source's explicit substitution node evaluated. -/
theorem scoped_reduct_pair (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    reduct? rule bindingSpec ambient.length
      (pairAssignment ambient channel body sent after signature tail) =
      some (fundedResidual body sent after tail) := by
  have bodyRecovery : recoverValue? [.base (costBaseSortName "Name")]
      ambient.length 1 [.bvar 0] body =
      some ⟨[.base (costBaseSortName "Name")], ambient.length, body⟩ :=
    RestAwareTyping.recoverValue?_fullSpine _ ambient body bodyScoped
  have bodyInst := recoverValue?_forward _ _ _ _ _ _ bodyRecovery
  have sentInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length sent sentScoped)
  have afterInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length after afterScoped)
  have tailInst := recoverValue?_forward _ _ _ _ _ _
    (RestAwareTyping.recoverValue?_root_empty ambient.length tail tailScoped)
  have args_p : arguments? rule bindingSpec (costSourceSchemaName "p") .right
      [0, 0, 0] = some [.bvar 0] := by decide +kernel
  have args_q : arguments? rule bindingSpec (costSourceSchemaName "q") .right
      [0, 0, 1, 0] = some [] := by decide +kernel
  have args_k : arguments? rule bindingSpec (costSourceSchemaName "k") .right
      [0, 1] = some [] := by decide +kernel
  have args_tail : arguments? rule bindingSpec (costAdministrativeSchemaName "stack-tail") .right
      [1, 0] = some [] := by decide +kernel
  simp only [reduct?, right_shape]
  simp [instantiateAt?, instantiateWith?, instantiateArgsWith?, lookup, pairAssignment,
    args_p, args_q, args_k, args_tail, tailInst,
    fundedResidual, instantiatedContractum]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag] at *
  simp_all

/-- Actual scoped execution of every well-scoped funded pair. The input
body can depend on its local name and on the caller's whole ambient context. -/
theorem scoped_firing_pair (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelScoped : channel.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length rule
      (fundedPair channel body sent after signature tail) =
      [fundedResidual body sent after tail] := by
  simp only [applyRuleAt, applyRuleWithAt, applyRuleComparedWithAt, show rule.bindings = some bindingSpec from rfl,
    binding_admitted, if_true]
  rw [matchRuleWithAt_literal, scoped_match_pair ambient channel body sent after signature tail
    channelScoped bodyScoped sentScoped afterScoped signatureScoped tailScoped]
  have noPremises : rule.premises = [] := rfl
  simp [completeAssignments, noPremises,
    scoped_reduct_pair ambient channel body sent after signature tail
      bodyScoped sentScoped afterScoped tailScoped]

/-- Every payload is typed where the authored constructor places it;
the input body has one additional name binder. -/
theorem fundedPair_typed {free : FreeTypeContext} {ambient : List TypeExpr}
    {channel body sent after signature tail : Pattern}
    (channelTyped : HasSort language free ambient channel (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    HasSort language free ambient (fundedPair channel body sent after signature tail)
      costWrappedSortName := by
  have redexTyped : HasSort language free ambient
      (decoratedRedex channel body sent after) (costBaseSortName "Proc") := by
    apply HasType.collectionConstructor
      (rule := communicationDecoration.baseConstructor rhoCalc.terms[3])
      (parameterName := "ps") (elementType := .base (costBaseSortName "Proc"))
    · decide +kernel
    · exact communicationDecoration_parallel_parameters
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := communicationDecoration.baseConstructor rhoCalc.terms[5])
        · decide +kernel
        · simp [UsesBareCollection, communicationDecoration_input_parameters]
        · rw [communicationDecoration_input_parameters]
          exact .cons trivial rfl channelTyped (.cons trivial rfl (.lambda bodyTyped) .nil)
      · apply ElementsHaveType.cons
        · apply HasType.constructor
            (rule := communicationDecoration.baseConstructor rhoSyncOutputRule)
          · decide +kernel
          · simp [UsesBareCollection, communicationDecoration_output_parameters]
          · rw [communicationDecoration_output_parameters]
            exact .cons trivial rfl channelTyped
              (.cons trivial rfl sentTyped (.cons trivial rfl afterTyped .nil))
        · exact .nil _ _
  exact CostApparatus.contact_hasType (by decide +kernel)
    (CostApparatus.signed_hasType (by decide +kernel) redexTyped signatureTyped)
    (CostApparatus.funding_hasType (by decide +kernel)
      (CostApparatus.stackCons_hasType (by decide +kernel) signatureTyped tailTyped))

/-- Actual binder substitution preserves the wrapped result sort in the
corrected language, including apparatus-bearing payloads. -/
theorem fundedResidual_typed {free : FreeTypeContext} {ambient : List TypeExpr}
    {body sent after tail : Pattern}
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    HasSort language free ambient (fundedResidual body sent after tail) costWrappedSortName := by
  have quoteTyped : HasSort language free ambient
      (.apply (costWrappedConstructorName "NQuote") [sent]) (costBaseSortName "Name") := by
    apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2])
    · decide +kernel
    · simp [UsesBareCollection, rhoSync_costWrappedQuote_params]
    · rw [rhoSync_costWrappedQuote_params]
      exact .cons trivial rfl sentTyped .nil
  have payloadTyped : HasSort language free ambient
      (instantiatedContractum body sent after) costWrappedSortName := by
    apply HasType.collectionConstructor
      (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3])
      (parameterName := "ps") (elementType := .base costWrappedSortName)
    · decide +kernel
    · rfl
    · exact .cons (bodyTyped.instantiateBVar quoteTyped) (.cons afterTyped (.nil _ _))
  exact CostApparatus.contact_hasType (by decide +kernel) payloadTyped
    (CostApparatus.funding_hasType (by decide +kernel) tailTyped)

/-- A scoped matcher step and its sorted result follow from local payload
judgments. No closed free-variable assignment stands in for the binder. -/
theorem typed_scoped_firing_pair {free : FreeTypeContext} (ambient : List TypeExpr)
    (channel body sent after signature tail : Pattern)
    (channelTyped : HasSort language free ambient channel (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language ambient.length rule
      (fundedPair channel body sent after signature tail) =
      [fundedResidual body sent after tail] ∧
    HasSort language free ambient (fundedResidual body sent after tail) costWrappedSortName := by
  refine ⟨scoped_firing_pair ambient channel body sent after signature tail
    channelTyped.isWellScopedAt ?_ sentTyped.isWellScopedAt afterTyped.isWellScopedAt
    signatureTyped.isWellScopedAt tailTyped.isWellScopedAt,
    fundedResidual_typed bodyTyped sentTyped afterTyped tailTyped⟩
  simpa [Nat.add_comm] using bodyTyped.isWellScopedAt

/-- This body uses both the local input name and an ambient name. -/
def openBody : Pattern := .collection .hashBag
  [.apply (costWrappedConstructorName "PDrop") [.bvar 0],
   .apply (costWrappedConstructorName "PDrop") [.bvar 1]] none

def openSource : Pattern := fundedPair FiniteWhole.canonicalChannel openBody
  FiniteWhole.zero FiniteWhole.zero FiniteWhole.unitSignature FiniteWhole.retainedTail

def openTarget : Pattern := fundedResidual openBody FiniteWhole.zero
  FiniteWhole.zero FiniteWhole.retainedTail

theorem open_source_typed : HasSort language FreeTypeContext.empty
    [.base (costBaseSortName "Name")] openSource costWrappedSortName :=
  checkHasType_sound (by decide +kernel)

theorem open_target_typed : HasSort language FreeTypeContext.empty
    [.base (costBaseSortName "Name")] openTarget costWrappedSortName :=
  checkHasType_sound (by decide +kernel)

theorem open_scoped_firing : applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
    language 1 rule openSource = [openTarget] := by decide +kernel

/-- The ambient name cannot be silently captured as the input-local name. -/
theorem absent_ambient_rejected : applyRuleAt Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
    language 0 rule openSource = [] := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePair
