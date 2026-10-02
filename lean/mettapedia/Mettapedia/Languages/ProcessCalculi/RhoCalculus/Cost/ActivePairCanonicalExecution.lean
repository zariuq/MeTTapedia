import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairNameComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairReflectionTyping

/-!
# Canonical channel matching in the funded scoped COMM interpreter

The existing authored rule captures the receiver's raw name, checks the sender
using the source-selected name comparison, and retains all contextual values.
The channel dependency spine is empty. This result does not establish
canonical naturality for nonempty spines or literal quotation sealing of an
open received payload. Signature observations remain exact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairCanonicalExecution

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching
open ActivePair (rule bindingSpec language pairAssignment)
open ActivePairReflectionTyping (residual)

abbrev profile := ActivePair.presentation.reflection.1

/-- Receiver and sender may have distinct spellings; neither capture is
normalized before occurrence recovery. -/
def fundedPairChannels (receiver sender body sent after signature tail : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.collection .hashBag
        [.apply (costBaseConstructorName "PInput") [receiver, .lambda none body],
         .apply (costBaseConstructorName "POutputK") [sender, sent, after]] none,
       signature],
     .apply costFundingConstructorName
       [.apply costTokenStackConsConstructorName [signature, tail]]]

theorem fundedPairChannels_same (channel body sent after signature tail : Pattern) :
    fundedPairChannels channel channel body sent after signature tail =
      ActivePair.fundedPair channel body sent after signature tail := rfl

private theorem left_shape : rule.left = fundedPairChannels
    (.fvar (costSourceSchemaName "n")) (.fvar (costSourceSchemaName "n"))
    (.fvar (costSourceSchemaName "p")) (.fvar (costSourceSchemaName "q"))
    (.fvar (costSourceSchemaName "k"))
    (.fvar (costAdministrativeSchemaName "signature"))
    (.fvar (costAdministrativeSchemaName "stack-tail")) := rfl

/-- The actual finite pair has one matching assignment precisely when its
repeated channel body is accepted. Its first raw receiver capture survives. -/
theorem compared_match_pair (compare : String → Pattern → Pattern → Bool)
    (ambient : List TypeExpr) (receiver sender body sent after signature tail : Pattern)
    (signatureAccepted : compare (costAdministrativeSchemaName "signature") signature signature = true)
    (receiverScoped : receiver.isWellScopedAt ambient.length = true)
    (senderScoped : sender.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    matchRuleWithAt compare rule bindingSpec ambient.length
      (fundedPairChannels receiver sender body sent after signature tail) =
      if compare (costSourceSchemaName "n") receiver sender then
        [pairAssignment ambient receiver body sent after signature tail]
      else [] := by
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
  simp only [matchRuleWithAt, left_shape]
  simp [fundedPairChannels, matchAtWith, matchArgsAtWith, matchBagAtWith,
    captureWith?, deps_n, deps_p, deps_q, deps_k, deps_sig, deps_tail,
    args_n1, args_p, args_n2, args_q, args_k, args_sig1, args_sig2, args_tail,
    bodyRecovery, RestAwareTyping.recoverValue?_root_empty,
    receiverScoped, senderScoped, sentScoped, afterScoped, signatureScoped, tailScoped,
    assignWith, lookup, pairAssignment]
  simp [costSourceSchemaName, costSourceSchemaTag, costAdministrativeSchemaName,
    costAdministrativeSchemaTag, costBaseConstructorName] at *
  split <;> simp_all

/-- The authored profile compares only the repeated name body canonically;
all metadata checks and the first assignment remain unchanged. -/
theorem scoped_match_pair (ambient : List TypeExpr)
    (receiver sender body sent after signature tail : Pattern)
    (channelsAccepted : ScopedReflectiveComparison.bodyComparison profile rule
      (costSourceSchemaName "n") receiver sender = true)
    (receiverScoped : receiver.isWellScopedAt ambient.length = true)
    (senderScoped : sender.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    matchRuleWithAt (ScopedReflectiveComparison.bodyComparison profile rule)
      rule bindingSpec ambient.length
      (fundedPairChannels receiver sender body sent after signature tail) =
      [pairAssignment ambient receiver body sent after signature tail] := by
  rw [compared_match_pair _ ambient receiver sender body sent after signature tail
    (ScopedReflectiveComparison.bodyComparison_refl _ _ _ _)
    receiverScoped senderScoped bodyScoped sentScoped afterScoped signatureScoped tailScoped,
    channelsAccepted]
  rfl

/-- Actual source-selected matching and source-selected binder activation
release the retained body, payload and output continuation in the ambient context. -/
theorem canonical_firing_pair (ambient : List TypeExpr)
    (receiver sender body sent after signature tail : Pattern)
    (channelsAccepted : ScopedReflectiveComparison.bodyComparison profile rule
      (costSourceSchemaName "n") receiver sender = true)
    (receiverScoped : receiver.isWellScopedAt ambient.length = true)
    (senderScoped : sender.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language ambient.length rule
      (fundedPairChannels receiver sender body sent after signature tail) =
      [residual body sent after tail] := by
  simp only [ScopedReflectiveExecution.applyRuleCanonicalAt,
    ScopedRuleExecution.applyRuleComparedWithAt,
    show rule.bindings = some bindingSpec from rfl, ActivePair.binding_admitted, if_true]
  rw [scoped_match_pair ambient receiver sender body sent after signature tail
    channelsAccepted receiverScoped senderScoped bodyScoped sentScoped afterScoped
    signatureScoped tailScoped]
  have noPremises : rule.premises = [] := rfl
  have selected : ScopedReflectiveExecution.binderOperation profile rule =
      ActivePairContextualReflection.operation := rfl
  simp [ScopedRuleExecution.completeAssignments, noPremises, selected,
    ActivePairReflectionTyping.reduct_pair ambient receiver body sent after signature tail
      bodyScoped sentScoped afterScoped tailScoped]

/-- Literal matching rejects distinct channel trees before either binder
operation or premise execution can change the result. -/
theorem literal_firing_rejected (operation : Pattern → Pattern → Pattern)
    (ambient : List TypeExpr) (receiver sender body sent after signature tail : Pattern)
    (different : receiver ≠ sender)
    (receiverScoped : receiver.isWellScopedAt ambient.length = true)
    (senderScoped : sender.isWellScopedAt ambient.length = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient.length) = true)
    (sentScoped : sent.isWellScopedAt ambient.length = true)
    (afterScoped : after.isWellScopedAt ambient.length = true)
    (signatureScoped : signature.isWellScopedAt ambient.length = true)
    (tailScoped : tail.isWellScopedAt ambient.length = true) :
    ScopedRuleExecution.applyRuleWithAt operation Engine.RelationEnv.empty
      language ambient.length rule
      (fundedPairChannels receiver sender body sent after signature tail) = [] := by
  simp only [ScopedRuleExecution.applyRuleWithAt,
    ScopedRuleExecution.applyRuleComparedWithAt,
    show rule.bindings = some bindingSpec from rfl, ActivePair.binding_admitted, if_true]
  rw [compared_match_pair _ ambient receiver sender body sent after signature tail
    (show literalBodyComparison _ signature signature = true by simp [literalBodyComparison])
    receiverScoped senderScoped bodyScoped sentScoped afterScoped signatureScoped tailScoped]
  simp [literalBodyComparison, different]

/-- Both channel spellings occupy their actual source-declared Name slots. -/
theorem fundedPairChannels_typed {free : FreeTypeContext} {ambient : List TypeExpr}
    {receiver sender body sent after signature tail : Pattern}
    (receiverTyped : HasSort language free ambient receiver (costBaseSortName "Name"))
    (senderTyped : HasSort language free ambient sender (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    HasSort language free ambient
      (fundedPairChannels receiver sender body sent after signature tail)
      costWrappedSortName := by
  have redexTyped : HasSort language free ambient
      (.collection .hashBag
        [.apply (costBaseConstructorName "PInput") [receiver, .lambda none body],
         .apply (costBaseConstructorName "POutputK") [sender, sent, after]] none)
      (costBaseSortName "Proc") := by
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
          exact .cons trivial rfl receiverTyped (.cons trivial rfl (.lambda bodyTyped) .nil)
      · apply ElementsHaveType.cons
        · apply HasType.constructor
            (rule := communicationDecoration.baseConstructor rhoSyncOutputRule)
          · decide +kernel
          · simp [UsesBareCollection, communicationDecoration_output_parameters]
          · rw [communicationDecoration_output_parameters]
            exact .cons trivial rfl senderTyped
              (.cons trivial rfl sentTyped (.cons trivial rfl afterTyped .nil))
        · exact .nil _ _
  exact CostApparatus.contact_hasType (by decide +kernel)
    (CostApparatus.signed_hasType (by decide +kernel) redexTyped signatureTyped)
    (CostApparatus.funding_hasType (by decide +kernel)
      (CostApparatus.stackCons_hasType (by decide +kernel) signatureTyped tailTyped))

/-- Actual canonical firing and ordinary typing of both endpoints. The
input body's object/name and quotation-admission premises are explicit;
there is no claim that an open received quotation becomes sealed. -/
theorem canonical_typed_firing {free : FreeTypeContext} (ambient : List TypeExpr)
    (receiver sender body sent after signature tail : Pattern)
    (channelsAccepted : ScopedReflectiveComparison.bodyComparison profile rule
      (costSourceSchemaName "n") receiver sender = true)
    (receiverTyped : HasSort language free ambient receiver (costBaseSortName "Name"))
    (senderTyped : HasSort language free ambient sender (costBaseSortName "Name"))
    (bodyTyped : HasSort language free (.base (costBaseSortName "Name") :: ambient)
      body costWrappedSortName)
    (bodyObject : isObjectPattern body = true)
    (bodySealed : ReflectiveWellSorted.ReflectiveScopeSafeAt profile
      (.base (costBaseSortName "Name") :: ambient).length body)
    (sentTyped : HasSort language free ambient sent costWrappedSortName)
    (afterTyped : HasSort language free ambient after costWrappedSortName)
    (signatureTyped : HasSort language free ambient signature costSignatureSortName)
    (tailTyped : HasSort language free ambient tail costTokenStackSortName) :
    HasSort language free ambient
      (fundedPairChannels receiver sender body sent after signature tail) costWrappedSortName ∧
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language ambient.length rule
      (fundedPairChannels receiver sender body sent after signature tail) =
      [residual body sent after tail] ∧
    HasSort language free ambient (residual body sent after tail) costWrappedSortName := by
  refine ⟨fundedPairChannels_typed receiverTyped senderTyped bodyTyped sentTyped afterTyped
    signatureTyped tailTyped, canonical_firing_pair ambient receiver sender body sent after
      signature tail channelsAccepted receiverTyped.isWellScopedAt senderTyped.isWellScopedAt
      ?_ sentTyped.isWellScopedAt afterTyped.isWellScopedAt signatureTyped.isWellScopedAt
      tailTyped.isWellScopedAt,
    ActivePairReflectionTyping.residual_hasType bodyTyped bodyObject bodySealed sentTyped
      afterTyped tailTyped⟩
  simpa [Nat.add_comm] using bodyTyped.isWellScopedAt

/-- Nonempty signed output payload and continuation, with distinct channels. -/
def closedPayload : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "POutputK")
    [ActivePairNameComparison.quotedSend, FiniteWhole.zero, FiniteWhole.zero],
   FiniteWhole.unitSignature]

def closedAfter : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "POutputK")
    [ActivePairNameComparison.quotedReceive, FiniteWhole.zero, FiniteWhole.zero],
   ActivePairNameComparison.productSignature]

def closedSource : Pattern := fundedPairChannels
  ActivePairNameComparison.expandedQuotedSend ActivePairNameComparison.quotedSend
  FiniteWhole.localBody closedPayload closedAfter
  FiniteWhole.unitSignature FiniteWhole.retainedTail

def closedTarget : Pattern := residual FiniteWhole.localBody closedPayload closedAfter
  FiniteWhole.retainedTail

/-- Both quotation colors in the actual profile admit the local drop body. -/
theorem localBody_sealed : ReflectiveWellSorted.ReflectiveScopeSafeAt profile 1
    FiniteWhole.localBody := by
  intro presentation member
  have presentations : profile.presentations =
      [ActivePairNameComparison.declaration, ActivePairContextualReflection.declaration] := rfl
  rw [presentations] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

/-- This concrete instance exercises canonical equality of distinct nonempty
quotations and releases two distinct nonempty wrapped outputs. -/
theorem closed_typed_firing :
    HasSort language FreeTypeContext.empty [] closedSource costWrappedSortName ∧
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language 0 rule closedSource = [closedTarget] ∧
    HasSort language FreeTypeContext.empty [] closedTarget costWrappedSortName := by
  exact canonical_typed_firing []
    ActivePairNameComparison.expandedQuotedSend ActivePairNameComparison.quotedSend
    FiniteWhole.localBody closedPayload closedAfter
    FiniteWhole.unitSignature FiniteWhole.retainedTail
    (by decide +kernel)
    ActivePairNameComparison.expandedQuotedSend_typed ActivePairNameComparison.quotedSend_typed
    (checkHasType_sound (by decide +kernel)) (by decide +kernel) localBody_sealed
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))

/-- The receiver is the expanded raw quotation, even though its comparison
uses the same canonical name as the sender. -/
theorem closed_capture_preserves_receiver :
    matchRuleWithAt (ScopedReflectiveComparison.bodyComparison profile rule)
      rule bindingSpec 0 closedSource =
      [pairAssignment [] ActivePairNameComparison.expandedQuotedSend FiniteWhole.localBody
        closedPayload closedAfter FiniteWhole.unitSignature FiniteWhole.retainedTail] ∧
    lookup (pairAssignment [] ActivePairNameComparison.expandedQuotedSend FiniteWhole.localBody
      closedPayload closedAfter FiniteWhole.unitSignature FiniteWhole.retainedTail)
      (costSourceSchemaName "n") =
      some ⟨[], 0, ActivePairNameComparison.expandedQuotedSend⟩ := by
  constructor
  · apply scoped_match_pair []
      ActivePairNameComparison.expandedQuotedSend ActivePairNameComparison.quotedSend
      FiniteWhole.localBody closedPayload closedAfter
      FiniteWhole.unitSignature FiniteWhole.retainedTail <;> decide +kernel
  · decide +kernel

/-- The local received-name drop activates its nonempty payload, and the
output continuation survives as a separate residual component. -/
theorem closed_target_shape : closedTarget = .apply costContactConstructorName
    [.collection .hashBag [closedPayload, closedAfter] none,
     .apply costFundingConstructorName [FiniteWhole.retainedTail]] ∧
    closedPayload ≠ closedAfter ∧ closedPayload ≠ FiniteWhole.zero ∧
    closedAfter ≠ FiniteWhole.zero := by decide +kernel

/-- Literal matching blocks the same distinct spellings under both ordinary
and reflective binder operations. -/
theorem closed_literal_routes_reject :
    ScopedRuleExecution.applyRuleAt Engine.RelationEnv.empty language 0 rule closedSource = [] ∧
    ScopedReflectiveExecution.applyRuleAt profile Engine.RelationEnv.empty
      language 0 rule closedSource = [] := by
  constructor
  · apply literal_firing_rejected Substitution.instantiateBVar []
      ActivePairNameComparison.expandedQuotedSend ActivePairNameComparison.quotedSend
      FiniteWhole.localBody closedPayload closedAfter
      FiniteWhole.unitSignature FiniteWhole.retainedTail <;> decide +kernel
  · apply literal_firing_rejected (ScopedReflectiveExecution.binderOperation profile rule) []
      ActivePairNameComparison.expandedQuotedSend ActivePairNameComparison.quotedSend
      FiniteWhole.localBody closedPayload closedAfter
      FiniteWhole.unitSignature FiniteWhole.retainedTail <;> decide +kernel

/-- The rule also fires through the actual language-level canonical entry. -/
theorem closed_language_firing : closedTarget ∈
    ScopedReflectiveExecution.rewriteCanonicalStepAt profile Engine.RelationEnv.empty
      language 0 closedSource := by
  apply (ScopedReflectiveExecution.mem_rewriteCanonicalStepAt_iff _ _ _ _ _ _).mpr
  refine ⟨rule, ?_, ?_⟩
  · simp only [ActivePair.language, List.mem_cons, true_or]
  · rw [closed_typed_firing.2.1]
    exact List.mem_singleton_self _

/-- A different canonical Name cannot fund communication merely because both
channel terms are individually typed and the purse has the expected key. -/
theorem different_channel_blocks :
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language 0 rule
      (fundedPairChannels ActivePairNameComparison.quotedSend ActivePairNameComparison.quotedReceive
        FiniteWhole.localBody closedPayload closedAfter
        FiniteWhole.unitSignature FiniteWhole.retainedTail) = [] := by
  decide +kernel

private def closedSourceWithStack (stack : Pattern) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.collection .hashBag
        [.apply (costBaseConstructorName "PInput")
          [ActivePairNameComparison.expandedQuotedSend, .lambda none FiniteWhole.localBody],
         .apply (costBaseConstructorName "POutputK")
          [ActivePairNameComparison.quotedSend, closedPayload, closedAfter]] none,
       FiniteWhole.unitSignature],
     .apply costFundingConstructorName [stack]]

/-- Canonical channel comparison grants neither a missing purse head nor a
literal-distinct signature, including a product of two unit syntax trees. -/
theorem funding_guards_preserved :
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language 0 rule (closedSourceWithStack FiniteWhole.emptyStack) = [] ∧
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty
      language 0 rule (closedSourceWithStack
        (.apply costTokenStackConsConstructorName
          [ActivePairNameComparison.productSignature, FiniteWhole.retainedTail])) = [] := by
  constructor <;> decide +kernel

/-- Each rejection fixture is independently sorted in the actual language;
none is blocked merely by an undeclared channel or funding constructor. -/
theorem rejected_sources_typed :
    HasSort language FreeTypeContext.empty []
      (fundedPairChannels ActivePairNameComparison.quotedSend ActivePairNameComparison.quotedReceive
        FiniteWhole.localBody closedPayload closedAfter
        FiniteWhole.unitSignature FiniteWhole.retainedTail) costWrappedSortName ∧
    HasSort language FreeTypeContext.empty []
      (closedSourceWithStack FiniteWhole.emptyStack) costWrappedSortName ∧
    HasSort language FreeTypeContext.empty []
      (closedSourceWithStack (.apply costTokenStackConsConstructorName
        [ActivePairNameComparison.productSignature, FiniteWhole.retainedTail]))
      costWrappedSortName := by
  exact ⟨checkHasType_sound (by decide +kernel), checkHasType_sound (by decide +kernel),
    checkHasType_sound (by decide +kernel)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairCanonicalExecution
