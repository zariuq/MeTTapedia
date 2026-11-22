import Mettapedia.OSLF.MeTTaIL.GeneralRhoRepresentation

/-!
# Source-selected reflective COMM and the original semantic substitution

The operation below eliminates the received binder in open ambient contexts.
On the original closed ambient domain it agrees with the existing authored
RHS readout and the paper-facing semantic substitution for every derived rho
body and payload. Received dropped names give a nonidentity family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping
open Mettapedia.GSLT.LanguageDef.ReflectiveNormalizationTyping
open DerivedPresentationSyntax ScopedPattern ReflectiveSubstitution ReflectiveInstantiation
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

def reflectiveBody (body payload : Pattern) : Pattern :=
  instantiate rhoReflectivePresentation.toReflectivePresentationDecl 0
    (.apply "NQuote" [normalizeReflective rhoReflectivePresentation.toReflectivePresentationDecl payload]) body

theorem selected_body (body payload : Pattern) :
    ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm
      (.apply "NQuote" [payload]) body = reflectiveBody body payload := by
  rw [binder_operation]
  rfl

theorem reflective_reduct {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true)
    (restSafe : Pattern.isWellScopedListAt ambient rest = true) :
    ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec ambient
      (captured ambient channel body payload rest) =
      some (.collection .hashBag (reflectiveBody body payload :: rest) none) := by
  rw [reduct_readout _ bodySafe payloadSafe restSafe, selected_body]

/-- The stored input body and old source RHS readout agree for all closed
ambient bodies and payloads. Intervening input binders remain arbitrary. -/
theorem reflective_reduct_original {free : FreeSortContext} {channel body payload : Pattern}
    {rest : List Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (restSafe : Pattern.isWellScopedListAt 0 rest = true) :
    ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec 0
      (captured 0 channel body payload rest) =
      some (applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel body payload rest)) := by
  have bodySafe : body.isWellScopedAt 1 = true := (derived_process_typed bodyTyped).isWellScopedAt
  have payloadSafe : payload.isWellScopedAt 0 = true := (derived_process_typed payloadTyped).isWellScopedAt
  have replacementSafe : (Pattern.apply "NQuote"
      [normalizeReflective rhoReflectivePresentation.toReflectivePresentationDecl payload]).isWellScopedAt 0 = true := by
    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
      normalizeReflective_scoped rhoReflectivePresentation.toReflectivePresentationDecl payloadSafe
  rw [reflective_reduct bodySafe payloadSafe restSafe, applyBindingsForRule_rhoComm]
  unfold reflectiveBody
  rw [closed_agreement rhoReflectivePresentation.toReflectivePresentationDecl bodySafe replacementSafe]

/-- The compiled reduct is the paper-facing COMM reduct of the resolved body,
for every closed derived body and payload. -/
theorem reflective_reduct_resolved {free : FreeSortContext} {channel body payload : Pattern}
    {rest : List Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (restSafe : Pattern.isWellScopedListAt 0 rest = true) :
    ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec 0
      (captured 0 channel body payload rest) =
      some (.collection .hashBag
        (semanticCommSubst (resolveQuotes rhoReflectivePresentation body) payload :: rest) none) := by
  rw [reflective_reduct_original bodyTyped payloadTyped restSafe,
    applyBindingsForRule_rhoComm_eq_resolved bodyTyped payloadTyped]

/-- The compiled reduct is the paper-facing COMM reduct when the received body
lies in the literal-quotation fiber (decided automatically for concrete
bodies); see `LanguageDefAdequacy.hiddenQuoteDrop_comm_differs` for a body
outside it. -/
theorem reflective_reduct_semantic {free : FreeSortContext} {channel body payload : Pattern}
    {rest : List Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload)
    (restSafe : Pattern.isWellScopedListAt 0 rest = true)
    (fiber : ReflectiveCoherent.quotesLiteral rhoReflectivePresentation body = true := by decide) :
    ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec 0
      (captured 0 channel body payload rest) =
      some (.collection .hashBag (semanticCommSubst body payload :: rest) none) := by
  rw [reflective_reduct_original bodyTyped payloadTyped restSafe,
    applyBindingsForRule_rhoComm_agrees_derived bodyTyped fiber payloadTyped]

private theorem derived_name_atomic {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (sealed : binderSafeAt "NQuote" bound.length name = true) :
    atomicOrClosed rhoReflectivePresentation.toReflectivePresentationDecl name = true := by
  cases typed with
  | bvar _ => rfl
  | fvar _ => rfl
  | @quote bound process _ =>
      have closed : (Pattern.apply "NQuote" [process]).isWellScopedAt 0 = true :=
        isWellScopedAt_of_binderSafeAt "NQuote" (by
          simpa [binderSafeAt, rhoReflectivePresentation] using sealed)
      exact atomicOrClosed_of_closed closed

private theorem derived_name_names {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) :
    namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl name = true := by
  cases typed <;> rfl

mutual
theorem derived_names_admitted {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process)
    (sealed : binderSafeAt "NQuote" bound.length process = true) :
    namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl process = true := by
  cases typed with
  | bvar _ | fvar _ | unit => rfl
  | drop name =>
      exact derived_name_atomic name (by
        simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using sealed)
  | @output bound channelPattern payloadPattern channel payload =>
      have components : binderSafeAt "NQuote" bound.length channelPattern = true ∧
          binderSafeAt "NQuote" bound.length payloadPattern = true := by
        simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using sealed
      change (namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl channelPattern &&
        (namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl payloadPattern && true)) = true
      simp only [Bool.and_eq_true]
      exact ⟨derived_name_names channel, derived_names_admitted payload components.2, True.intro⟩
  | @input bound channelPattern bodyPattern channel body =>
      have components : binderSafeAt "NQuote" bound.length channelPattern = true ∧
          binderSafeAt "NQuote" (bound.length + 1) bodyPattern = true := by
        simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using sealed
      have inner := derived_names_admitted body (by simpa [rhoReflectivePresentation] using components.2)
      change (namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl channelPattern &&
        (namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl bodyPattern && true)) = true
      simp only [Bool.and_eq_true]
      exact ⟨derived_name_names channel, inner, True.intro⟩
  | parallel processes =>
      exact derived_names_list_admitted processes sealed
termination_by sizeOf process

theorem derived_names_list_admitted {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
    (sealed : binderSafeListAt "NQuote" bound.length processes = true) :
    namesAdmittedList rhoReflectivePresentation.toReflectivePresentationDecl processes = true := by
  cases typed with
  | nil => rfl
  | cons process processes =>
      simp only [binderSafeListAt, Bool.and_eq_true] at sealed
      simp only [namesAdmittedList, Bool.and_eq_true]
      exact ⟨derived_names_admitted process sealed.1, derived_names_list_admitted processes sealed.2⟩
termination_by sizeOf processes
end

theorem reflective_body_typed {free : FreeTypeContext} {bound : List TypeExpr} {body payload : Pattern}
    (bodyTyped : HasType language free (.base "Name" :: bound) body (.base "Proc"))
    (sealed : binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : HasType language free bound payload (.base "Proc")) :
    HasType language free bound (reflectiveBody body payload) (.base "Proc") := by
  exact instantiate_hasType (binders := []) reflectiveWitness bodyTyped
    (by simpa [rhoReflectivePresentation] using sealed) names
    (quote_typed (normalizeReflective_hasType reflectiveWitness payloadTyped))

theorem reflective_body_represented {body payload : Pattern}
    (bodyRepresented : Represented body) (payloadRepresented : Represented payload) :
    Represented (reflectiveBody body payload) :=
  instantiate_represented _ 0
    ((represented_apply_iff _ _).mpr (by
      simpa using normalize_represented rhoReflectivePresentation.toReflectivePresentationDecl payloadRepresented))
    bodyRepresented

theorem reflective_body_open {free : FreeTypeContext} {bound : List TypeExpr} {body payload : Pattern}
    (bodyTyped : OpenPatternWellSorted language free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : namesAdmitted rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language free bound (.base "Proc") payload) :
    OpenPatternWellSorted language free bound (.base "Proc") (reflectiveBody body payload) := by
  have typed := reflective_body_typed bodyTyped.1 sealed names payloadTyped.1
  have represented := reflective_body_represented ⟨bodyTyped.2.1, bodyTyped.2.2.1⟩
    ⟨payloadTyped.2.1, payloadTyped.2.2.1⟩
  exact ⟨typed, represented.1, represented.2, typed.isWellScopedAt⟩

/-- Arbitrary payloads are activated through the received bound drop. The
result retains the existing static quote/drop normalization of that payload. -/
theorem reflective_body_received_drop (payload : Pattern) :
    reflectiveBody (.apply "PDrop" [.bvar 0]) payload =
      normalizeReflective rhoReflectivePresentation.toReflectivePresentationDecl payload := by
  simp [reflectiveBody, instantiate, resolveQuotes, resolveQuotesList, finishResolveApply,
    substituteResolved, receive, Substitution.instantiateBVarAt, Substitution.liftBVars_zero,
    rhoReflectivePresentation]

theorem received_drop_changes_body :
    reflectiveBody (.apply "PDrop" [.bvar 0]) (.apply "PZero" []) ≠
      .apply "PDrop" [.bvar 0] := by decide +kernel

end Mettapedia.OSLF.MeTTaIL.GeneralRho
