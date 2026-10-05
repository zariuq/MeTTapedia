import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchFrame
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnaryPersistentBoundary
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningTracing
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety

/-!
# Every supplied unary compiler firing reads back to the chosen source fetch

Reference faithfulness identifies the source declaration and active request.
The source event's physical envelope transports their original marks in both
directions. Opening that envelope follows the supplied trace's same actors;
the selected unary boundary recovers the supplied endpoint, including one-shot
consumption, persistent reuse, private scopes and all untouched components.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryReadback

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingFetchEnvelope NamePassingFetchSelected
open NamePassingFetchMarking NamePassingFetchFrame NamePassingFetchResidual
open ActiveMarking ActiveOriginErasure ScopedActiveFrontier ScopedCommunicationInversion ActiveHeaderInvariant

private theorem fits_scope_body {Label : Type} {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Label scope) {bodyMarks : ActiveMarking.Tree Label} {body : Proc Δ}
    (fits : Fits (binders.close bodyMarks) (scope.close body)) : Fits bodyMarks body := by
  induction binders with
  | nil => exact fits
  | bind origin _ ih =>
      cases fits with
      | nu _ inside => exact ih inside

private theorem single_scope_body {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    (single : SingleBodies (scope.close body)) : SingleBodies body := by
  induction scope with
  | nil => exact single
  | bind _ ih =>
      simp only [Scope.close, nu, SingleBodies] at single
      exact ih body single

/-- The certificate is selected from the original source's lookup authority.
Its compiled successor is related to the actual target supplied by the caller. -/
theorem traced_unary_readback {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) {target : Proc Δ}
    (actual : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) actual)
    (unary : inputHeader actual.selected = .input1) :
    ∃ (kind : Environment.Action) (successor : Expr Srt.nm Γ)
      (event : Environment.EventCertificate kind source successor),
      kind ≠ .beta ∧ inputOrigin event [] = traced.continuation.inputOrigin ∧
        outputOrigin event [] = traced.continuation.outputOrigin ∧
        Environment.StepModulo kind source successor ∧
        StructuralEq target (compile successor environment result) := by
  obtain ⟨kind, successor, event, nonBeta, inputOriginEq, outputOriginEq⟩ :=
    traced_selected_event source environment faithful result actual traced unary
  let boundary := eventEnvelope event nonBeta environment result
  let marks := eventMarks event nonBeta [] environment result
  let body : Proc boundary.world :=
    par (out1 (.var boundary.channel) (.var boundary.datum))
      (par (ActiveUnarySelectedBoundary.receiver boundary.persistent (.var boundary.channel) boundary.guard)
        boundary.frame)
  let bodyMarks : ActiveMarking.Tree Origin :=
    .par (.out1 (outputOrigin event []))
      (.par (ActiveUnarySelectedBoundary.receiverMarks boundary.persistent (inputOrigin event []) marks.guard)
        marks.frame)
  have originalFits := mark_fits source [] environment result
  have closedFits : Fits (marks.binders.close bodyMarks) (boundary.scope.close body) :=
    fitted_target marks.forward originalFits
  have bodyFits := fits_scope_body marks.binders closedFits
  have safe : ScopedOpening.Safe (boundary.scope.close body) :=
    (ScopedOpening.safe_structural boundary.before).mp
      (RhoUnarySourceSafety.lambda_polyadic_safe source environment result)
  let changed : Exposure (boundary.scope.close body) target :=
    actual.changeSource boundary.before.symm
  have inputInBoundary : Selection (inputHeader changed.selected) traced.continuation.inputOrigin
      (marks.binders.close bodyMarks) := by
    exact Classical.choice (marks.backward.selection_back _ _ ⟨traced.originalInput⟩)
  have outputInBoundary : Selection (outputHeader changed.selected) traced.continuation.outputOrigin
      (marks.binders.close bodyMarks) := by
    exact Classical.choice (marks.backward.selection_back _ _ ⟨traced.originalOutput⟩)
  let given : TracedExposure (marks.binders.close bodyMarks) changed :=
    { binders := traced.binders
      redexMarks := traced.redexMarks
      frameMarks := traced.frameMarks
      continuation := traced.continuation
      frameFits := traced.frameFits
      transportedFits := traced.transportedFits
      transport := .trans marks.backward traced.transport
      originalInput := inputInBoundary
      originalOutput := outputInBoundary }
  obtain ⟨returned, opened, selected, sameInput, sameOutput, arity, endpoint⟩ :=
    ScopedOpeningTracing.open_scope_traced marks.binders body bodyMarks bodyFits changed given safe
  have inputChosen : selected.continuation.inputOrigin = inputOrigin event [] :=
    sameInput.trans inputOriginEq.symm
  have outputChosen : selected.continuation.outputOrigin = outputOrigin event [] :=
    sameOutput.trans outputOriginEq.symm
  have different : inputOrigin event [] ≠ outputOrigin event [] := by
    intro equal
    exact input_not_lookup event [] ((congrArg Origin.kind equal).trans (output_kind event nonBeta []))
  have single := single_scope_body boundary.scope body
    ((singleBodies_structural boundary.before).mp (compiler_singleBodies source environment result))
  have frameSingle : SingleBodies boundary.frame := by
    change SingleBodies (par (out1 (.var boundary.channel) (.var boundary.datum))
      (par (ActiveUnarySelectedBoundary.receiver boundary.persistent (.var boundary.channel) boundary.guard)
        boundary.frame)) at single
    simp only [par, out1, SingleBodies, true_and] at single
    exact single.2
  have frameUnused := event_frame_vacuous event nonBeta environment result
  have zero := event_pair_frame_zero event nonBeta [] environment result
  have explicitFits : Fits (.par (.out1 (outputOrigin event []))
      (.par (ActiveUnarySelectedBoundary.receiverMarks boundary.persistent (inputOrigin event []) marks.guard)
        marks.frame)) (par (out1 (.var boundary.channel) (.var boundary.datum))
          (par (ActiveUnarySelectedBoundary.receiver boundary.persistent (.var boundary.channel) boundary.guard)
            boundary.frame)) := bodyFits
  have guardFits : Fits marks.guard boundary.guard := by
    cases explicitFits with
    | par output rest => cases rest with
      | par receiver frame =>
          exact ActiveUnaryPersistentBoundary.receiver_guard_fits boundary.persistent
            (inputOrigin event []) (.var boundary.channel) receiver
  have frameFits : Fits marks.frame boundary.frame := by
    cases explicitFits with
    | par output rest => cases rest with
      | par receiver frame => exact frame
  have returnedEq := ActiveUnaryPersistentBoundary.receiver_endpoint boundary.persistent
    boundary.channel boundary.datum boundary.guard boundary.frame (inputOrigin event [])
    (outputOrigin event []) different marks.guard marks.frame guardFits frameFits frameUnused frameSingle
    zero opened selected (arity.trans unary) inputChosen outputChosen
  exact ⟨kind, successor, event, nonBeta, inputOriginEq, outputOriginEq, event.sound.toModulo,
    endpoint.trans ((boundary.scope.congr returnedEq).trans boundary.after)⟩

/-- Unrestricted equation-saturated unary executions retain their selected
source fetch and reach its compiled successor modulo the authored equations. -/
theorem unary_readback {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) {target : Proc Δ}
    (actual : Exposure (compile source environment result) target)
    (unary : inputHeader actual.selected = .input1) :
    ∃ (kind : Environment.Action) (successor : Expr Srt.nm Γ),
      kind ≠ .beta ∧ Environment.StepModulo kind source successor ∧
        StructuralEq target (compile successor environment result) := by
  obtain ⟨traced⟩ := tracedExposure_exists ⟨.privateReference, []⟩
    (mark_fits source [] environment result) actual
  obtain ⟨kind, successor, event, nonBeta, _, _, step, endpoint⟩ :=
    traced_unary_readback source environment faithful result actual traced unary
  exact ⟨kind, successor, nonBeta, step, endpoint⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryReadback
