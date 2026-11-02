import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory
import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafService

/-!
# Retained argument-control protocol controls

These controls exercise the entire argument controller using finite service
fixtures. They check ordered sibling traversal, correlated selections, raw
arguments, domains, suspension and reply identity. Callback closure uses the
actual checked reply consumer, including refusal, cancellation and retained
effects. The independently earned leaf connection is stated separately from
fixtures supplying already-evaluated duplicate occurrences. These checks do
not establish native callback or export correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControlControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeArgumentControlPolicy NativeArgumentControl NativeArgumentControlMachine
open NativeArgumentControlEncoding
open NativeArgumentControlHistory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open NativeArgumentProjection (Snapshot)

private def a : Atom := .symbol "a"
private def b : Atom := .symbol "b"
private def pick : Atom := .expression [.symbol "pick"]
private def choice : Atom := .symbol "Choice"
private def errorData : Atom := .expression [.symbol "Error", .symbol "held"]
private def nested : Atom := .expression [.symbol "let", .var "x", pick,
  .expression [.symbol "quote", .expression [.symbol "Pair", .var "x", .var "x"]]]
private def empty : Bindings := ⟨[], []⟩
private def bound : Bindings := ⟨[("x", a)], []⟩
private def arguments : TypedApplyState := ⟨.symbol "same", [pick], [choice], 0, [], empty⟩
private def resolved : Prepared := ⟨choice, pick, {dialect := .he}⟩
private def ops : Operations := ⟨fun _ evaluated => some evaluated, fun environment _ _ => some environment⟩
private def config (frames : List Frame) : Configuration := ⟨frames, [], 7, 0, [], 0⟩
private def start : Configuration := config [.enter arguments]

theorem initial_history_is_admitted : HistoryInv start :=
  history_empty _ (by simp [PlainFrames, Plain]) 7

theorem bound_variable_in_he_demands_evaluation :
    ({dialect := .he} : Policy).raw (.var "x") choice pick = false := rfl

theorem already_held_petta_variable_stays_raw :
    ({dialect := .petta} : Policy).raw (.var "x") choice pick = true := rfl

theorem unbound_variable_remains_raw :
    ({dialect := .he} : Policy).raw (.var "x") choice (.var "x") = true := rfl

theorem he_atom_preserves_nested_binding_and_quotation :
    ({dialect := .he} : Policy).raw nested Atom.atomType nested = true := rfl

theorem he_atom_preserves_error_data :
    ({dialect := .he} : Policy).raw errorData Atom.atomType errorData = true := rfl

theorem prime_atom_preserves_syntax :
    ({dialect := .prime} : Policy).raw nested Atom.atomType nested = true := rfl

theorem prime_proc_demands_evaluation :
    ({dialect := .prime} : Policy).raw pick procType pick = false := rfl

theorem petta_eager_atom_demands_evaluation :
    ({dialect := .petta, eagerCallable := true} : Policy).raw pick Atom.atomType pick = false := rfl

theorem data_domain_holds_unrecognized_syntax :
    ({dialect := .prime, dataDomain := true} : Policy).raw nested (.symbol "Data") nested = true := rfl

theorem normalization_overrides_data_and_atom :
    ({dialect := .prime, normalize := true, dataDomain := true} : Policy).raw
      nested Atom.atomType nested = false := rfl

theorem control_continuation_prevents_need_reification :
    ({dialect := .prime, controlContinuation := true, observableReference := true} : Policy).reify
      Atom.atomType = false := rfl

theorem data_reference_requests_reification :
    ({dialect := .prime, dataDomain := true, observableReference := true} : Policy).reify choice = true := rfl

theorem ordinary_he_mode_retains_environment :
    ({dialect := .he} : Policy).mode choice = .heTypedInEnvironment := rfl

theorem prime_proc_uses_untyped_service :
    ({dialect := .prime} : Policy).mode procType = .untyped := rfl

theorem normalization_requests_normal_form_service :
    ({dialect := .prime, normalize := true} : Policy).mode choice = .normalForm := rfl

theorem entry_returns_a_preparation_request :
    inspect ops start = call start [] (.prepare arguments) := rfl

private def waitPrepare : Configuration := issue start [] (.prepare arguments)
private def prepReply : Reply := ⟨(request waitPrepare (.prepare arguments) 0).endpoint, .prepared resolved, 5⟩
private def preparedState : Configuration := replied waitPrepare [] prepReply [.prepared arguments resolved]

theorem pending_preparation_history_is_admitted : HistoryInv waitPrepare :=
  issue_history initial_history_is_admitted [] (by simp [PlainFrames]) (.prepare arguments)

theorem preparation_reply_retains_source_state :
    deliver waitPrepare prepReply = .accepted preparedState := rfl

theorem accepted_preparation_preserves_earned_history : HistoryInv preparedState :=
  delivery_preserves_history pending_preparation_history_is_admitted preparation_reply_retains_source_state

theorem unissued_pending_serial_is_not_admitted : ¬HistoryInv (config [.waiting (.prepare arguments) 0]) := by
  intro admitted
  have below := (admitted.pendingFresh (.prepare arguments) 0 [] rfl).1
  change 0 < 0 at below
  omega

theorem preparation_reply_accounts_once :
    preparedState.externalWork = 5 ∧ preparedState.replyHistory = [0] := ⟨rfl, rfl⟩

theorem missing_reply_keeps_identical_endpoint :
    inspect ops waitPrepare = .call (request waitPrepare (.prepare arguments) 0) waitPrepare := rfl

theorem wrong_reply_kind_is_rejected :
    deliver waitPrepare {prepReply with value := .continuationEntered} = .rejected .wrongKind := rfl

theorem reply_without_pending_service_is_rejected :
    deliver start prepReply = .rejected .noPending := rfl

theorem reply_from_another_episode_is_rejected :
    deliver {waitPrepare with episode := 8} prepReply = .rejected .endpointMismatch := rfl

theorem reply_spliced_into_another_history_is_rejected :
    deliver {waitPrepare with emitted := [(a, bound)]} prepReply = .rejected .endpointMismatch := rfl

theorem old_reply_cannot_be_repeated (next : Configuration) :
    deliver preparedState prepReply ≠ .accepted next := duplicate_reply_rejected preparation_reply_retains_source_state next

theorem malformed_configuration_tag_is_rejected :
    readConfiguration (.expression [.symbol "he-native-argument-control-v1"]) = none := rfl

theorem full_saved_configuration_round_trip :
    readConfiguration (configurationData {waitPrepare with emitted := [(a, bound), (a, bound)], replyHistory := [9, 11], externalWork := 23}) =
      some {waitPrepare with emitted := [(a, bound), (a, bound)], replyHistory := [9, 11], externalWork := 23} := by simp

theorem substituted_call_requests_evaluation :
    inspect ops preparedState = call preparedState [] (.evaluate arguments resolved) := rfl

private def duplicateResults : ResultList := [(a, bound), (a, bound), (b, empty)]
private def selected : Snapshot := selectedSnapshot arguments resolved duplicateResults

theorem wait_eval_retains_duplicate_order_and_provenance :
    selected.pending = duplicateResults := rfl

theorem selected_outcome_retains_one_fixed_child_prefix :
    inspect ops (config [.iterate selected resolved]) =
      call (config [.iterate selected resolved]) []
        (.continuation (arguments.advance a bound) (.alternatives (activate selected a bound) resolved)) := rfl

theorem selected_parent_keeps_both_pending_siblings :
    (activate selected a bound).pending = [(a, bound), (b, empty)] := rfl

theorem returned_child_resumes_at_the_next_duplicate :
    inspect ops (config [.afterIterChild (activate selected a bound) resolved]) =
      .silent (config [.iterate {selected with nextOutcome := 1} resolved]) := rfl

theorem only_child_return_releases_parent :
    inspect ops (config [.afterOnlyChild arguments resolved a bound]) = .silent (config []) := rfl

theorem invalid_child_return_fault_is_explicit :
    inspect ops (config [.afterIterChild selected resolved]) = .fail [.fault .invalidChildPhase] := rfl

theorem cancelled_child_retains_parent_selection :
    acceptedFrame (.continuation (arguments.advance a bound) (.alternatives (activate selected a bound) resolved))
      .continuationCancelled = some [.afterIterChild (activate selected a bound) resolved] := rfl

theorem merge_failure_does_not_reorder_siblings :
    consume {ops with merge := fun _ _ => none} false selected = .skipped selected.afterOutcome := rfl

theorem binder_failure_does_not_reorder_siblings :
    consume {ops with extend := fun _ _ _ => none} false selected = .skipped selected.afterOutcome := rfl

theorem changed_error_is_emitted_without_binding :
    consume {ops with extend := fun _ _ _ => none} false
      {selected with outcomes := [(errorData, bound)]} =
      .failure (errorData, bound) {selected with outcomes := [(errorData, bound)], nextOutcome := 1} := rfl

theorem error_as_data_policy_selects_the_value :
    consume ops true {selected with outcomes := [(errorData, bound)]} =
      .child (errorData, bound) (activate {selected with outcomes := [(errorData, bound)]} errorData bound) := rfl

theorem unchanged_error_source_is_data :
    consume ops false {selected with original := errorData, outcomes := [(errorData, bound)]} =
      .child (errorData, bound)
        (activate {selected with original := errorData, outcomes := [(errorData, bound)]} errorData bound) := rfl

private def binderDomain : Atom := .expression [.symbol "Binder", .symbol "x", choice]
private def dependentArguments : TypedApplyState := {arguments with argTypes := [binderDomain]}
private def dependentPrepared : Prepared := {resolved with policy := {dialect := .prime, dependentTelescope := true}}
private def binderOps : Operations := {ops with extend := fun environment domain _ => if domain == binderDomain then some environment else none}

theorem evaluation_domain_is_resolved_but_binder_domain_is_original :
    dependentPrepared.domain = choice ∧ originalDomain dependentArguments = binderDomain := ⟨rfl, rfl⟩

theorem raw_binder_extension_uses_original_telescope_domain :
    rawBindings binderOps dependentArguments dependentPrepared a = some empty := rfl

theorem evaluated_binder_extension_uses_original_telescope_domain :
    consume binderOps false (selectedSnapshot dependentArguments dependentPrepared [(a, bound)]) =
      .child (a, bound) (activate (selectedSnapshot dependentArguments dependentPrepared [(a, bound)]) a bound) := rfl

theorem replacing_original_domain_with_resolved_domain_would_fail :
    binderOps.extend bound dependentPrepared.domain a = none := rfl

private def evalWait : Configuration := issue preparedState [] (.evaluate arguments resolved)
private def effectRequest : Atom := .expression [.symbol "println!", .symbol "hello"]
private def effectToken : Atom := .expression [.symbol "opaque-evaluation-continuation", nested]
private def effectReply : Reply := ⟨(request evalWait (.evaluate arguments resolved) 2).endpoint,
  .effectRequired effectToken effectRequest, 3⟩
private def effectWait : Configuration := replied evalWait [] effectReply
  [.waiting (.effect arguments resolved effectToken effectRequest) 0]

theorem effect_reply_suspends_with_retained_evaluation :
    deliver evalWait effectReply = .accepted effectWait := rfl

theorem evaluation_wait_preserves_earned_history : HistoryInv evalWait :=
  issue_history accepted_preparation_preserves_earned_history [] (by simp [PlainFrames]) (.evaluate arguments resolved)

theorem external_effect_request_preserves_earned_history : HistoryInv effectWait :=
  delivery_preserves_history evaluation_wait_preserves_earned_history effect_reply_suspends_with_retained_evaluation

theorem inspecting_effect_does_not_commit_or_charge_it :
    inspect ops effectWait = .call
      (request effectWait (.effect arguments resolved effectToken effectRequest) 3) effectWait := rfl

theorem effect_wait_does_not_publish_answers : effectWait.emitted = [] := rfl

private def returnedEffect : Reply := ⟨(request effectWait (.effect arguments resolved effectToken effectRequest) 3).endpoint,
  .effectReturned (.symbol "ack"), 7⟩
private def resumeWait : Configuration := replied effectWait [] returnedEffect
  [.waiting (.resumeEvaluation arguments resolved effectToken (.symbol "ack")) 0]

theorem effect_return_resumes_the_exact_saved_evaluation :
    deliver effectWait returnedEffect = .accepted resumeWait := rfl

theorem effect_return_retains_its_continuation_and_ordered_history :
    resumeWait.frames = [.waiting (.resumeEvaluation arguments resolved effectToken (.symbol "ack")) 4] ∧
      resumeWait.replyHistory = [0, 2, 3] ∧ resumeWait.externalWork = 15 := ⟨rfl, rfl, rfl⟩

theorem effect_return_preserves_earned_history : HistoryInv resumeWait :=
  delivery_preserves_history external_effect_request_preserves_earned_history effect_return_resumes_the_exact_saved_evaluation

theorem effect_return_cannot_be_accepted_twice (next : Configuration) :
    deliver resumeWait returnedEffect ≠ .accepted next :=
  duplicate_reply_rejected effect_return_resumes_the_exact_saved_evaluation next

theorem raw_error_reply_can_remain_data :
    acceptedFrame (.transform arguments resolved) (.transformed (.value errorData)) =
      some [.rawReady arguments resolved errorData] := rfl

theorem reification_error_emits_exact_failure_occurrence :
    response (.transform arguments resolved) (.transformed (.error (errorData, bound))) =
      some ([(errorData, bound)], []) := rfl

theorem failed_data_wrapper_drops_only_this_branch :
    response (.transform arguments resolved) (.transformed .dropped) = some ([], []) := rfl

theorem unavailable_wait_eval_collector_drops_only_this_branch :
    response (.evaluate arguments resolved) .collectorUnavailable = some ([], []) := rfl

/-- Finite service fixture for complete argument traversals. It returns
already-evaluated occurrences and never implements expression reduction. -/
private def fixtureReply : Waiting → ReplyValue
  | .prepare state => .prepared ⟨originalDomain state, original state, {dialect := .he}⟩
  | .transform _ prepared => .transformed (.value prepared.bound)
  | .evaluate _ prepared | .resumeEvaluation _ prepared _ _ =>
      .evaluated (if prepared.bound == pick then [(a, empty), (b, empty)] else [(prepared.bound, empty)])
  | .effect _ _ _ _ => .effectReturned (.symbol "ack")
  | .continuation _ _ => .continuationEntered

private def drive : Nat → Configuration → Configuration
  | 0, state => state
  | fuel + 1, state =>
    match inspect ops state with
    | .silent after | .publish _ after => drive fuel after
    | .call request saved =>
        match fulfillCurrent saved (fixtureReply request.service) 1 with
        | .accepted after => drive fuel after
        | .rejected _ => saved
    | .finish after => after
    | .fail _ => state

private def independentArguments : TypedApplyState :=
  ⟨.symbol "pair", [pick, pick], [choice, choice], 0, [], empty⟩

theorem complete_shared_argument_traversal_keeps_two_correlated_selections :
    (drive 40 start).emitted =
      [(.expression [.symbol "same", a], empty), (.expression [.symbol "same", b], empty)] := by decide

theorem independent_argument_traversal_keeps_four_ordered_pairs :
    (drive 80 (config [.enter independentArguments])).emitted =
      [(.expression [.symbol "pair", a, a], empty), (.expression [.symbol "pair", a, b], empty),
        (.expression [.symbol "pair", b, a], empty), (.expression [.symbol "pair", b, b], empty)] := by decide

theorem shared_argument_traversal_releases_its_complete_stack : (drive 40 start).frames = [] := by decide

theorem independent_argument_traversal_releases_its_complete_stack :
    (drive 80 (config [.enter independentArguments])).frames = [] := by decide

theorem two_raw_arguments_keep_nested_syntax_and_error_data :
    (drive 30 (config [.enter ⟨.symbol "raw-pair", [nested, errorData],
      [Atom.atomType, Atom.atomType], 0, [], bound⟩])).emitted =
      [(.expression [.symbol "raw-pair", nested, errorData], bound)] := by decide

theorem ordered_duplicate_traversal_keeps_occurrence_multiplicity :
    (drive 40 (config [.iterate selected resolved])).emitted =
      [(.expression [.symbol "same", a], bound), (.expression [.symbol "same", a], bound),
        (.expression [.symbol "same", b], empty)] := by decide

theorem pause_resume_preserves_exact_pending_parent :
    (machine ops).run 1 (config [.afterIterChild (activate selected a bound) resolved]) =
      ([], .exhausted (config [.iterate {selected with nextOutcome := 1} resolved])) := rfl

theorem pending_service_is_visible_at_every_positive_budget (fuel : Nat) :
    (machine ops).run (fuel + 1) waitPrepare =
      ([], .suspended (request waitPrepare (.prepare arguments) 0) waitPrepare) :=
  awaiting_run ops waitPrepare (.prepare arguments) 0 fuel [] rfl

/-! ## Checked callbacks, ordered occurrences and retained boundaries -/

private def fixtureEnvironment : Environment Atom Atom Atom Atom := fun endpoint =>
  match readEndpoint endpoint with
  | some (_, service, _) => ([], .returned (replyData ⟨endpoint, fixtureReply service, 1⟩))
  | none => ([], .faulted (.symbol "invalid-endpoint"))

private def closedFixture := (interactionMachine ops .stop).close interactionCallback fixtureEnvironment

private def answerOccurrences (events : List Atom) : ResultList :=
  events.filterMap fun
    | .expression [.symbol "answer", result] => TypedApplyEncoding.readResult result
    | _ => none

theorem checked_callbacks_keep_correlated_selections :
    answerOccurrences (closedFixture.run 40 (.active start)).1 =
      [(.expression [.symbol "same", a], empty), (.expression [.symbol "same", b], empty)] := by decide

theorem checked_callbacks_keep_independent_choice_order :
    answerOccurrences (closedFixture.run 80 (.active (config [.enter independentArguments]))).1 =
      [(.expression [.symbol "pair", a, a], empty), (.expression [.symbol "pair", a, b], empty),
        (.expression [.symbol "pair", b, a], empty), (.expression [.symbol "pair", b, b], empty)] := by decide +kernel

/-- This consumes an already-evaluated result list. It does not assert that
the singleton source-leaf service produces a duplicated answer list. -/
theorem checked_callbacks_keep_duplicate_bindings_and_order :
    answerOccurrences (closedFixture.run 40 (.active (config [.iterate selected resolved]))).1 =
      [(.expression [.symbol "same", a], bound), (.expression [.symbol "same", a], bound),
        (.expression [.symbol "same", b], empty)] := by decide

theorem represented_duplicate_trace_and_endpoint_are_exact :
    ((interactionDataMachine ops .stop).close representedCallback fixtureEnvironment).run 40
        (interactionData (.active (config [.iterate selected resolved]))) =
      ((closedFixture.run 40 (.active (config [.iterate selected resolved]))).1,
        encodeInteractionOutcome (closedFixture.run 40 (.active (config [.iterate selected resolved]))).2) :=
  interaction_closed_run_encoded ops .stop fixtureEnvironment 40 _

theorem checked_callback_releases_complete_stack :
    (closedFixture.run 40 (.active start)).2 = .finished (configurationData (drive 40 start)) ∧
      (drive 40 start).frames = [] := ⟨rfl, by decide⟩

private def wrongReply : Reply := {prepReply with value := .continuationEntered}
private def wrongData : Atom := replyData wrongReply
private def refused : Interaction := .refused .wrongKind waitPrepare wrongData

theorem decoded_wrong_reply_kind_is_refused :
    readReply wrongData = some wrongReply ∧
      resumeInteraction (.active waitPrepare) (.returned wrongData) = refused :=
  ⟨readReply_replyData _, rfl⟩

theorem reply_refusal_preserves_all_history_and_work :
    resumeInteraction (.active waitPrepare) (.returned wrongData) =
      .refused .wrongKind waitPrepare wrongData ∧
      waitPrepare.replyHistory = [] ∧ waitPrepare.externalWork = 0 ∧ waitPrepare.nextTicket = 1 := ⟨rfl, rfl, rfl, rfl⟩

theorem refusal_stop_finishes_with_complete_boundary :
    (interactionMachine ops .stop).run 1 refused = ([], .finished (interactionData refused)) := rfl

theorem refusal_retry_resumes_identical_unconsumed_endpoint :
    (interactionMachine ops .retry).run 1 refused = ([], .exhausted (.active waitPrepare)) := rfl

theorem malformed_reply_is_separate_from_endpoint_refusal :
    resumeInteraction (.active waitPrepare) (.returned (.symbol "invalid-reply")) =
      .malformedReply waitPrepare (.symbol "invalid-reply") := rfl

theorem negative_reply_charge_is_not_decoded :
    readReply (.expression [.symbol "he-native-argument-reply-v1", prepReply.endpoint,
      replyValueData prepReply.value, .grounded (.int (-1))]) = none := rfl

theorem cancellation_retains_pending_configuration :
    resumeInteractionData (interactionData (.active effectWait)) .cancelled =
      interactionData (.cancelled effectWait) := resumeInteraction_encoded _ _

theorem callback_failure_is_not_argument_fault :
    resumeInteraction (.active effectWait) (.faulted (.symbol "external-failure")) =
      .callbackFault effectWait (.symbol "external-failure") ∧
      (interactionMachine ops .stop).run 1 (.callbackFault effectWait (.symbol "external-failure")) =
        ([], .finished (interactionData (.callbackFault effectWait (.symbol "external-failure")))) := ⟨rfl, rfl⟩

theorem spliced_callback_retains_actual_saved_parent :
    resumeInteraction (.active {waitPrepare with emitted := [(a, bound)]})
        (.returned (replyData prepReply)) =
      .refused .endpointMismatch {waitPrepare with emitted := [(a, bound)]} (replyData prepReply) := rfl

theorem consumed_callback_cannot_charge_again :
    resumeInteraction (.active preparedState) (.returned (replyData prepReply)) =
      .refused .noPending preparedState (replyData prepReply) ∧
      preparedState.externalWork = 5 ∧ preparedState.replyHistory = [0] := ⟨rfl, rfl, rfl⟩

private def refusingEnvironment : Environment Atom Atom Atom Atom := fun _ => ([], .returned wrongData)
private def retrying := (interactionMachine ops .retry).close interactionCallback refusingEnvironment
private def refusalEvents : List Atom := [callEventData prepReply.endpoint, replyEventData (.returned wrongData)]

private theorem retrying_active_step : retrying.step (.active waitPrepare) = some (.publish refusalEvents refused) := rfl
private theorem retrying_refused_step : retrying.step refused = some (.silent (.active waitPrepare)) := rfl

theorem refusing_handler_retry_keeps_exact_events_and_endpoint :
    retrying.run 2 (.active waitPrepare) = (refusalEvents, .exhausted (.active waitPrepare)) ∧
      retrying.run 4 (.active waitPrepare) = (refusalEvents ++ refusalEvents, .exhausted (.active waitPrepare)) := by
  simp only [Machine.run, retrying_active_step, retrying_refused_step, List.append_nil]
  exact ⟨trivial, trivial⟩

private theorem refusal_loop_runs (fuel : Nat) :
    (∃ residual, (retrying.run fuel (.active waitPrepare)).2 = .exhausted residual) ∧
    (∃ residual, (retrying.run fuel refused).2 = .exhausted residual) := by
  induction fuel with
  | zero => exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  | succ fuel ih =>
      constructor
      · obtain ⟨residual, remains⟩ := ih.2
        exact ⟨residual, by simp only [Machine.run, retrying_active_step]; exact remains⟩
      · obtain ⟨residual, remains⟩ := ih.1
        exact ⟨residual, by simp only [Machine.run, retrying_refused_step]; exact remains⟩

/-- A refusing handler can run forever. The correspondence preserves this
behavior and supplies no eventual-acceptance or handler-fairness theorem. -/
theorem refusal_forever_diverges_in_both_representations :
    retrying.DivergesWithin (.active waitPrepare) ∧
      ((interactionDataMachine ops .retry).close representedCallback refusingEnvironment).DivergesWithin
        (interactionData (.active waitPrepare)) := by
  have source : retrying.DivergesWithin (.active waitPrepare) := fun fuel => (refusal_loop_runs fuel).1
  exact ⟨source, (interaction_closed_divergence ops .retry refusingEnvironment _ _ rfl).mp source⟩

private def badCallback : Callback Interaction Atom Atom Atom Atom :=
  {interactionCallback with resume := fun _ _ => .active start}
private def acceptedEnvironment : Environment Atom Atom Atom Atom := fun _ =>
  ([], .returned (replyData prepReply))

theorem identical_callback_labels_do_not_determine_retained_result :
    badCallback.callEvent = interactionCallback.callEvent ∧
      badCallback.replyEvent = interactionCallback.replyEvent ∧
      ((interactionMachine ops .stop).close badCallback acceptedEnvironment).run 1 (.active waitPrepare) ≠
        ((interactionMachine ops .stop).close interactionCallback acceptedEnvironment).run 1 (.active waitPrepare) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have after : ((interactionMachine ops .stop).close interactionCallback acceptedEnvironment).run 1 (.active waitPrepare) =
      ([callEventData prepReply.endpoint, replyEventData (.returned (replyData prepReply))],
        .exhausted (.active preparedState)) := rfl
  have bad : ((interactionMachine ops .stop).close badCallback acceptedEnvironment).run 1 (.active waitPrepare) =
      ([callEventData prepReply.endpoint, replyEventData (.returned (replyData prepReply))],
        .exhausted (.active start)) := rfl
  rw [after, bad] at equal
  have impossible : start.frames = preparedState.frames := congrArg
    (fun result => match result.2 with | .exhausted (.active saved) => saved.frames | _ => []) equal
  cases impossible

private def effectReceipt : Atom := .expression [.symbol "effect-receipt", effectRequest]
private def effectEnvironment : Environment Atom Atom Atom Atom := fun endpoint =>
  match readEndpoint endpoint with
  | some (_, .effect _ _ _ _, _) => ([effectReceipt], .returned (replyData returnedEffect))
  | some (_, service, _) => ([], .returned (replyData ⟨endpoint, fixtureReply service, 1⟩))
  | none => ([], .faulted (.symbol "invalid-endpoint"))
private def closedEffects := (interactionMachine ops .stop).close interactionCallback effectEnvironment

theorem effect_call_records_handler_receipt_and_saved_resumption :
    closedEffects.run 1 (.active effectWait) =
      ([callEventData returnedEffect.endpoint, effectReceipt, replyEventData (.returned (replyData returnedEffect))],
        .exhausted (.active resumeWait)) := rfl

theorem resumed_effect_does_not_repeat_established_handler_receipt :
    (closedEffects.run 2 (.active effectWait)).1.count effectReceipt = 1 ∧
      (closedEffects.run 1 (.active resumeWait)).1.count effectReceipt = 0 := by decide

theorem represented_effect_prefix_resumes_complete_endpoint (second : Nat) :
    ((interactionDataMachine ops .stop).close representedCallback effectEnvironment).run (1 + second)
        (interactionData (.active effectWait)) =
      ([callEventData returnedEffect.endpoint, effectReceipt, replyEventData (.returned (replyData returnedEffect))] ++
          (closedEffects.run second (.active resumeWait)).1,
        encodeInteractionOutcome (closedEffects.run second (.active resumeWait)).2) :=
  interaction_closed_resume ops .stop effectEnvironment 1 second _ _ _
    effect_call_records_handler_receipt_and_saved_resumption

private def cancelledService : Waiting :=
  .continuation (arguments.advance a bound) (.alternatives (activate selected a bound) resolved)
private def cancelledWait : Configuration := issue (config [.iterate selected resolved]) [] cancelledService
private def cancelledReply : Reply := ⟨(request cancelledWait cancelledService 0).endpoint, .continuationCancelled, 2⟩
private def cancelledParent : Configuration := replied cancelledWait [] cancelledReply
  [.afterIterChild (activate selected a bound) resolved]

theorem cancelled_child_reply_has_independent_parent_rule :
    FrameReplyRel cancelledService .continuationCancelled [.afterIterChild (activate selected a bound) resolved] :=
  .cancelled _ _

theorem cancelled_child_checked_reply_retains_pending_duplicate :
    resumeInteractionData (interactionData (.active cancelledWait)) (.returned (replyData cancelledReply)) =
      interactionData (.active cancelledParent) ∧
      (activate selected a bound).pending = [(a, bound), (b, empty)] := by decide

/-! ## Independently earned singleton source replies -/

/-- The actual recursive source worker earns the singleton leaf reply. The
existing independent delivery judgment and history invariant connect it to
one closed callback transition of the retained parent and its data codec. -/
theorem independently_earned_leaf_closed_reply
    (operations : Operations) (policy : RefusalPolicy) (saved : Configuration)
    (argument : TypedApplyState) (prepared : Prepared) (rest : List Frame) (ticket : Nat)
    (pending : saved.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (history : HistoryInv saved) (space : Space) (source : HE.GroundedDispatch)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : Spec.Eval.EvalTypeService)
    (fuel charge : Nat) (leaf : FirstSuccessLeafEvaluation.LeafRel prepared.bound prepared.domain)
    (environment : Environment Atom Atom Atom Atom) (externalEvents : List Atom)
    (provided : environment (request saved (.evaluate argument prepared) ticket).endpoint =
      (externalEvents, .returned (replyData
        ⟨(request saved (.evaluate argument prepared) ticket).endpoint,
          .evaluated (HE.evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)), charge⟩))) :
    ∃ (job : FirstSuccessLeafService.Job) (after : Configuration),
      job.value = prepared.bound ∧ job.expected = prepared.domain ∧ job.bindings = argument.env ∧
      DeliveryRel saved
        ⟨(request saved (.evaluate argument prepared) ticket).endpoint,
          .evaluated (HE.evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)), charge⟩ after ∧
      HistoryInv after ∧
      ((interactionDataMachine operations policy).close representedCallback environment).run 1
        (interactionData (.active saved)) =
        (callEventData (request saved (.evaluate argument prepared) ticket).endpoint :: externalEvents ++
          [replyEventData (.returned (replyData
            ⟨(request saved (.evaluate argument prepared) ticket).endpoint,
              .evaluated (HE.evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)), charge⟩))],
          .exhausted (interactionData (.active after))) ∧
      (FirstSuccessRecursiveExecution.dataMachine source).observe 4
        (RecursiveEncoding.configurationData job.pending) = ⟨[job.reply], .finished job.finished⟩ ∧
      Spec.Eval.EvalAtomRawRel space dispatch live (typing := typing)
        prepared.bound prepared.domain argument.env job.reply := by
  obtain ⟨job, after, value, expected, bindings, admitted, retained, earned, evidence⟩ :=
    FirstSuccessLeafService.retained_evaluation_reply saved argument prepared rest ticket pending history
      space source dispatch live typing fuel charge leaf
  refine ⟨job, after, value, expected, bindings, admitted, retained, ?_, earned, evidence⟩
  rw [interaction_closed_run_encoded]
  have entered := interaction_waiting_one_call operations policy environment saved
    (.evaluate argument prepared) ticket rest pending
  have callEvents : Machine.callEvents interactionCallback environment
      (request saved (.evaluate argument prepared) ticket).endpoint =
      callEventData (request saved (.evaluate argument prepared) ticket).endpoint :: externalEvents ++
        [replyEventData (.returned (replyData
          ⟨(request saved (.evaluate argument prepared) ticket).endpoint,
            .evaluated (HE.evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)), charge⟩))] := by
    simp only [Machine.callEvents, interactionCallback, provided]
  rw [callEvents] at entered
  simp only [provided] at entered
  rw [(returned_reply_accepted_iff _ _ _).mpr admitted] at entered
  rw [entered]
  rfl

private def leafSyntax : Atom := .expression [.symbol "quote",
  .expression [.symbol "Pair", .var "fresh", .var "fresh"]]
private def leafArgument : TypedApplyState := ⟨.symbol "hold", [leafSyntax], [Atom.expressionType], 0, [], bound⟩
private def leafPrepared : Prepared := ⟨Atom.expressionType, leafSyntax, {dialect := .he}⟩
private def leafPending : Configuration := issue (config [.enter leafArgument]) [] (.evaluate leafArgument leafPrepared)

theorem independently_admitted_leaf_demand_is_not_raw :
    leafPrepared.policy.raw (original leafArgument) leafPrepared.domain leafPrepared.bound = false ∧
      FirstSuccessLeafEvaluation.LeafRel leafPrepared.bound leafPrepared.domain :=
  ⟨rfl, Or.inr ⟨Atom.expressionType, .expression _, Or.inr (Or.inl rfl)⟩⟩

theorem nonempty_earned_leaf_is_accepted_by_checked_callback (source : HE.GroundedDispatch)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : Spec.Eval.EvalTypeService) :
    ∃ (job : FirstSuccessLeafService.Job) (after : Configuration),
      HistoryInv after ∧
      resumeInteractionData (interactionData (.active leafPending)) (.returned (replyData
        ⟨(request leafPending (.evaluate leafArgument leafPrepared) 0).endpoint,
          .evaluated (HE.evalAtom Space.empty source leafSyntax Atom.expressionType bound 1), 4⟩)) =
        interactionData (.active after) ∧
      (FirstSuccessRecursiveExecution.dataMachine source).observe 4
        (RecursiveEncoding.configurationData job.pending) = ⟨[(leafSyntax, bound)], .finished job.finished⟩ ∧
      Spec.Eval.EvalAtomRawRel Space.empty dispatch live (typing := typing)
        leafSyntax Atom.expressionType bound (leafSyntax, bound) := by
  have initial : HistoryInv (config [.enter leafArgument]) := history_empty _ (by simp [PlainFrames, Plain]) 7
  have retained : HistoryInv leafPending := issue_history initial [] (by simp [PlainFrames]) _
  obtain ⟨job, after, value, expected, bindings, accepted, history, observed, evidence⟩ :=
    FirstSuccessLeafService.retained_evaluation_reply leafPending leafArgument leafPrepared [] 0 rfl retained
      Space.empty source dispatch live typing 0 4 independently_admitted_leaf_demand_is_not_raw.2
  have exactReply : job.reply = (leafSyntax, bound) := by
    simp only [FirstSuccessLeafService.Job.reply, value, bindings, leafPrepared, leafArgument]
  refine ⟨job, after, history, (represented_reply_accepted_iff _ _ _).mpr accepted, ?_, ?_⟩
  · rw [exactReply] at observed
    exact observed
  · rw [exactReply] at evidence
    exact evidence

/-! ## World-validated issued replies -/

namespace OwnedControls

open Mettapedia.Machines
open Mettapedia.Machines.Cursor.OwnedLifecycle
open OwnedReplyBoundary

private def world : RevisionEnvironment Nat (Option Nat) := ⟨fun key => if key = 0 then none else some 3⟩
private def capture : Capture Nat (Option Nat) :=
  ⟨5, (CapturedReadView.admit world).consult world 0, effectWait⟩
private def firstRow : IssuedReturn.Row Atom Nat := ⟨1, 11, configurationData effectWait, 5⟩
private def secondRow : IssuedReturn.Row Atom Nat := ⟨2, 12, configurationData effectWait, 5⟩
private def registry : OwnedReplyBoundary.Registry := ⟨19, [firstRow, secondRow]⟩
private def first : OwnedReplyBoundary.Handle := ⟨19, 7, firstRow⟩
private def second : OwnedReplyBoundary.Handle := ⟨19, 7, secondRow⟩
private def remaining : OwnedReplyBoundary.Registry := ⟨19, [secondRow]⟩

theorem issued_namespace_is_valid : registry.Valid := by
  simp [registry, IssuedReturn.Registry.Valid, firstRow, secondRow]

/-- Equal retained payloads have two issued occurrence identities. -/
theorem equal_payloads_have_independent_issued_authority :
    first.row.payload = second.row.payload ∧ first.row ≠ second.row ∧
      IssuedReturn.Authenticated registry first ∧ IssuedReturn.Authenticated registry second := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro equal
    have impossible := congrArg IssuedReturn.Row.occurrence equal
    change (1 : Nat) = 2 at impossible
    omega
  · simp [IssuedReturn.Authenticated, registry, first, firstRow]
  · simp [IssuedReturn.Authenticated, registry, second, secondRow]

theorem valid_effect_reply_retains_resumption_and_consumes_one_owner :
    (deliverChecked registry world capture first returnedEffect).1 = .ok (resumeWait, remaining) ∧
      (deliverChecked registry world capture first returnedEffect).2.2 = 1 := ⟨rfl, rfl⟩

theorem accepted_effect_reply_keeps_paid_history : HistoryInv resumeWait :=
  accepted_history external_effect_request_preserves_earned_history
    valid_effect_reply_retains_resumption_and_consumes_one_owner.1

theorem equal_payload_sibling_survives_delivery :
    IssuedReturn.lookup remaining second = (some 0, 1) := rfl

/-- Reusing an unchanged pre-reply packet with the current registry refuses. -/
theorem copied_pre_reply_packet_has_no_issued_authority :
    (deliverChecked remaining world capture first returnedEffect).1 = .error .unissued := rfl

theorem copying_the_registry_would_duplicate_authority :
    (deliverChecked registry world capture first returnedEffect).1 = .ok (resumeWait, remaining) :=
  valid_effect_reply_retains_resumption_and_consumes_one_owner.1

theorem parent_lineage_is_checked_in_addition_to_registry_membership :
    IssuedReturn.Authenticated registry {first with parent := 8} ∧
      (deliverChecked registry world capture {first with parent := 8} returnedEffect).1 =
        .error .ownerMismatch := by
  refine ⟨?_, rfl⟩
  simp [IssuedReturn.Authenticated, registry, first, firstRow]

theorem provider_mismatch_is_not_a_reply_to_this_capture :
    (deliverChecked registry world {capture with source := 6} first returnedEffect).1 =
      .error .ownerMismatch := rfl

theorem changed_answer_history_is_not_the_saved_owner_payload :
    (deliverChecked registry world
      {capture with capture := {effectWait with emitted := [(a, bound), (a, bound)]}}
      first returnedEffect).1 = .error .ownerMismatch := rfl

theorem wrong_reply_kind_does_not_publish_a_registry_edit :
    (deliverChecked registry world capture first {returnedEffect with value := .continuationEntered}).1 =
      .error (.protocol .wrongKind) ∧ IssuedReturn.Authenticated registry first := by
  refine ⟨rfl, ?_⟩
  simp [IssuedReturn.Authenticated, registry, first, firstRow]

theorem unrelated_world_change_accepts_the_same_complete_reply :
    (deliverChecked registry (world.update 1 (some 99)) capture first returnedEffect).1 =
      .ok (resumeWait, remaining) := rfl

theorem new_binding_invalidates_a_consulted_absence :
    (deliverChecked registry (world.update 0 (some 7)) capture first returnedEffect).1 =
      .error .staleDependencies ∧
      (deliverChecked registry (world.update 0 (some 7)) capture first returnedEffect).2.1.captured.current 0 =
        none := ⟨rfl, rfl⟩

private def poisoned : Capture Nat (Option Nat) :=
  {capture with view := (deliverChecked registry (world.update 0 (some 7)) capture first returnedEffect).2.1}

theorem restoring_the_world_does_not_clear_an_observed_mismatch :
    (deliverChecked registry world poisoned first returnedEffect).1 = .error .staleDependencies := rfl

theorem incomplete_capture_cannot_accept_even_an_issued_reply :
    (deliverChecked registry world {capture with view := {capture.view with captureComplete := false}}
      first returnedEffect).1 = .error .staleDependencies := rfl

theorem independent_equal_payload_reply_survives_the_first :
    (deliverChecked remaining world capture second returnedEffect).1 = .ok (resumeWait, ⟨19, []⟩) := rfl

/-- Two independently issued copies of the same payload retain their separate
consumer endpoints through either delivery order and unrelated world writes. -/
theorem independent_replies_survive_unrelated_world_writes :
    ∃ finalFirst finalSecond,
      (deliverChecked remaining (world.update 1 (some 99)) capture second returnedEffect).1 =
        .ok (resumeWait, finalFirst) ∧
      (deliverChecked ⟨19, [firstRow]⟩ (world.update 2 (some 88)) capture first returnedEffect).1 =
        .ok (resumeWait, finalSecond) ∧
      finalFirst.identity = finalSecond.identity ∧ finalFirst.rows.Perm finalSecond.rows ∧
      BindingPublication.applyWrites (BindingPublication.applyWrites world.current [(1, 99)])
        [(2, 88)] =
          BindingPublication.applyWrites (BindingPublication.applyWrites world.current [(2, 88)])
            [(1, 99)] ∧
      ∀ survivor, IssuedReturn.Authenticated finalFirst survivor ↔
        IssuedReturn.Authenticated finalSecond survivor := by
  apply independent_replies_with_binding_publication [(1, 99)] [(2, 88)]
    (registry := registry) (live := world)
    (capture := capture) (other := capture) (handle := first) (second := second)
    (reply := returnedEffect) (secondReply := returnedEffect)
  · exact valid_effect_reply_retains_resumption_and_consumes_one_owner.1
  · rfl
  · exact Ne.symm equal_payloads_have_independent_issued_authority.2.1
  · simp [capture, CapturedReadView.consult, CapturedReadView.admit]
  · simp [capture, CapturedReadView.consult, CapturedReadView.admit]
  · simp

/-- Support disjointness is sufficient, but harmless writes to consulted keys
can also pass the exact revision guard. The retained capture is unchanged. -/
theorem benign_write_to_consulted_key_keeps_admission :
    let observed : Capture Nat (Option Nat) :=
      {capture with view := (CapturedReadView.admit world).consult world 1}
    ¬ List.Disjoint observed.view.consulted (([(1, 3)] : List (Nat × Nat)).map Prod.fst) ∧
      (deliverChecked remaining (world.update 1 (some 3)) observed second returnedEffect).1 =
        .ok (resumeWait, ⟨19, []⟩) := by
  refine ⟨?_, rfl⟩
  simp [CapturedReadView.consult, CapturedReadView.admit]

/-- Distinct authority alone does not permit reordering a write which changes
the other consumer's consulted absence. The sibling row still exists. -/
theorem independent_authority_does_not_override_changed_dependencies :
    IssuedReturn.Authenticated remaining second ∧
      (deliverChecked remaining (world.update 0 (some 7)) capture second returnedEffect).1 =
        .error .staleDependencies := by
  refine ⟨?_, rfl⟩
  simp [IssuedReturn.Authenticated, remaining, second, secondRow]

theorem cancellation_retains_all_paid_data_and_sibling_authority :
    (cancel registry capture first).1 = some (remaining, capture) ∧
      IssuedReturn.Authenticated remaining second ∧
      (deliverChecked remaining world capture first returnedEffect).1 = .error .unissued := by
  refine ⟨rfl, ?_, rfl⟩
  simp [IssuedReturn.Authenticated, remaining, second, secondRow]

theorem stale_dependencies_do_not_prevent_owned_cancellation :
    (cancel registry poisoned first).1 = some (remaining, poisoned) := rfl

theorem a_different_parent_cannot_cancel_an_issued_row :
    cancel registry capture {first with parent := 8} = (none, 0) := rfl

private def observedCapture : Capture RevisionDependencySetCanary.Store Nat :=
  ⟨5, AuthorityObservationControls.capture, effectWait⟩

theorem dependency_observer_bookkeeping_is_retained_at_admission :
    let checked := RevisionEnvironment.checkObserved observedCapture.view.captured
      AuthorityObservationControls.stableObserve observedCapture.view.consulted AuthorityObservationControls.initial
    checked.2.cacheTicks = 2 ∧
      (deliverChecked registry (AuthorityObservationControls.projection checked.2)
        observedCapture first returnedEffect).1 = .ok (resumeWait, remaining) := ⟨rfl, rfl⟩

/-- Truthful individual reads can still invalidate an earlier consulted key.
The final-world guard refuses, retaining the two paid observer operations. -/
theorem truthful_reads_without_support_stability_cannot_authorize_delivery :
    let checked := RevisionEnvironment.checkObserved observedCapture.view.captured
      AuthorityObservationControls.lateObserve observedCapture.view.consulted AuthorityObservationControls.initial
    checked.1 = true ∧ checked.2.cacheTicks = 2 ∧
      (deliverChecked registry (AuthorityObservationControls.projection checked.2)
        observedCapture first returnedEffect).1 = .error .staleDependencies := ⟨rfl, rfl, rfl⟩

end OwnedControls

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControlControls
