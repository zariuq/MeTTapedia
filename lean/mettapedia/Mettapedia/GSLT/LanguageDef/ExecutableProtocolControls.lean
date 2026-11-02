import Mettapedia.GSLT.LanguageDef.ExecutableProtocolComposition

/-! Finite protocol controls keep complete replies, state and ordered calls.
Recorded target mutations demonstrate that source admission alone cannot
justify an independently emitted program. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Controls

def eligible : Hook := ⟨"eligible", "can_run", .guard, [], [], ["ready"], []⟩
def prepare : Hook := ⟨"prepare", "resolve", .prepare, ["ready"], [], ["arguments"], []⟩
def execute : Hook := ⟨"execute", "run_effect", .effect, ["arguments"], ["frame"], [], []⟩
def frame : Resource := ⟨"frame", "open_frame", "close_frame", "move_frame", [], []⟩

def executionBody : Body :=
  .call "eligible"
    (.call "prepare"
      (.acquire "frame"
        (.call "execute" (.transfer "frame" (.ret .answered))
          (.release "frame" (.ret .raised)))
        (.ret .resource_failure))
      (.ret .declined))
    (.ret .declined)

def exampleProtocol : Protocol :=
  ⟨"invoke", "Invocation", [eligible, prepare, execute], [frame], [], [], executionBody, []⟩

/-- An independently written target, not a definition by applying `lower`. -/
def expectedC : CStmt :=
  .ifCall "can_run"
    (.ifCall "resolve"
      (.ifCall "open_frame"
        (.ifCall "run_effect" (.voidCall "move_frame" (.ret .answered))
          (.voidCall "close_frame" (.ret .raised)))
        (.ret .resource_failure))
      (.ret .declined))
    (.ret .declined)

def examplePlan : Plan := ⟨exampleProtocol, expectedC⟩

def host : Host Nat where
  boolean := fun _ world reply => 2 * world + if reply then 1 else 0
  void := fun _ world => world + 100

theorem source_admitted : check exampleProtocol = true := by decide
theorem source_well_formed : Valid exampleProtocol := (check_iff _).mp source_admitted
theorem target_is_actual_lowering : lower exampleProtocol executionBody = some expectedC := by decide
theorem recorded_plan_admitted : checkPlan examplePlan = true := by decide
theorem recorded_plan_valid : PlanValid examplePlan := (checkPlan_iff _).mp recorded_plan_admitted

theorem successful_execution : evalC host expectedC 0 [true, true, true, true, false] =
    ⟨.returned .answered, 115, [false],
      [.boolean "can_run" true, .boolean "resolve" true, .boolean "open_frame" true,
        .boolean "run_effect" true, .void "move_frame"]⟩ := by decide

theorem early_refusal_skips_preparation : evalC host expectedC 7 [false, true] =
    ⟨.returned .declined, 14, [true], [.boolean "can_run" false]⟩ := by decide

theorem preparation_refusal_retains_its_call : evalC host expectedC 0 [true, false, true] =
    ⟨.returned .declined, 2, [true],
      [.boolean "can_run" true, .boolean "resolve" false]⟩ := by decide

theorem allocation_failure_has_no_disposal : evalC host expectedC 0 [true, true, false] =
    ⟨.returned .resource_failure, 6, [],
      [.boolean "can_run" true, .boolean "resolve" true, .boolean "open_frame" false]⟩ := by decide

theorem failed_effect_is_not_decline : evalC host expectedC 0 [true, true, true, false] =
    ⟨.returned .raised, 114, [],
      [.boolean "can_run" true, .boolean "resolve" true, .boolean "open_frame" true,
        .boolean "run_effect" false, .void "close_frame"]⟩ := by decide

theorem missing_reply_does_not_invent_return : evalC host expectedC 0 [true, true, true] =
    ⟨.noReply "run_effect", 7, [],
      [.boolean "can_run" true, .boolean "resolve" true, .boolean "open_frame" true]⟩ := by decide

theorem source_state_and_trace_preserved (world : Nat) (replies : List Bool) :
    evalC host expectedC world replies =
      evalSource exampleProtocol host executionBody world replies :=
  lower_eval_exact _ _ _ _ target_is_actual_lowering _ _

theorem every_decline_is_effect_free (world : Nat) (replies : List Bool)
    (declined : (evalC host expectedC world replies).status = .returned .declined) :
    ∀ event ∈ (evalC host expectedC world replies).calls, ¬ EffectEvent exampleProtocol event :=
  lower_decline_has_no_effect source_well_formed.metadata source_well_formed.body
    expectedC target_is_actual_lowering host world replies declined

theorem every_decline_is_publication_free (world : Nat) (replies : List Bool)
    (declined : (evalC host expectedC world replies).status = .returned .declined) :
    ∀ event ∈ (evalC host expectedC world replies).calls,
      ¬ IrreversibleEvent exampleProtocol event :=
  lower_decline_has_no_publication source_well_formed.metadata source_well_formed.body
    expectedC target_is_actual_lowering host world replies declined

theorem transfer_call_is_irreversible :
    IrreversibleEvent exampleProtocol (.void "move_frame") := by
  unfold IrreversibleEvent
  decide

theorem release_call_can_remain_reversible :
    ¬ IrreversibleEvent exampleProtocol (.void "close_frame") := by
  unfold IrreversibleEvent
  decide

theorem unsuccessful_effect_call_is_irreversible :
    IrreversibleEvent exampleProtocol (.boolean "run_effect" false) := by
  unfold IrreversibleEvent
  decide

def withBody (body : Body) : Protocol := { exampleProtocol with body := body }

theorem missing_fact_refused : check (withBody
    (.call "prepare" (.ret .done) (.ret .declined))) = false := by decide

theorem false_guard_does_not_prove_facts : check (withBody
    (.call "eligible" (.ret .done)
      (.call "prepare" (.ret .done) (.ret .declined)))) = false := by decide

theorem unowned_resource_use_refused : check { exampleProtocol with
    entryFacts := ["arguments"], body :=
      .call "execute" (.ret .answered) (.ret .raised) } = false := by decide

theorem leaked_owner_refused : check (withBody
    (.acquire "frame" (.ret .done) (.ret .resource_failure))) = false := by decide

theorem suspension_cannot_hide_owner : check (withBody
    (.acquire "frame" (.ret .suspended) (.ret .resource_failure))) = false := by decide

theorem raised_cannot_hide_owner : check (withBody
    (.acquire "frame" (.ret .raised) (.ret .resource_failure))) = false := by decide

theorem failure_cannot_hide_owner : check (withBody
    (.acquire "frame" (.ret .engine_failure) (.ret .resource_failure))) = false := by decide

theorem release_requires_owner : check (withBody
    (.release "frame" (.ret .done))) = false := by decide

theorem transfer_requires_owner : check (withBody
    (.transfer "frame" (.ret .done))) = false := by decide

theorem acquired_transfer_cannot_decline : check (withBody
    (.acquire "frame" (.transfer "frame" (.ret .declined))
      (.ret .resource_failure))) = false := by decide

theorem entry_transfer_cannot_decline : check { exampleProtocol with
    entryOwned := ["frame"], body := .transfer "frame" (.ret .declined) } = false := by decide

theorem release_may_remain_reversible : check (withBody
    (.acquire "frame" (.release "frame" (.ret .declined)) (.ret .declined))) = true := by decide

theorem transferred_context_blocks_continued_decline :
    let published := transferContext ⟨[], ["frame"], false⟩ "frame"
    checkBody exampleProtocol (continuationEntry exampleProtocol published)
      (.ret .declined) = false := by decide

theorem transferred_context_allows_continued_failure :
    let published := transferContext ⟨[], ["frame"], false⟩ "frame"
    checkBody exampleProtocol { published with owned := [] }
      (.ret .engine_failure) = true := by decide

def guardedFrame : Resource := { frame with
  acquireRequires := ["ready"], transferRequires := ["arguments"] }

theorem allocation_before_admission_fact_refused : check { exampleProtocol with
    resources := [guardedFrame], body :=
      .acquire "frame" (.release "frame" (.ret .done)) (.ret .resource_failure) } = false := by decide

theorem publication_before_validation_fact_refused : check { exampleProtocol with
    resources := [guardedFrame], entryOwned := ["frame"], body :=
      .transfer "frame" (.ret .done) } = false := by decide

theorem guarded_acquisition_and_publication_admitted : check { exampleProtocol with
    resources := [guardedFrame] } = true := by decide

theorem false_guard_cannot_authorize_acquisition : check { exampleProtocol with
    resources := [guardedFrame], body :=
      .call "eligible" (.ret .done)
        (.acquire "frame" (.release "frame" (.ret .done)) (.ret .resource_failure)) } = false := by decide

theorem preparation_false_cannot_authorize_publication : check { exampleProtocol with
    resources := [guardedFrame], entryFacts := ["ready"], entryOwned := ["frame"], body :=
      .call "prepare" (.release "frame" (.ret .done))
        (.transfer "frame" (.ret .done)) } = false := by decide

theorem duplicate_acquisition_prerequisite_refused : check { exampleProtocol with
    resources := [{ frame with acquireRequires := ["ready", "ready"] }],
    body := .ret .done } = false := by decide

theorem duplicate_publication_prerequisite_refused : check { exampleProtocol with
    resources := [{ frame with transferRequires := ["ready", "ready"] }],
    body := .ret .done } = false := by decide

theorem invalid_acquisition_fact_name_refused : check { exampleProtocol with
    resources := [{ frame with acquireRequires := ["bad-fact"] }],
    body := .ret .done } = false := by decide

theorem invalid_publication_fact_name_refused : check { exampleProtocol with
    resources := [{ frame with transferRequires := ["bad-fact"] }],
    body := .ret .done } = false := by decide

theorem failed_acquire_does_not_create_owner : check (withBody
    (.acquire "frame" (.release "frame" (.ret .done))
      (.release "frame" (.ret .resource_failure)))) = false := by decide

theorem double_acquire_refused : check (withBody
    (.acquire "frame"
      (.acquire "frame" (.release "frame" (.ret .done))
        (.release "frame" (.ret .resource_failure)))
      (.ret .resource_failure))) = false := by decide

theorem double_release_refused : check { exampleProtocol with
    entryOwned := ["frame"],
    body := .release "frame" (.release "frame" (.ret .done)) } = false := by decide

theorem transfer_then_release_refused : check { exampleProtocol with
    entryOwned := ["frame"],
    body := .transfer "frame" (.release "frame" (.ret .done)) } = false := by decide

theorem entry_owner_can_transfer_to_suspension : check { exampleProtocol with
    entryOwned := ["frame"], body := .transfer "frame" (.ret .suspended) } = true := by decide

theorem entry_owner_can_release_on_failure : check { exampleProtocol with
    entryOwned := ["frame"], body := .release "frame" (.ret .engine_failure) } = true := by decide

theorem entry_owner_must_be_declared : check { exampleProtocol with
    entryOwned := ["missing"], body := .ret .done } = false := by decide

theorem duplicate_entry_owner_refused : check { exampleProtocol with
    entryOwned := ["frame", "frame"], body := .release "frame" (.ret .done) } = false := by decide

def effectOnly : Hook := ⟨"effect_only", "effect_only_c", .effect, [], [], [], []⟩

theorem false_effect_also_blocks_decline : check { exampleProtocol with
    hooks := [effectOnly], body :=
      .call "effect_only" (.ret .done) (.ret .declined) } = false := by decide

theorem true_effect_blocks_decline : check { exampleProtocol with
    hooks := [effectOnly], body :=
      .call "effect_only" (.ret .declined) (.ret .raised) } = false := by decide

theorem pure_prepare_can_decline : check { exampleProtocol with
    hooks := [⟨"prepare", "prepare_c", .prepare, [], [], [], []⟩], body :=
      .call "prepare" (.ret .declined) (.ret .declined) } = true := by decide

theorem unknown_hook_refused : check (withBody
    (.call "missing" (.ret .done) (.ret .raised))) = false := by decide

theorem unknown_hook_has_no_target : lower exampleProtocol
    (.call "missing" (.ret .done) (.ret .raised)) = none := by decide

theorem unknown_resource_refused : check (withBody
    (.acquire "missing" (.ret .done) (.ret .raised))) = false := by decide

theorem duplicate_hook_id_refused : check { exampleProtocol with
    hooks := [eligible, { eligible with cName := "other" }] } = false := by decide

theorem duplicate_resource_id_refused : check { exampleProtocol with
    resources := [frame, { frame with
      acquire := "open_other", release := "close_other", transfer := "move_other" }] } = false := by decide

theorem hook_resource_c_name_collision_refused : check { exampleProtocol with
    resources := [{ frame with acquire := "can_run" }] } = false := by decide

theorem undeclared_hook_resource_refused : check { exampleProtocol with
    hooks := [{ eligible with uses := ["missing"] }], body := .ret .done } = false := by decide

theorem invalid_identifier_refused : check { exampleProtocol with
    name := "has-dash" } = false := by decide

/-- Logical hook and resource IDs have separate source namespaces. -/
theorem sorted_id_namespaces_can_overlap : check { exampleProtocol with
    hooks := [{ eligible with id := "frame" }], body :=
      .call "frame" (.ret .done) (.ret .done) } = true := by decide

def repeated : Protocol := { exampleProtocol with
  hooks := [eligible], body :=
    .call "eligible" (.call "eligible" (.ret .answered) (.ret .raised)) (.ret .declined) }

theorem duplicate_entry_fact_refused : check { exampleProtocol with
    entryFacts := ["ready", "ready"] } = false := by decide

theorem duplicate_required_fact_refused : check { exampleProtocol with
    hooks := [{ eligible with requires := ["ready", "ready"] }],
    body := .ret .done } = false := by decide

theorem duplicate_used_resource_refused : check { exampleProtocol with
    hooks := [{ eligible with uses := ["frame", "frame"] }],
    body := .ret .done } = false := by decide

theorem duplicate_proved_fact_refused : check { exampleProtocol with
    hooks := [{ eligible with proves := ["ready", "ready"] }],
    body := .ret .done } = false := by decide

theorem repeated_calls_admitted : check repeated = true := by decide

theorem repeated_call_occurrences_retained : evalSource repeated host repeated.body 0 [true, false] =
    ⟨.returned .raised, 2, [], [.boolean "can_run" true, .boolean "can_run" false]⟩ := by decide

theorem extra_call_target_refused : checkPlan
    ⟨exampleProtocol, .voidCall "surprise" expectedC⟩ = false := by decide

theorem changed_reply_branch_target_refused : checkPlan
    ⟨exampleProtocol, .ifCall "can_run" expectedC (.ret .answered)⟩ = false := by decide

theorem omitted_preparation_target_refused : checkPlan
    ⟨exampleProtocol, .ifCall "can_run" (.ret .answered) (.ret .declined)⟩ = false := by decide

/-- The source remains admitted while an independently changed target adds
behavior. Exact recorded-target admission is therefore necessary. -/
theorem source_admission_does_not_validate_extra_target_behavior :
    check exampleProtocol = true ∧
      evalC host (.voidCall "surprise" expectedC) 0 [false] ≠
        evalSource exampleProtocol host exampleProtocol.body 0 [false] := by decide

/-- Equality of final outcomes alone misses an extra observable call and
state change, even when the source's result is still realized. -/
theorem matching_outcome_is_not_complete_observation :
    (evalC host (.voidCall "surprise" expectedC) 0 [false]).status =
        (evalC host expectedC 0 [false]).status ∧
      (evalC host (.voidCall "surprise" expectedC) 0 [false]).calls ≠
        (evalC host expectedC 0 [false]).calls ∧
      (evalC host (.voidCall "surprise" expectedC) 0 [false]).world ≠
        (evalC host expectedC 0 [false]).world := by decide

def firstEffect : Protocol := { exampleProtocol with
  name := "first_stage", hooks := [effectOnly], resources := [], body :=
    .call "effect_only" (.ret .done) (.ret .raised) }

def localDecline : Protocol := { exampleProtocol with
  name := "second_stage", hooks := [], resources := [], body := .ret .declined }

def inheritedEffect : Context := ⟨[], [], true⟩

theorem separately_admitted_stages_do_not_reset_effects :
    check firstEffect = true ∧ check localDecline = true ∧
      checkBody localDecline (continuationEntry localDecline inheritedEffect)
        localDecline.body = false := by decide

theorem unchecked_composition_can_decline_after_effect :
    evalC host (sequenceTarget
      (.ifCall "effect_only_c" (.ret .done) (.ret .raised))
      (.ret .declined) (fun outcome => outcome == .done)) 0 [true, false] =
        ⟨.returned .declined, 1, [false], [.boolean "effect_only_c" true]⟩ := by decide

theorem inherited_effect_allows_suspension :
    checkBody localDecline (continuationEntry localDecline inheritedEffect)
      (.ret .suspended) = true := by decide

def finish : CStmt := .ifCall "finish" (.ret .done) (.ret .engine_failure)

theorem failure_retains_first_stage_trace_state_and_reply_suffix :
    evalC host (sequenceTarget expectedC finish (fun outcome => outcome == .answered))
      0 [true, true, true, true, false, true] =
        ⟨.returned .engine_failure, 230, [true],
          [.boolean "can_run" true, .boolean "resolve" true, .boolean "open_frame" true,
            .boolean "run_effect" true, .void "move_frame", .boolean "finish" false]⟩ := by decide

theorem failure_retains_charged_prefix :
    invoice (fun _ => 1)
      (evalC host (sequenceTarget expectedC finish (fun outcome => outcome == .answered))
        0 [true, true, true, true, false]).calls = 5 + 1 := by decide

def transferStage : Protocol := { exampleProtocol with
  name := "transfer_stage", hooks := [], entryOwned := ["frame"],
  body := .transfer "frame" (.ret .done) }

def releaseStage : Protocol := { exampleProtocol with
  name := "release_stage", hooks := [], entryOwned := ["frame"],
  body := .release "frame" (.ret .suspended) }

def transferPlan : Plan := ⟨transferStage, .voidCall "move_frame" (.ret .done)⟩
def releasePlan : Plan := ⟨releaseStage, .voidCall "close_frame" (.ret .suspended)⟩

theorem ownership_stages_admitted :
    checkPlan transferPlan = true ∧ checkPlan releasePlan = true := by decide

theorem owner_handoff_continuation_inherits_publication :
    checkBody releaseStage
      (continuationEntry releaseStage (transferContext (initial transferStage) "frame"))
      releaseStage.body = true := by decide

def tokenHost : Host (List Nat) where
  boolean := fun _ world _ => world
  void := fun name world =>
    if name == "move_frame" then 8 :: world.erase 7
    else if name == "close_frame" then world.erase 8 else world

def transferBoundary : TokenBoundary (List Nat) Nat where
  input := [7]
  output := fun _ => [8]
  owns := fun world token => token ∈ world

def releaseBoundary : TokenBoundary (List Nat) Nat where
  input := [8]
  output := fun _ => []
  owns := fun world token => token ∈ world

def onDone (outcome : Outcome) : Bool := outcome == .done

theorem actual_token_handoff_compatible : transferBoundary.Compatible releaseBoundary onDone := by
  intro outcome selected
  exact ⟨List.Sublist.refl _, fun _ _ _ present => present⟩

theorem transfer_host_conforms : transferBoundary.Conforms tokenHost transferPlan.target := by
  intro world replies ready outcome returned
  simp [TokenBoundary.Delivered, transferBoundary, transferPlan, evalC, record, stop,
    tokenHost]

theorem release_host_conforms : releaseBoundary.Conforms tokenHost releasePlan.target := by
  intro world replies ready outcome returned
  simp [TokenBoundary.Delivered, releaseBoundary]

theorem entry_resource_bound_to_actual_token : releaseBoundary.BindsEntry releaseStage
    (fun id => if id == "frame" then some 8 else none) := by
  exact .cons (by decide) .nil

theorem token_sequence_preserves_world_and_calls :
    evalC tokenHost (sequenceTarget transferPlan.target releasePlan.target onDone) [7] [] =
      ⟨.returned .suspended, [], [], [.void "move_frame", .void "close_frame"]⟩ := by decide

theorem no_token_can_be_invented_at_handoff :
    ¬ ({ transferBoundary with output := fun _ => [] }).Compatible releaseBoundary onDone := by
  intro compatible
  have included := (compatible .done (by decide)).1
  have member := included.subset (by simp [releaseBoundary] : 8 ∈ releaseBoundary.input)
  simp at member

theorem duplicate_token_handoff_refused :
    ¬ transferBoundary.Compatible ({ releaseBoundary with input := [8, 8] }) onDone := by
  intro compatible
  have included := (compatible .done (by decide)).1
  have unique : ([8, 8] : List Nat).Nodup := included.nodup (by
    simp [transferBoundary])
  simp at unique

def mutateCurrent : Hook :=
  ⟨"mutate", "mutate_current", .effect, ["current"], [], [], ["current"]⟩

def refreshCurrent : Hook :=
  ⟨"refresh", "refresh_current", .guard, [], [], ["current"], []⟩

def useCurrent : Hook :=
  ⟨"use", "use_current", .effect, ["current"], [], [], []⟩

def afterWrite : Protocol :=
  { name := "after_write", contextType := "CurrentContext"
    hooks := [mutateCurrent, refreshCurrent, useCurrent], resources := []
    entryFacts := ["current"], entryOwned := []
    body := .call "mutate"
      (.call "refresh" (.call "use" (.ret .done) (.ret .raised)) (.ret .raised))
      (.ret .raised) }

theorem revalidated_after_write : check afterWrite = true := by decide

theorem stale_after_success_refused :
    check { afterWrite with body := (.call "mutate"
      (.call "use" (.ret .done) (.ret .raised)) (.ret .raised)) } = false := by decide

theorem stale_after_failure_refused :
    check { afterWrite with body := (.call "mutate" (.ret .raised)
      (.call "use" (.ret .done) (.ret .raised))) } = false := by decide

theorem failed_hook_still_invalidates :
    "current" ∉ (callContext (initial afterWrite) mutateCurrent false).facts := by decide

theorem forgotten_is_not_negated :
    (callContext (initial afterWrite) { refreshCurrent with proves := [], invalidates := ["current"] }
      true).facts = [] := by decide

#print axioms revalidated_after_write
#print axioms stale_after_success_refused
#print axioms stale_after_failure_refused

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Controls
