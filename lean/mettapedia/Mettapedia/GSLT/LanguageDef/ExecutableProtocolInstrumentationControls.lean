import Mettapedia.GSLT.LanguageDef.ExecutableProtocolInstrumentationCorrectness

/-!
# Checked protocol controls

The target fixture is authored separately from the lowering function. The
host has actual fact/ownership fields, including deliberately dishonest
acquisition and disposal implementations used as negative controls. These
finite examples do not assert conformance of arbitrary native predicates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation.Controls

def protocol : Protocol :=
  { name := "admit"
    contextType := "Context"
    hooks := [
      ⟨"guard", "admit_guard", .guard, ["input"], [], ["valid"], []⟩,
      ⟨"ready", "admit_ready", .prepare, ["valid"], ["pending"], ["reserved"], []⟩]
    resources := [⟨"pending", "admit_acquire", "admit_release", "admit_transfer",
      ["valid"], ["reserved"]⟩]
    entryFacts := ["input"]
    entryOwned := []
    body := .call "guard"
      (.acquire "pending"
        (.call "ready" (.transfer "pending" (.ret .answered))
          (.release "pending" (.ret .declined)))
        (.ret .declined))
      (.ret .declined) }

def checks : List Validator := [
  ⟨.fact, "input", "check_input"⟩,
  ⟨.fact, "valid", "check_valid"⟩,
  ⟨.fact, "reserved", "check_reserved"⟩,
  ⟨.own, "pending", "check_pending"⟩]

def inputCheck : Check := ⟨.fact, "input", "check_input", true⟩
def validCheck : Check := ⟨.fact, "valid", "check_valid", true⟩
def reservedCheck : Check := ⟨.fact, "reserved", "check_reserved", true⟩
def ownerCheck (expected : Bool) : Check := ⟨.own, "pending", "check_pending", expected⟩

def finish (outcome : Outcome) (last : DeclineKey) : IStmt :=
  .validate (ownerCheck false)
    (if outcome = .declined then .tick last (.ret .declined) else .ret outcome)

/-- An independently authored recorded target, including duplicate checks
where one check is a postcondition and the next is an exit obligation. -/
def target : IStmt :=
  .validate inputCheck (.validate (ownerCheck false)
    (.validate inputCheck
      (.ifCall "admit_guard"
        (.validate validCheck (.validate (ownerCheck false)
          (.ifCall "admit_acquire"
            (.validate (ownerCheck true)
              (.validate validCheck (.validate (ownerCheck true)
                (.ifCall "admit_ready"
                  (.validate (ownerCheck true) (.validate reservedCheck
                    (.voidCall "admit_transfer" (.validate (ownerCheck false)
                      (finish .answered (.afterBool "admit_ready" true))))))
                  (.validate (ownerCheck true)
                    (.voidCall "admit_release" (.validate (ownerCheck false)
                      (finish .declined (.afterBool "admit_ready" false)))))))))
            (.validate (ownerCheck false)
              (finish .declined (.afterBool "admit_acquire" false))))))
        (finish .declined (.afterBool "admit_guard" false)))))

def plan : RecordedPlan := ⟨protocol, checks, target⟩

theorem source_admitted : ExecutableProtocol.check protocol = true := by decide
theorem mappings_admitted : checkChecks protocol checks = true := by decide
theorem target_admitted : checkPlan plan = true := by decide
theorem valid : PlanValid plan := (checkPlan_iff plan).mp target_admitted
theorem erased_target_is_source_lowering : lower protocol protocol.body = some target.erase :=
  instrument_erases protocol checks target valid.target
theorem target_counter_discipline : Disciplined .entry target :=
  instrument_disciplined protocol checks target valid.target

def missingOwner : RecordedPlan :=
  { plan with checks := checks.filter fun v => v.kind == .fact }

theorem missing_mapping_unavailable : instrument protocol missingOwner.checks = none := by decide
theorem missing_mapping_refused : checkPlan missingOwner = false := by decide

def duplicateMapping : RecordedPlan :=
  { plan with checks := ⟨.fact, "input", "another_input"⟩ :: checks }

theorem duplicate_mapping_refused : checkPlan duplicateMapping = false := by decide

def unknownMapping : RecordedPlan :=
  { plan with checks := ⟨.fact, "unproved", "check_unproved"⟩ :: checks }

theorem undeclared_fact_mapping_refused : checkPlan unknownMapping = false := by decide

def unknownOwner : RecordedPlan :=
  { plan with checks := ⟨.own, "foreign", "check_foreign"⟩ :: checks }

theorem undeclared_owner_mapping_refused : checkPlan unknownOwner = false := by decide

def invalidName : RecordedPlan :=
  { plan with checks := checks.map fun v => { v with cName := "bad-name" } }

theorem invalid_predicate_name_refused : checkPlan invalidName = false := by decide

def extraCall : RecordedPlan := { plan with target := .voidCall "unlisted" target }
theorem extra_call_refused : checkPlan extraCall = false := by decide

def erasedChecks : RecordedPlan := { plan with target := .ret .declined }
theorem erased_checks_refused : checkPlan erasedChecks = false := by decide

def wrongExpected : RecordedPlan :=
  { plan with target := match target with
      | .validate check next => .validate { check with expected := false } next
      | other => other }

theorem wrong_expected_value_refused : checkPlan wrongExpected = false := by decide

def wrongReasons : IStmt → IStmt
  | .ret outcome => .ret outcome
  | .ifCall name yes no => .ifCall name (wrongReasons yes) (wrongReasons no)
  | .voidCall name next => .voidCall name (wrongReasons next)
  | .validate check next => .validate check (wrongReasons next)
  | .tick _ next => .tick .entry (wrongReasons next)

def wrongReasonPlan : RecordedPlan := { plan with target := wrongReasons target }
theorem wrong_decline_reason_refused : checkPlan wrongReasonPlan = false := by decide

structure World where
  input : Bool
  valid : Bool
  owned : Bool
  reserved : Bool
  deriving DecidableEq, Repr

def initialWorld : World := ⟨true, false, false, false⟩

def host : Host World :=
  { boolean := fun name world reply =>
      if name = "admit_guard" then { world with valid := reply }
      else if name = "admit_acquire" then { world with owned := reply }
      else if name = "admit_ready" then { world with reserved := reply }
      else world
    void := fun name world =>
      if name = "admit_release" ∨ name = "admit_transfer" then { world with owned := false }
      else world }

def validator (name : String) (world : World) : Bool :=
  if name = "check_input" then world.input
  else if name = "check_valid" then world.valid
  else if name = "check_reserved" then world.reserved
  else if name = "check_pending" then world.owned
  else false

def run (replies : List Bool) : Result World :=
  eval ⟨true, true⟩ host validator target initialWorld replies emptyCounters

theorem success_outcome : (run [true, true, true, false]).status = .core (.returned .answered) :=
  by decide
theorem success_reply_suffix : (run [true, true, true, false]).remaining = [false] := by decide
theorem success_owners_discharged : (run [true, true, true]).world.owned = false := by decide
theorem success_calls : coreCalls (run [true, true, true]).observations =
    [.boolean "admit_guard" true, .boolean "admit_acquire" true,
      .boolean "admit_ready" true, .void "admit_transfer"] := by decide
theorem success_not_counted : declineKeys (run [true, true, true]).observations = [] := by decide

theorem guard_refusal_outcome : (run [false, true]).status = .core (.returned .declined) := by decide
theorem guard_refusal_suffix : (run [false, true]).remaining = [true] := by decide
theorem guard_refusal_has_no_preparation : coreCalls (run [false]).observations =
    [.boolean "admit_guard" false] := by decide
theorem guard_refusal_reason : declineKeys (run [false]).observations =
    [.afterBool "admit_guard" false] := by decide
theorem guard_refusal_count : ((run [false]).counters (.afterBool "admit_guard" false)).val = 1 :=
  by decide
theorem guard_refusal_other_count : ((run [false]).counters (.afterBool "admit_ready" false)).val = 0 :=
  by decide

theorem acquisition_refusal_outcome : (run [true, false]).status = .core (.returned .declined) :=
  by decide
theorem acquisition_refusal_calls : coreCalls (run [true, false]).observations =
    [.boolean "admit_guard" true, .boolean "admit_acquire" false] := by decide
theorem acquisition_refusal_reason : declineKeys (run [true, false]).observations =
    [.afterBool "admit_acquire" false] := by decide

theorem cleanup_refusal_outcome : (run [true, true, false]).status = .core (.returned .declined) :=
  by decide
theorem cleanup_refusal_calls : coreCalls (run [true, true, false]).observations =
    [.boolean "admit_guard" true, .boolean "admit_acquire" true,
      .boolean "admit_ready" false, .void "admit_release"] := by decide
theorem cleanup_preserves_boolean_reason : declineKeys (run [true, true, false]).observations =
    [.afterBool "admit_ready" false] := by decide
theorem cleanup_exactly_one_count :
    ((run [true, true, false]).counters (.afterBool "admit_ready" false)).val = 1 := by decide

theorem empty_reply_is_not_decline : (run []).status = .core (.noReply "admit_guard") := by decide
theorem empty_reply_is_not_counted : declineKeys (run []).observations = [] := by decide
theorem missing_acquisition_reply : (run [true]).status = .core (.noReply "admit_acquire") := by decide

def failedEntry : Result World :=
  eval ⟨true, true⟩ host validator target { initialWorld with input := false }
    [true, true, true] emptyCounters

theorem failed_entry_diagnostic : failedEntry.status = .failedCheck inputCheck false := by decide
theorem failed_entry_no_calls : coreCalls failedEntry.observations = [] := by decide
theorem failed_entry_no_count : declineKeys failedEntry.observations = [] := by decide
theorem failed_entry_preserves_replies : failedEntry.remaining = [true, true, true] := by decide

def falseFactHost : Host World :=
  { host with boolean := fun name world reply =>
      if name = "admit_guard" then { world with valid := false }
      else host.boolean name world reply }

def falseFact : Result World :=
  eval ⟨true, true⟩ falseFactHost validator target initialWorld [true, true, true] emptyCounters

theorem false_fact_before_use_detected : falseFact.status = .failedCheck validCheck false := by decide
theorem false_fact_prevents_acquisition : coreCalls falseFact.observations =
    [.boolean "admit_guard" true] := by decide
theorem false_fact_does_not_count_decline : declineKeys falseFact.observations = [] := by decide

def lyingAcquireHost : Host World :=
  { host with boolean := fun name world reply =>
      if name = "admit_acquire" then { world with owned := true }
      else host.boolean name world reply }

def lyingAcquire : Result World :=
  eval ⟨true, true⟩ lyingAcquireHost validator target initialWorld [true, false] emptyCounters

theorem lying_failed_acquisition_detected :
    lyingAcquire.status = .failedCheck (ownerCheck false) true := by decide
theorem lying_failed_acquisition_no_next_call : coreCalls lyingAcquire.observations =
    [.boolean "admit_guard" true, .boolean "admit_acquire" false] := by decide
theorem lying_failed_acquisition_no_decline_count : declineKeys lyingAcquire.observations = [] :=
  by decide

def lyingReleaseHost : Host World :=
  { host with void := fun name world =>
      if name = "admit_release" then world else host.void name world }

def lyingRelease : Result World :=
  eval ⟨true, true⟩ lyingReleaseHost validator target initialWorld [true, true, false] emptyCounters

theorem forgotten_release_detected : lyingRelease.status = .failedCheck (ownerCheck false) true :=
  by decide
theorem forgotten_release_not_decline : lyingRelease.status ≠ .core (.returned .declined) := by decide
theorem forgotten_release_no_count : declineKeys lyingRelease.observations = [] := by decide

def lyingTransferHost : Host World :=
  { host with void := fun name world =>
      if name = "admit_transfer" then world else host.void name world }

def lyingTransfer : Result World :=
  eval ⟨true, true⟩ lyingTransferHost validator target initialWorld [true, true, true] emptyCounters

theorem forgotten_transfer_detected : lyingTransfer.status = .failedCheck (ownerCheck false) true :=
  by decide
theorem forgotten_transfer_not_answered : lyingTransfer.status ≠ .core (.returned .answered) :=
  by decide

theorem honest_path_checks_pass :
    checksPass true host validator target initialWorld [true, true, true] = true := by decide
theorem dishonest_path_checks_fail :
    checksPass true falseFactHost validator target initialWorld [true, true, true] = false := by decide
theorem passing_path_source_correspondence :
    (run [true, true, true]).project =
      some (evalSource protocol host protocol.body initialWorld [true, true, true]) :=
  valid.passing_eval_exact ⟨true, true⟩ host validator initialWorld _ emptyCounters honest_path_checks_pass
theorem failed_path_static_resource_discipline :
    ∃ last, Trace protocol (initial protocol) (coreCalls lyingRelease.observations) last :=
  valid.calls_enabled ⟨true, true⟩ lyingReleaseHost validator initialWorld _ emptyCounters

theorem disabled_execution_exact :
    eval ⟨false, false⟩ falseFactHost validator target initialWorld [true, true, true] emptyCounters =
      liftCore (evalSource protocol falseFactHost protocol.body initialWorld [true, true, true])
        emptyCounters := valid.disabled_eval_exact falseFactHost validator initialWorld _ emptyCounters

theorem unchecked_bad_host_ordinary_outcome :
    (eval ⟨false, false⟩ falseFactHost validator target initialWorld [true, true, true]
      emptyCounters).status = .core (.returned .answered) := by decide

def countedOnly : Result World :=
  eval ⟨false, true⟩ host validator target initialWorld [false] emptyCounters

theorem counted_only_original_calls : coreCalls countedOnly.observations =
    [.boolean "admit_guard" false] := by decide
theorem counted_only_counter_enabled :
    (countedOnly.counters (.afterBool "admit_guard" false)).val = 1 := by decide
theorem counted_only_no_validation_events : countedOnly.observations =
    [.call (.boolean "admit_guard" false), .decline (.afterBool "admit_guard" false)] := by decide

def nearMaximum : Counter := ⟨counterBound - 2, by decide⟩

theorem zero_counts_to_one : (saturatingSucc counterZero).val = 1 := by decide
theorem next_to_maximum_counts_to_maximum : saturatingSucc nearMaximum = counterMax := by decide
theorem maximum_is_saturated : saturatingSucc counterMax = counterMax := saturatingSucc_max
theorem saturation_does_not_wrap : (saturatingSucc counterMax).val ≠ 0 := by decide

def saturatedRun : Result World :=
  eval ⟨true, true⟩ host validator target initialWorld [false] (fun _ => counterMax)

theorem saturated_run_still_records_decline : declineKeys saturatedRun.observations =
    [.afterBool "admit_guard" false] := by decide
theorem saturated_run_numeric_count_stays_maximum :
    saturatedRun.counters (.afterBool "admit_guard" false) = counterMax := by decide

def secondDecline : Result World :=
  eval ⟨true, true⟩ host validator target initialWorld [false] (run [false]).counters

theorem repeated_declines_count_twice :
    (secondDecline.counters (.afterBool "admit_guard" false)).val = 2 := by decide

def entryProtocol : Protocol :=
  { name := "entry_protocol", contextType := "Context", hooks := [], resources := [],
    entryFacts := [], entryOwned := [], body := .ret .declined }

def entryPlan : RecordedPlan := ⟨entryProtocol, [], .tick .entry (.ret .declined)⟩

theorem entry_decline_plan_admitted : checkPlan entryPlan = true := by decide
theorem entry_decline_uses_entry_counter :
    declineKeys (eval ⟨true, true⟩ host validator entryPlan.target initialWorld []
      emptyCounters).observations = [.entry] := by decide

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation.Controls
