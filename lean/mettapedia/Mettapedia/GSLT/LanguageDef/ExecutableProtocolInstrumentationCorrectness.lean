import Mettapedia.GSLT.LanguageDef.ExecutableProtocolInstrumentation

/-!
# Instrumented protocol correspondence

Successful instrumentation erases to the independently defined ordinary
lowering. A normal instrumented execution retains exactly the source result,
host world, ordinary call/reply trace and unconsumed reply suffix. Validation
failure is a distinct fail-stop observation and is never reflected as an
ordinary source outcome. Decline instructions are separately checked against
the last ordinary Boolean decision, with explicit saturating accounting.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation

theorem wrap_erase (checks : List Validator) (requests : List Request)
    (next target : IStmt) (compiled : wrap checks requests next = some target) :
    target.erase = next.erase := by
  simp only [wrap, Option.map_eq_some_iff] at compiled
  obtain ⟨cs, _, rfl⟩ := compiled
  exact IStmt.erase_validateMany cs next

theorem Disciplined.validateMany {last : DeclineKey} {next : IStmt}
    (disciplined : Disciplined last next) (checks : List Check) :
    Disciplined last (IStmt.validateMany checks next) := by
  induction checks with
  | nil => exact disciplined
  | cons check rest ih => exact .validate last check _ ih

theorem wrap_disciplined (checks : List Validator) (requests : List Request)
    (last : DeclineKey) (next target : IStmt)
    (compiled : wrap checks requests next = some target)
    (disciplined : Disciplined last next) : Disciplined last target := by
  simp only [wrap, Option.map_eq_some_iff] at compiled
  obtain ⟨cs, _, rfl⟩ := compiled
  exact disciplined.validateMany cs

theorem instrumentBody_invariants (p : Protocol) (checks : List Validator)
    (last : DeclineKey) (body : Body) (target : IStmt)
    (compiled : instrumentBody p checks last body = some target) :
    lower p body = some target.erase ∧ Disciplined last target := by
  induction body generalizing last target with
  | ret outcome =>
      have erased := wrap_erase checks (factRequests (exitRequires p outcome) ++ allOwnerRequests p []) _ target compiled
      refine ⟨?_, wrap_disciplined checks (factRequests (exitRequires p outcome) ++ allOwnerRequests p []) last _ target compiled ?_⟩
      · rw [erased]
        by_cases h : outcome = .declined <;> simp [lower, h, IStmt.erase]
      · by_cases h : outcome = .declined
        · subst outcome
          simpa using Disciplined.decline last
        · simpa [h] using Disciplined.ret last outcome h
  | call id yes no ihYes ihNo =>
      simp only [instrumentBody, bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨hook, declared, yes', hy, no', hn, wrapped⟩ := compiled
      obtain ⟨yesLower, yesDiscipline⟩ := ihYes _ yes' hy
      obtain ⟨noLower, noDiscipline⟩ := ihNo _ no' hn
      have erased := wrap_erase checks _ (.ifCall hook.cName yes' no') target wrapped
      refine ⟨?_, wrap_disciplined checks _ last _ target wrapped
        (.ifCall last hook.cName yes' no' yesDiscipline noDiscipline)⟩
      rw [erased]
      simp [lower, declared, yesLower, noLower, IStmt.erase]
  | acquire id yes no ihYes ihNo =>
      simp only [instrumentBody, bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨resource, declared, yes', hy, no', hn, yes'', hyy, no'', hnn, wrapped⟩ := compiled
      obtain ⟨yesLower, yesDiscipline⟩ := ihYes _ yes' hy
      obtain ⟨noLower, noDiscipline⟩ := ihNo _ no' hn
      have yesErase := wrap_erase checks _ yes' yes'' hyy
      have noErase := wrap_erase checks _ no' no'' hnn
      have erased := wrap_erase checks _ (.ifCall resource.acquire yes'' no'') target wrapped
      refine ⟨?_, wrap_disciplined checks _ last _ target wrapped
        (.ifCall last resource.acquire yes'' no''
          (wrap_disciplined checks _ _ yes' yes'' hyy yesDiscipline)
          (wrap_disciplined checks _ _ no' no'' hnn noDiscipline))⟩
      rw [erased]
      simp [lower, declared, yesLower, noLower, IStmt.erase, yesErase, noErase]
  | release id next ih =>
      simp only [instrumentBody, bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨resource, declared, next', hn, after, ha, wrapped⟩ := compiled
      obtain ⟨nextLower, nextDiscipline⟩ := ih last next' hn
      have afterErase := wrap_erase checks _ next' after ha
      have erased := wrap_erase checks _ (.voidCall resource.release after) target wrapped
      refine ⟨?_, wrap_disciplined checks _ last _ target wrapped
        (.voidCall last resource.release after
          (wrap_disciplined checks _ _ next' after ha nextDiscipline))⟩
      rw [erased]
      simp [lower, declared, nextLower, IStmt.erase, afterErase]
  | transfer id next ih =>
      simp only [instrumentBody, bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨resource, declared, next', hn, after, ha, wrapped⟩ := compiled
      obtain ⟨nextLower, nextDiscipline⟩ := ih last next' hn
      have afterErase := wrap_erase checks _ next' after ha
      have erased := wrap_erase checks _ (.voidCall resource.transfer after) target wrapped
      refine ⟨?_, wrap_disciplined checks _ last _ target wrapped
        (.voidCall last resource.transfer after
          (wrap_disciplined checks _ _ next' after ha nextDiscipline))⟩
      rw [erased]
      simp [lower, declared, nextLower, IStmt.erase, afterErase]

theorem instrument_erases (p : Protocol) (checks : List Validator) (target : IStmt)
    (compiled : instrument p checks = some target) :
    lower p p.body = some target.erase := by
  simp only [instrument, bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨body, hb, wrapped⟩ := compiled
  rw [wrap_erase checks _ body target wrapped]
  exact (instrumentBody_invariants p checks .entry p.body body hb).1

theorem instrument_disciplined (p : Protocol) (checks : List Validator) (target : IStmt)
    (compiled : instrument p checks = some target) : Disciplined .entry target := by
  simp only [instrument, bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨body, hb, wrapped⟩ := compiled
  exact wrap_disciplined checks _ .entry body target wrapped
    (instrumentBody_invariants p checks .entry p.body body hb).2

@[simp] theorem coreCalls_call (event : Event) (rest : List Observation) :
    coreCalls (.call event :: rest) = event :: coreCalls rest := rfl

@[simp] theorem coreCalls_validation (check : Check) (actual : Bool)
    (rest : List Observation) :
    coreCalls (.validation check actual :: rest) = coreCalls rest := rfl

@[simp] theorem coreCalls_decline (key : DeclineKey) (rest : List Observation) :
    coreCalls (.decline key :: rest) = coreCalls rest := rfl

@[simp] theorem declineKeys_call (event : Event) (rest : List Observation) :
    declineKeys (.call event :: rest) = declineKeys rest := rfl

@[simp] theorem declineKeys_validation (check : Check) (actual : Bool)
    (rest : List Observation) :
    declineKeys (.validation check actual :: rest) = declineKeys rest := rfl

@[simp] theorem declineKeys_decline (key : DeclineKey) (rest : List Observation) :
    declineKeys (.decline key :: rest) = key :: declineKeys rest := rfl

theorem eval_normal_refines {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) (status : Status)
    (normal : (eval mode host validator target world replies counters).status = .core status) :
    evalC host target.erase world replies =
      ⟨status, (eval mode host validator target world replies counters).world,
        (eval mode host validator target world replies counters).remaining,
        coreCalls (eval mode host validator target world replies counters).observations⟩ := by
  induction target generalizing world replies counters status with
  | ret outcome =>
      simp only [eval, halt, IStatus.core.injEq] at normal
      subst status
      rfl
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil =>
          simp only [eval, halt, IStatus.core.injEq] at normal
          subst status
          rfl
      | cons reply rest =>
          cases reply with
          | false =>
              simpa [eval, IStmt.erase, observe, evalC, record] using
                congrArg (record (.boolean name false))
                  (ihNo (host.boolean name world false) rest counters status normal)
          | true =>
              simpa [eval, IStmt.erase, observe, evalC, record] using
                congrArg (record (.boolean name true))
                  (ihYes (host.boolean name world true) rest counters status normal)
  | voidCall name next ih =>
      simpa [eval, IStmt.erase, observe, evalC, record] using
        congrArg (record (.void name))
          (ih (host.void name world) replies counters status normal)
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, IStmt.erase, enabled, passed, observe] using
            ih world replies counters status (by simpa [eval, enabled, passed, observe] using normal)
        · simp [eval, enabled, passed, observe, halt] at normal
      · simpa [eval, IStmt.erase, enabled] using
          ih world replies counters status (by simpa [eval, enabled] using normal)
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [eval, IStmt.erase, enabled, observe] using
          ih world replies (countDecline counters key) status
            (by simpa [eval, enabled, observe] using normal)
      · simpa [eval, IStmt.erase, enabled] using
          ih world replies counters status (by simpa [eval, enabled] using normal)

theorem eval_project_of_normal {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) (status : Status)
    (normal : (eval mode host validator target world replies counters).status = .core status) :
    (eval mode host validator target world replies counters).project =
      some (evalC host target.erase world replies) := by
  rw [eval_normal_refines mode host validator target world replies counters status normal]
  simp [Result.project, normal]

theorem PlanValid.normal_eval_exact {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) (status : Status)
    (normal : (eval mode host validator plan.target world replies counters).status = .core status) :
    (eval mode host validator plan.target world replies counters).project =
      some (evalSource plan.protocol host plan.protocol.body world replies) := by
  rw [eval_project_of_normal mode host validator plan.target world replies counters status normal]
  rw [lower_eval_exact plan.protocol host plan.protocol.body plan.target.erase
    (instrument_erases plan.protocol plan.checks plan.target valid.target)]

theorem eval_failed_validation {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (check : Check) (next : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) (enabled : mode.checked = true)
    (failed : validator check.cName world ≠ check.expected) :
    eval mode host validator (.validate check next) world replies counters =
      ⟨.failedCheck check (validator check.cName world), world, replies,
        [.validation check (validator check.cName world)], counters⟩ := by
  simp [eval, enabled, failed, observe, halt]

theorem eval_failed_validation_no_call {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (check : Check) (next : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) (enabled : mode.checked = true)
    (failed : validator check.cName world ≠ check.expected) :
    coreCalls (eval mode host validator (.validate check next) world replies counters).observations =
      [] := by
  rw [eval_failed_validation mode host validator check next world replies counters enabled failed]
  rfl

def liftCore {World : Type} (execution : Execution World) (counters : CounterStore) :
    Result World :=
  ⟨.core execution.status, execution.world, execution.remaining,
    execution.calls.map Observation.call, counters⟩

/-- Disabled operations are absent even from the observed trace. In
particular, their predicates are not called and private counters are intact. -/
theorem eval_disabled_exact {World : Type} (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    eval ⟨false, false⟩ host validator target world replies counters =
      liftCore (evalC host target.erase world replies) counters := by
  induction target generalizing world replies with
  | ret outcome => rfl
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => rfl
      | cons reply rest =>
          cases reply with
          | false => simp [eval, IStmt.erase, evalC, ihNo, liftCore, observe, record]
          | true => simp [eval, IStmt.erase, evalC, ihYes, liftCore, observe, record]
  | voidCall name next ih =>
      simp [eval, IStmt.erase, evalC, ih, liftCore, observe, record]
  | validate check next ih => simpa [eval, IStmt.erase] using ih world replies
  | tick key next ih => simpa [eval, IStmt.erase] using ih world replies

theorem PlanValid.disabled_eval_exact {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (host : Host World) (validator : String → World → Bool)
    (world : World) (replies : List Bool) (counters : CounterStore) :
    eval ⟨false, false⟩ host validator plan.target world replies counters =
      liftCore (evalSource plan.protocol host plan.protocol.body world replies) counters := by
  rw [eval_disabled_exact, lower_eval_exact plan.protocol host plan.protocol.body plan.target.erase
    (instrument_erases plan.protocol plan.checks plan.target valid.target)]

def replayCounters : CounterStore → List DeclineKey → CounterStore
  | counters, [] => counters
  | counters, key :: rest => replayCounters (countDecline counters key) rest

/-- Every change to private counters is the saturating replay of precisely
the counter operations present in the ordered observation. -/
theorem eval_counter_replay {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    (eval mode host validator target world replies counters).counters =
      replayCounters counters
        (declineKeys (eval mode host validator target world replies counters).observations) := by
  induction target generalizing world replies counters with
  | ret outcome => rfl
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => rfl
      | cons reply rest =>
          cases reply with
          | false =>
              simpa [eval, observe] using
                (ihNo (host.boolean name world false) rest counters)
          | true =>
              simpa [eval, observe] using
                (ihYes (host.boolean name world true) rest counters)
  | voidCall name next ih =>
      simpa [eval, observe] using ih (host.void name world) replies counters
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, enabled, passed, observe] using ih world replies counters
        · simp [eval, enabled, passed, observe, halt, declineKeys, replayCounters]
      · simpa [eval, enabled] using ih world replies counters
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [eval, enabled, observe, replayCounters] using
          ih world replies (countDecline counters key)
      · simpa [eval, enabled] using ih world replies counters

/-- Generated counter instructions occur exactly once on a returned decline,
and never on another outcome, a missing reply, or a failed validation. -/
theorem Disciplined.eval_declines {last : DeclineKey} {target : IStmt}
    (disciplined : Disciplined last target) {World : Type} (mode : Mode)
    (host : Host World) (validator : String → World → Bool) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    declineKeys (eval mode host validator target world replies counters).observations =
      if mode.counted = true ∧
          (eval mode host validator target world replies counters).status =
            .core (.returned .declined) then
        [lastDecision last
          (coreCalls (eval mode host validator target world replies counters).observations)]
      else [] := by
  induction disciplined generalizing world replies counters with
  | ret last outcome other =>
      simp [eval, halt, declineKeys, other]
  | decline last =>
      cases enabled : mode.counted <;>
        simp [eval, enabled, observe, halt, declineKeys, coreCalls, lastDecision]
  | ifCall last name yes no onTrue onFalse ihYes ihNo =>
      cases replies with
      | nil => simp [eval, halt, declineKeys]
      | cons reply rest =>
          cases reply with
          | false =>
              simpa [eval, observe, lastDecision] using
                (ihNo (host.boolean name world false) rest counters)
          | true =>
              simpa [eval, observe, lastDecision] using
                (ihYes (host.boolean name world true) rest counters)
  | voidCall last name next after ih =>
      simpa [eval, observe, lastDecision] using ih (host.void name world) replies counters
  | validate last check next after ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, enabled, passed, observe] using ih world replies counters
        · simp [eval, enabled, passed, observe, halt, declineKeys]
      · simpa [eval, enabled] using ih world replies counters

theorem PlanValid.decline_reason {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) (counted : mode.counted = true)
    (returned : (eval mode host validator plan.target world replies counters).status =
      .core (.returned .declined)) :
    declineKeys (eval mode host validator plan.target world replies counters).observations =
      [lastDecision .entry
        (coreCalls (eval mode host validator plan.target world replies counters).observations)] := by
  simpa [counted, returned] using
    (instrument_disciplined plan.protocol plan.checks plan.target valid.target).eval_declines
      mode host validator world replies counters

theorem PlanValid.decline_counter {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) (counted : mode.counted = true)
    (returned : (eval mode host validator plan.target world replies counters).status =
      .core (.returned .declined)) :
    (eval mode host validator plan.target world replies counters).counters =
      countDecline counters (lastDecision .entry
        (coreCalls (eval mode host validator plan.target world replies counters).observations)) := by
  rw [eval_counter_replay, valid.decline_reason mode host validator world replies counters
    counted returned]
  rfl

theorem PlanValid.decline_counter_value {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) (counted : mode.counted = true)
    (returned : (eval mode host validator plan.target world replies counters).status =
      .core (.returned .declined)) :
    let key := lastDecision .entry
      (coreCalls (eval mode host validator plan.target world replies counters).observations)
    ((eval mode host validator plan.target world replies counters).counters key).val =
      min ((counters key).val + 1) (counterBound - 1) := by
  dsimp only
  rw [valid.decline_counter mode host validator world replies counters counted returned,
    countDecline_same, saturatingSucc_value]

theorem PlanValid.other_counters_unchanged {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore)
    (other : (eval mode host validator plan.target world replies counters).status ≠
      .core (.returned .declined)) :
    (eval mode host validator plan.target world replies counters).counters = counters := by
  rw [eval_counter_replay]
  have keys := (instrument_disciplined plan.protocol plan.checks plan.target valid.target).eval_declines
    mode host validator world replies counters
  rw [if_neg (fun h => other h.2)] at keys
  rw [keys]
  rfl

/-- An independent pure path predicate follows ordinary host transitions,
without executing counters or constructing instrumented result records. -/
def checksPass {World : Type} (checked : Bool) (host : Host World)
    (validator : String → World → Bool) : IStmt → World → List Bool → Bool
  | .ret _, _, _ => true
  | .ifCall name yes no, world, replies => match replies with
      | [] => true
      | false :: rest => checksPass checked host validator no
          (host.boolean name world false) rest
      | true :: rest => checksPass checked host validator yes
          (host.boolean name world true) rest
  | .voidCall name next, world, replies =>
      checksPass checked host validator next (host.void name world) replies
  | .validate check next, world, replies =>
      (!checked || validator check.cName world == check.expected) &&
        checksPass checked host validator next world replies
  | .tick _ next, world, replies => checksPass checked host validator next world replies

theorem checksPass_iff_normal {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    checksPass mode.checked host validator target world replies = true ↔
      ∃ status, (eval mode host validator target world replies counters).status = .core status := by
  induction target generalizing world replies counters with
  | ret outcome => simp [checksPass, eval, halt]
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => simp [checksPass, eval, halt]
      | cons reply rest =>
          cases reply with
          | false => simpa [checksPass, eval, observe] using
              (ihNo (host.boolean name world false) rest counters)
          | true => simpa [checksPass, eval, observe] using
              (ihYes (host.boolean name world true) rest counters)
  | voidCall name next ih =>
      simpa [checksPass, eval, observe] using ih (host.void name world) replies counters
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [checksPass, eval, enabled, passed, observe] using ih world replies counters
        · simp [checksPass, eval, enabled, passed, observe, halt]
      · simpa [checksPass, eval, enabled] using ih world replies counters
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [checksPass, eval, enabled, observe] using
          ih world replies (countDecline counters key)
      · simpa [checksPass, eval, enabled] using ih world replies counters

theorem PlanValid.passing_eval_exact {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore)
    (passing : checksPass mode.checked host validator plan.target world replies = true) :
    (eval mode host validator plan.target world replies counters).project =
      some (evalSource plan.protocol host plan.protocol.body world replies) := by
  obtain ⟨status, normal⟩ :=
    (checksPass_iff_normal mode host validator plan.target world replies counters).mp passing
  exact valid.normal_eval_exact mode host validator world replies counters status normal

theorem eval_calls_prefix {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    coreCalls (eval mode host validator target world replies counters).observations <+:
      (evalC host target.erase world replies).calls := by
  induction target generalizing world replies counters with
  | ret outcome => exact ⟨[], rfl⟩
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => exact ⟨[], rfl⟩
      | cons reply rest =>
          cases reply with
          | false => simpa [eval, observe, IStmt.erase, evalC, record] using
              ((List.cons_prefix_cons (a := .boolean name false) (b := .boolean name false)).mpr ⟨rfl,
                ihNo (host.boolean name world false) rest counters⟩)
          | true => simpa [eval, observe, IStmt.erase, evalC, record] using
              ((List.cons_prefix_cons (a := .boolean name true) (b := .boolean name true)).mpr ⟨rfl,
                ihYes (host.boolean name world true) rest counters⟩)
  | voidCall name next ih =>
      simpa [eval, observe, IStmt.erase, evalC, record] using
        ((List.cons_prefix_cons (a := .void name) (b := .void name)).mpr
          ⟨rfl, ih (host.void name world) replies counters⟩)
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, enabled, passed, observe, IStmt.erase] using ih world replies counters
        · simp [eval, enabled, passed, observe, halt, coreCalls, IStmt.erase]
      · simpa [eval, enabled, IStmt.erase] using ih world replies counters
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [eval, enabled, observe, IStmt.erase] using
          ih world replies (countDecline counters key)
      · simpa [eval, enabled, IStmt.erase] using ih world replies counters

/-- Ordinary replies are neither consumed by checks nor lost on fail-stop. -/
theorem eval_reply_partition {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    consumed (coreCalls (eval mode host validator target world replies counters).observations) ++
      (eval mode host validator target world replies counters).remaining = replies := by
  induction target generalizing world replies counters with
  | ret outcome => rfl
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => rfl
      | cons reply rest =>
          cases reply with
          | false => simpa [eval, observe] using
              congrArg (List.cons false) (ihNo (host.boolean name world false) rest counters)
          | true => simpa [eval, observe] using
              congrArg (List.cons true) (ihYes (host.boolean name world true) rest counters)
  | voidCall name next ih =>
      simpa [eval, observe] using ih (host.void name world) replies counters
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, enabled, passed, observe] using ih world replies counters
        · simp [eval, enabled, passed, observe, halt, coreCalls, consumed]
      · simpa [eval, enabled] using ih world replies counters
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [eval, enabled, observe] using ih world replies (countDecline counters key)
      · simpa [eval, enabled] using ih world replies counters

def replayWorld {World : Type} (host : Host World) : World → List Event → World
  | world, [] => world
  | world, .boolean name reply :: rest => replayWorld host (host.boolean name world reply) rest
  | world, .void name :: rest => replayWorld host (host.void name world) rest

/-- The world at a failed check is exactly the world produced by the
retained prefix of ordinary calls. Validation itself never mutates it. -/
theorem eval_world_replay {World : Type} (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (target : IStmt) (world : World)
    (replies : List Bool) (counters : CounterStore) :
    (eval mode host validator target world replies counters).world =
      replayWorld host world
        (coreCalls (eval mode host validator target world replies counters).observations) := by
  induction target generalizing world replies counters with
  | ret outcome => rfl
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => rfl
      | cons reply rest =>
          cases reply with
          | false => simpa [eval, observe, replayWorld] using
              (ihNo (host.boolean name world false) rest counters)
          | true => simpa [eval, observe, replayWorld] using
              (ihYes (host.boolean name world true) rest counters)
  | voidCall name next ih =>
      simpa [eval, observe, replayWorld] using ih (host.void name world) replies counters
  | validate check next ih =>
      by_cases enabled : mode.checked = true
      · by_cases passed : validator check.cName world = check.expected
        · simpa [eval, enabled, passed, observe] using ih world replies counters
        · simp [eval, enabled, passed, observe, halt, coreCalls, replayWorld]
      · simpa [eval, enabled] using ih world replies counters
  | tick key next ih =>
      by_cases enabled : mode.counted = true
      · simpa [eval, enabled, observe] using ih world replies (countDecline counters key)
      · simpa [eval, enabled] using ih world replies counters

theorem trace_prefix {p : Protocol} {first last : Context} {calls segment : List Event}
    (trace : Trace p first calls last) (isPrefix : segment <+: calls) :
    ∃ middle, Trace p first segment middle := by
  induction trace generalizing segment with
  | nil =>
      obtain ⟨suffix, eq⟩ := isPrefix
      have empty : segment = [] := (List.append_eq_nil_iff.mp eq).1
      subst segment
      exact ⟨_, .nil _⟩
  | @cons first middle last event rest enabled after ih =>
      cases segment with
      | nil => exact ⟨first, .nil first⟩
      | cons head tail =>
          obtain ⟨suffix, eq⟩ := isPrefix
          simp only [List.cons_append, List.cons.injEq] at eq
          obtain ⟨rfl, eq⟩ := eq
          obtain ⟨endContext, traceTail⟩ := ih ⟨suffix, eq⟩
          exact ⟨endContext, .cons enabled traceTail⟩

/-- Even a fail-stop execution retains only operations enabled by the
source's fact and exclusive-resource judgment. An abort is not a resource-
discharging ordinary return. -/
theorem PlanValid.calls_enabled {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) :
    ∃ last, Trace plan.protocol (initial plan.protocol)
      (coreCalls (eval mode host validator plan.target world replies counters).observations) last := by
  obtain ⟨last, trace, _⟩ := valid.source.body.source_safe host world replies
  have isPrefix := eval_calls_prefix mode host validator plan.target world replies counters
  rw [lower_eval_exact plan.protocol host plan.protocol.body plan.target.erase
    (instrument_erases plan.protocol plan.checks plan.target valid.target)] at isPrefix
  exact trace_prefix trace isPrefix

theorem PlanValid.normal_safe {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore) (status : Status)
    (normal : (eval mode host validator plan.target world replies counters).status = .core status) :
    ∃ last, Trace plan.protocol (initial plan.protocol)
      (coreCalls (eval mode host validator plan.target world replies counters).observations) last ∧
        SafeStop plan.protocol last status := by
  obtain ⟨last, trace, safe⟩ := lower_target_safe valid.source.body plan.target.erase
    (instrument_erases plan.protocol plan.checks plan.target valid.target) host world replies
  rw [eval_normal_refines mode host validator plan.target world replies counters status normal]
    at trace safe
  exact ⟨last, trace, safe⟩

theorem PlanValid.decline_no_publication {World : Type} {plan : RecordedPlan}
    (valid : PlanValid plan) (mode : Mode) (host : Host World)
    (validator : String → World → Bool) (world : World) (replies : List Bool)
    (counters : CounterStore)
    (declined : (eval mode host validator plan.target world replies counters).status =
      .core (.returned .declined)) :
    ∀ event ∈ coreCalls (eval mode host validator plan.target world replies counters).observations,
      ¬ IrreversibleEvent plan.protocol event := by
  obtain ⟨last, trace, safe⟩ := valid.normal_safe mode host validator world replies counters
    (.returned .declined) declined
  cases safe with
  | returned _ _ clean _ =>
      exact trace.no_irreversible_of_false valid.source.metadata (clean rfl)

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Instrumentation
