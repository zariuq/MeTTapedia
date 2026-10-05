import Mettapedia.Languages.MeTTa.HE.LetChainResumption
import Mettapedia.Languages.MeTTa.HE.TypedApplyMachine
import Mettapedia.GSLT.Dynamics.OrderedDemand

/-!
# HE results under the ordered, effect-aware observer

An HE result list is read as an ordered trace: a successful return is an
answer occurrence, an error return is a fault event, and bindings travel with
each occurrence.  The HE producer layer commits no separate effect events.

* **Producer completion is success priority** (`heTrace_reference`).  The
  completion policy of `ProducerCompletion` is the generic success-priority
  completion of `OrderedDemand`: `[fault, 1, 1]` completes to `[1, 1]`.
* **Completion before consumption** (`completion_observation_faithful`).
  Every finite run of the completion machine followed by its consumer observes
  a prefix of the completed composition, and the final run observes all of it.
  For a consumer that returns nothing on successes, no finite run ever
  publishes the suppressed producer fault (`suppressed_fault_never_reappears`).
* **The live-frontier observer is a different observer**
  (`live_frontier_publishes_fault`, `completion_ne_live_frontier`).  Feeding
  each raw return to the consumer as it arrives publishes the fault at the
  first step.  An adapter with a live frontier, such as PeTTa's, states that
  observer; it is not identified with HE's.
* **When fusion is licensed** (`fusion_licence_iff_uniform`).  Consuming the
  raw producer in place of its completion is exact for every consumer that
  returns errors unchanged exactly when the producer's returns are all
  successes or all errors.
* **The typed application machine is prefix-faithful**
  (`typedApply_prefixFaithful`).  At every administrative budget its published
  results are an ordered prefix of the independently defined direct
  evaluator's, with duplicate occurrences and bindings, and an exhausted
  machine has published all of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.OrderedEffectObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Dynamics.OrderedDemand

/-- The ordered events of HE results: errors are faults, other returns are
answers, and no separate effect is committed at this layer. -/
abbrev HEEvent := Event ResultPair Empty ResultPair

/-- Read one HE result as an event. -/
def heEvent (result : ResultPair) : HEEvent :=
  if isErrorAtom result.1 then .fault result else .answer result

/-- Read an HE result list as an ordered trace. -/
def heTrace (results : ResultList) : Trace ResultPair Empty ResultPair :=
  results.map heEvent

theorem heEvent_injective : Function.Injective heEvent := by
  intro first second same
  unfold heEvent at same
  split at same <;> split at same <;> simp_all

theorem heTrace_injective : Function.Injective heTrace :=
  List.map_injective_iff.mpr heEvent_injective

theorem answers_heTrace (results : ResultList) :
    answers (heTrace results) = results.filter fun result => !isErrorAtom result.1 := by
  induction results with
  | nil => rfl
  | cons result rest ih =>
      rw [heTrace, List.map_cons, answers_cons, ← heTrace, ih]
      by_cases error : isErrorAtom result.1 = true <;>
        simp [heEvent, error, Event.answer?]

theorem filter_heTrace (results : ResultList) :
    (heTrace results).filter (fun event => !event.isFault) =
      heTrace (results.filter fun result => !isErrorAtom result.1) := by
  rw [heTrace, List.filter_map, heTrace]
  congr 1
  apply List.filter_congr
  intro result _
  by_cases error : isErrorAtom result.1 = true <;> simp [heEvent, error, Event.isFault]

/-- **HE's producer completion is success priority.** -/
theorem heTrace_reference (returns : ResultList) :
    heTrace (ProducerCompletion.reference returns) = successPriority (heTrace returns) := by
  by_cases noSuccess : (returns.filter fun result => !isErrorAtom result.1) = []
  · have allErrors : (returns.filter fun result => isErrorAtom result.1) = returns := by
      rw [List.filter_eq_self]
      intro result member
      by_contra notError
      have present : result ∈ returns.filter fun result => !isErrorAtom result.1 := by
        simpa [List.mem_filter, member] using notError
      rw [noSuccess] at present
      cases present
    simp [ProducerCompletion.reference, noSuccess, allErrors, successPriority,
      answers_heTrace]
  · have isEmpty : (returns.filter fun result => !isErrorAtom result.1).isEmpty = false := by
      simpa [List.isEmpty_iff] using noSuccess
    simp only [ProducerCompletion.reference, isEmpty, Bool.false_eq_true, if_false,
      successPriority, answers_heTrace, if_neg noSuccess]
    exact (filter_heTrace returns).symm

/-- A consumer of HE results that returns an error unchanged. -/
def PassesErrors (body : ResultPair → ResultList) : Prop :=
  ∀ result, isErrorAtom result.1 = true → body result = [result]

/-- Consuming results is trace composition when errors pass through. -/
theorem heTrace_flatMap (body : ResultPair → ResultList) (passes : PassesErrors body)
    (results : ResultList) :
    heTrace (results.flatMap body) = bindTrace (heTrace results) fun result => heTrace (body result) := by
  induction results with
  | nil => rfl
  | cons result rest ih =>
      simp only [List.flatMap_cons, heTrace, List.map_append, List.map_cons,
        bindTrace_cons] at ih ⊢
      rw [ih]
      by_cases error : isErrorAtom result.1 = true
      · simp [heEvent, error, Event.bind, passes result error]
      · simp [heEvent, error, Event.bind]

/-- **Completion before consumption, as trace composition.** -/
theorem heTrace_consume (body : ResultPair → ResultList) (passes : PassesErrors body)
    (returns : ResultList) :
    heTrace (ProducerCompletion.consume body returns) =
      bindTrace (successPriority (heTrace returns)) fun result => heTrace (body result) := by
  rw [ProducerCompletion.consume, heTrace_flatMap body passes, heTrace_reference]

/-! ## Finite observations of completion followed by consumption -/

/-- The observation after `fuel` administrative transitions: nothing is
published before completion, and the consumed completion afterwards. -/
def completionObservation (body : ResultPair → ResultList) (fuel : ℕ)
    (frame : ProducerCompletion.Frame) : Observation HEEvent Unit :=
  match ProducerCompletion.run fuel frame with
  | (some returns, _) => ⟨heTrace (returns.flatMap body), .finished ()⟩
  | (none, _) => ⟨[], .suspended⟩

/-- The reference: the consumed completion of every return still owed. -/
def completionReference (body : ResultPair → ResultList) (frame : ProducerCompletion.Frame) :
    Observation HEEvent Unit :=
  ⟨heTrace (ProducerCompletion.consume body (frame.savedRev.reverse ++ frame.remaining)),
    .finished ()⟩

/-- **Every finite run observes a prefix of the consumed completion.** -/
theorem completion_observation_faithful (body : ResultPair → ResultList)
    (frame : ProducerCompletion.Frame) :
    PrefixFaithful (fun fuel => completionObservation body fuel frame)
      (completionReference body frame) := by
  intro fuel
  have preserved := ProducerCompletion.run_preserves_completion fuel frame
  show (completionObservation body fuel frame).Prefix _
  rcases outcome : ProducerCompletion.run fuel frame with ⟨_ | returns, _ | next⟩
  · simp [outcome] at preserved
  · simp only [completionObservation, outcome]
    exact ⟨List.nil_prefix, fun final => final.elim⟩
  · simp only [outcome] at preserved
    simp only [completionObservation, outcome, preserved]
    exact Observation.Prefix.refl _
  · simp [outcome] at preserved

/-- The producer `[fault, ok, ok]`. -/
def faultReturn : ResultPair :=
  (.expression [.symbol "Error", .symbol "source", .symbol "fault"], Bindings.empty)

def okReturn : ResultPair := (.symbol "ok", Bindings.empty)

def faultThenTwo : ProducerCompletion.Frame := ⟨[], [faultReturn, okReturn, okReturn]⟩

/-- A consumer that returns errors unchanged and nothing for a success. -/
def answerless (result : ResultPair) : ResultList :=
  if isErrorAtom result.1 then [result] else []

theorem answerless_passes : PassesErrors answerless := by
  intro result error
  simp [answerless, error]

/-- `[fault, ok, ok]` completes to `[ok, ok]`. -/
theorem faultThenTwo_completes :
    ProducerCompletion.reference [faultReturn, okReturn, okReturn] = [okReturn, okReturn] := by
  decide

/-- **The suppressed producer fault never reappears**: at every budget, the
completion followed by an answerless consumer has published nothing. -/
theorem suppressed_fault_never_reappears (fuel : ℕ) :
    (completionObservation answerless fuel faultThenTwo).events = [] := by
  have faithful : (completionObservation answerless fuel faultThenTwo).Prefix
      (completionReference answerless faultThenTwo) :=
    completion_observation_faithful answerless faultThenTwo fuel
  have reference : (completionReference answerless faultThenTwo).events = [] := by
    decide
  have published := faithful.1
  rw [reference] at published
  exact List.prefix_nil.mp published

/-! ## The live-frontier observer -/

/-- A live frontier feeds each raw return to the consumer as soon as it
arrives. -/
def liveFrontierObservation (body : ResultPair → ResultList) (fuel : ℕ)
    (returns : ResultList) : Observation HEEvent Unit :=
  ⟨heTrace ((returns.take fuel).flatMap body),
    if returns.length ≤ fuel then .finished () else .suspended⟩

/-- **Early fault publication**: the live frontier publishes the producer fault
after one return. -/
theorem live_frontier_publishes_fault :
    (liveFrontierObservation answerless 1 [faultReturn, okReturn, okReturn]).events =
      [.fault faultReturn] := by
  decide

/-- The two observers disagree on the same producer and consumer: HE's
completion observer is not the live-frontier observer. -/
theorem completion_ne_live_frontier :
    (completionReference answerless faultThenTwo).events ≠
      (liveFrontierObservation answerless 3 [faultReturn, okReturn, okReturn]).events := by
  decide

/-- **Fusion licence.**  Consuming the raw producer, in place of its
completion, is exact for every consumer that passes errors through exactly
when the producer's returns are all successes or all errors. -/
theorem fusion_licence_iff_uniform (returns : ResultList) :
    (∀ body, PassesErrors body → ProducerCompletion.consume body returns = returns.flatMap body) ↔
      (∀ result ∈ returns, isErrorAtom result.1 = false) ∨
        (∀ result ∈ returns, isErrorAtom result.1 = true) := by
  have identity : PassesErrors fun result => [result] := fun _ _ => rfl
  constructor
  · intro fused
    have same := fused (fun result => [result]) identity
    simp only [ProducerCompletion.consume, List.flatMap_singleton'] at same
    have traces := congrArg heTrace same
    rw [heTrace_reference, successPriority_eq_self_iff, answers_heTrace] at traces
    rcases traces with noSuccess | noFault
    · right
      intro result member
      by_contra notError
      have present : result ∈ returns.filter fun result => !isErrorAtom result.1 := by
        simpa [List.mem_filter, member] using notError
      rw [noSuccess] at present
      cases present
    · left
      intro result member
      have notFault := noFault (heEvent result) (List.mem_map_of_mem member)
      by_contra error
      simp only [Bool.not_eq_false] at error
      simp [heEvent, error, Event.isFault] at notFault
  · intro uniform body passes
    have fixed : ProducerCompletion.reference returns = returns := by
      apply heTrace_injective
      rw [heTrace_reference, successPriority_eq_self_iff, answers_heTrace]
      rcases uniform with noError | allError
      · right
        intro event member
        obtain ⟨result, present, rfl⟩ := List.mem_map.mp member
        simp [heEvent, noError result present, Event.isFault]
      · left
        apply List.filter_eq_nil_iff.mpr
        intro result member
        simp [allError result member]
    rw [ProducerCompletion.consume, fixed]

/-! ## The typed application machine is prefix-faithful -/

variable (eval1 : Atom → Atom → Bindings → ResultList)
  (applyEnv : Bindings → Atom → Atom)
  (mergeEnv : Bindings → Bindings → Option Bindings)
  (extendBinder : Bindings → Atom → Atom → Option Bindings)
  (isTrivial : Atom → Bool)

/-- The machine's observation at an administrative budget: its published
results, finished exactly when no frame remains, and suspended otherwise. -/
def typedApplyObservation (st : TypedApplyState) (budget : ℕ) : Observation HEEvent Unit :=
  let paused := machineRun eval1 applyEnv mergeEnv extendBinder isTrivial (.initial st) budget
  ⟨heTrace paused.emitted, if paused.worklist = [] then .finished () else .suspended⟩

/-- **Ordered prefix faithfulness of typed application**: at every budget the
machine publishes an ordered prefix of the direct evaluator's results, with
duplicates and bindings, and a finished machine has published all of them. -/
theorem typedApply_prefixFaithful (st : TypedApplyState) :
    PrefixFaithful (typedApplyObservation eval1 applyEnv mergeEnv extendBinder isTrivial st)
      ⟨heTrace (typedApplyDirect eval1 applyEnv mergeEnv extendBinder isTrivial st),
        .finished ()⟩ := by
  intro budget
  obtain ⟨residual, split⟩ :=
    typedApplyMachine_cancel_prefix eval1 applyEnv mergeEnv extendBinder isTrivial st budget
  refine ⟨?_, fun final => ?_⟩
  · rw [split, heTrace, List.map_append]
    exact List.prefix_append _ _
  · by_cases done : (machineRun eval1 applyEnv mergeEnv extendBinder isTrivial
        (.initial st) budget).worklist = []
    · have complete := typedApplyMachine_complete_eq_direct
        eval1 applyEnv mergeEnv extendBinder isTrivial st budget done
      simp [typedApplyObservation, done, complete]
    · simp [typedApplyObservation, done, Status.Final] at final

end Mettapedia.Languages.MeTTa.HE.OrderedEffectObservation
