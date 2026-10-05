import Mettapedia.GSLT.Dynamics.DemandAgreement
import Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra
import Mathlib.Tactic.Linarith

/-!
# Ordered, effect-aware observations of demand

A runtime that accepts a transformation of demand must preserve the ordered
answer occurrences of a run, its committed effects and its faults, not only
the bag or the set of its answers.  This module states that observer and
derives exactly when the demand transformations preserve it.

* **Events and traces** (`Event`, `Trace`).  A run publishes, in order,
  answer occurrences, committed effects and faults.  Sequential composition
  (`bindTrace`) consumes each answer in place and keeps every effect and fault
  where it occurred; it is the lifting of a per-event segment
  (`OrderedOccurrenceBodyAlgebra.run`), so it preserves ordered choice.
* **Completion status** (`Status`, `Observation`).  A finite observation is
  its published events with an explicit status: finished with a verdict,
  faulted, suspended, or incomplete.  `Observation.Prefix` orders finite
  observations; a final status is never revised.
* **The ordered demand laws.**  A computation bound once and used `n` times,
  eagerly, lazily with sharing, or by resampling (`eagerTrace`, `lazyTrace`,
  `resampledTrace`).  Eager and lazy evaluation agree exactly when the binding
  is used or the computation is a single answer with no effect and no fault
  (`eagerTrace_eq_lazyTrace_iff`).  Sharing and resampling agree exactly when
  there is at most one use, or the computation has no answer, or it is a single
  answer (`lazyTrace_eq_resampledTrace_iff`).
* **The bag laws are the image of these** (`answerBag_eagerTrace`,
  `answerBag_lazyTrace`, `answerBag_resampledTrace`): forgetting order, effects
  and faults sends each ordered strategy to its bag strategy in
  `DemandAgreement`.  The converse fails.  The bag-cardinality laws license
  discarding a computation whose only answer follows an effect, and copying it
  by resampling, while the ordered observer sees the effect dropped or
  committed twice (`unused_effect_control`, `repeated_effect_control`).
  Reordered answers and lost equal occurrences are further controls
  (`reordering_control`, `lost_occurrence_control`).
* **Completion and fusion** (`fusion_licence_iff`).  Fusing a consumer into a
  producer's live stream preserves the observation for every consumer exactly
  when the producer's completion policy leaves its trace unchanged.  Under
  success priority (`successPriority`) that is exactly a trace without
  answers, or without faults (`successPriority_eq_self_iff`).  A producer
  `[fault, 1, 1]` completes to `[1, 1]`; streamed into a consumer that returns
  nothing, it publishes the fault early, while its answer bags agree
  (`early_fault_control`).  The streaming observer and the completion observer
  are different observers, and neither is identified with the other.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.OrderedDemand

open Mettapedia.GSLT.Dynamics.DemandAgreement (shareTuple eagerShared lazyShared)

/-- An event of an ordered run: an answer occurrence, a committed effect, or a
fault. -/
inductive Event (Answer Effect Fault : Type) where
  | answer (value : Answer)
  | effect (effect : Effect)
  | fault (fault : Fault)
  deriving DecidableEq, Repr

namespace Event

variable {A B E F : Type}

/-- The answer carried by an event, if it is one. -/
def answer? : Event A E F → Option A
  | .answer value => some value
  | .effect _ => none
  | .fault _ => none

def isFault : Event A E F → Bool
  | .answer _ => false
  | .effect _ => false
  | .fault _ => true

/-- Continue an event: an answer is consumed by `next`; an effect or a fault
stays where it occurred. -/
def bind (next : A → List (Event B E F)) : Event A E F → List (Event B E F)
  | .answer value => next value
  | .effect committed => [.effect committed]
  | .fault failure => [.fault failure]

def mapAnswer (f : A → B) : Event A E F → Event B E F
  | .answer value => .answer (f value)
  | .effect committed => .effect committed
  | .fault failure => .fault failure

@[simp] theorem answer?_mapAnswer (f : A → B) (event : Event A E F) :
    (event.mapAnswer f).answer? = event.answer?.map f := by
  cases event <;> rfl

end Event

/-- An ordered run. -/
abbrev Trace (A E F : Type) := List (Event A E F)

variable {A B C E F : Type}

/-- **Sequential composition**: every answer occurrence is consumed in place. -/
def bindTrace (trace : Trace A E F) (next : A → Trace B E F) : Trace B E F :=
  OrderedOccurrenceBodyAlgebra.run (Event.bind next) trace

/-- The answers of a run, in order, with every occurrence. -/
def answers (trace : Trace A E F) : List A :=
  trace.filterMap Event.answer?

/-- The bag of answers: order, effects and faults forgotten. -/
def answerBag (trace : Trace A E F) : Multiset A :=
  (answers trace : Multiset A)

@[simp] theorem bindTrace_nil (next : A → Trace B E F) : bindTrace [] next = [] :=
  rfl

@[simp] theorem bindTrace_cons (event : Event A E F) (trace : Trace A E F)
    (next : A → Trace B E F) :
    bindTrace (event :: trace) next = event.bind next ++ bindTrace trace next :=
  rfl

theorem bindTrace_append (first second : Trace A E F) (next : A → Trace B E F) :
    bindTrace (first ++ second) next = bindTrace first next ++ bindTrace second next := by
  simp [bindTrace, OrderedOccurrenceBodyAlgebra.run, List.flatMap_append]

/-- Composition is the lifting of a per-event segment, so it preserves ordered
choice. -/
theorem bindTrace_preservesOrderedChoice (next : A → Trace B E F) :
    OrderedOccurrenceBodyAlgebra.PreservesOrderedChoice (fun trace : Trace A E F =>
      bindTrace trace next) :=
  OrderedOccurrenceBodyAlgebra.preservesOrderedChoice_of_candidateLocalizable
    ⟨Event.bind next, fun _ => rfl⟩

@[simp] theorem bindTrace_pure (trace : Trace A E F) :
    bindTrace trace (fun value => [.answer value]) = trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [Event.bind, ih]

theorem bindTrace_map (trace : Trace A E F) (f : A → B) :
    bindTrace trace (fun value => [.answer (f value)]) = trace.map (Event.mapAnswer f) := by
  induction trace with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [Event.bind, Event.mapAnswer, ih]

theorem answers_cons (event : Event A E F) (trace : Trace A E F) :
    answers (event :: trace) = (event.answer?.toList) ++ answers trace := by
  cases event <;> rfl

@[simp] theorem answers_nil : answers ([] : Trace A E F) = [] :=
  rfl

theorem answers_append (first second : Trace A E F) :
    answers (first ++ second) = answers first ++ answers second :=
  List.filterMap_append

theorem answers_map (trace : Trace A E F) (f : A → B) :
    answers (trace.map (Event.mapAnswer f)) = (answers trace).map f := by
  simp [answers, List.filterMap_map, List.map_filterMap]

theorem answers_bindTrace (trace : Trace A E F) (next : A → Trace B E F) :
    answers (bindTrace trace next) = (answers trace).flatMap fun value => answers (next value) := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      rw [bindTrace_cons, answers_append, ih, answers_cons]
      cases event <;> simp [Event.bind, Event.answer?, answers_cons]

theorem answerBag_bindTrace (trace : Trace A E F) (next : A → Trace B E F) :
    answerBag (bindTrace trace next) = (answerBag trace).bind fun value => answerBag (next value) := by
  simp only [answerBag, answers_bindTrace, Multiset.coe_bind]

theorem answerBag_map (trace : Trace A E F) (f : A → B) :
    answerBag (trace.map (Event.mapAnswer f)) = (answerBag trace).map f := by
  simp only [answerBag, answers_map, Multiset.map_coe]

/-! ## Completion status and finite ordered observations -/

/-- **The status of a finite observation.**  A run finished with a verdict,
faulted, suspended with a saved continuation, or is incomplete: its allowance
ended while it could still move, or it can no longer move without having
finished. -/
inductive Status (Verdict : Type) where
  | finished (verdict : Verdict)
  | faulted
  | suspended
  | incomplete
  deriving DecidableEq, Repr

/-- A final status is never revised by a longer run. -/
def Status.Final {Verdict : Type} : Status Verdict → Prop
  | .finished _ => True
  | .faulted => True
  | _ => False

/-- **A finite ordered observation**: the events published so far, and the
status at that point. -/
structure Observation (Ev Verdict : Type) where
  events : List Ev
  status : Status Verdict
  deriving DecidableEq

/-- `first` is a finite prefix of `second`: its events come first, and a final
observation is already the whole observation. -/
def Observation.Prefix {Ev Verdict : Type} (first second : Observation Ev Verdict) : Prop :=
  first.events <+: second.events ∧ (first.status.Final → first = second)

theorem Observation.Prefix.refl {Ev Verdict : Type} (observation : Observation Ev Verdict) :
    observation.Prefix observation :=
  ⟨List.prefix_refl _, fun _ => rfl⟩

theorem Observation.Prefix.trans {Ev Verdict : Type} {first second third : Observation Ev Verdict}
    (one : first.Prefix second) (two : second.Prefix third) : first.Prefix third := by
  refine ⟨one.1.trans two.1, fun final => ?_⟩
  have same := one.2 final
  subst same
  exact two.2 final

/-- A fuel-indexed execution is **faithful to a reference observation** when
every finite run observes a prefix of it. -/
def PrefixFaithful {Ev Verdict : Type} (execution : ℕ → Observation Ev Verdict)
    (reference : Observation Ev Verdict) : Prop :=
  ∀ fuel, (execution fuel).Prefix reference

/-! ## Ordered demand: a computation bound once and used `n` times -/

/-- Eager: the computation runs once, and every answer is used `n` times. -/
def eagerTrace (n : ℕ) (bound : Trace A E F) : Trace (List A) E F :=
  bound.map (Event.mapAnswer (shareTuple n))

/-- Lazy with sharing: zero uses never run the computation. -/
def lazyTrace (n : ℕ) (bound : Trace A E F) : Trace (List A) E F :=
  if n = 0 then [.answer []] else eagerTrace n bound

/-- Resampling: every use runs the computation again, with its effects and
faults. -/
def resampledTrace : ℕ → Trace A E F → Trace (List A) E F
  | 0, _ => [.answer []]
  | n + 1, bound => bindTrace bound fun value =>
      (resampledTrace n bound).map (Event.mapAnswer (value :: ·))

theorem answerBag_eagerTrace (n : ℕ) (bound : Trace A E F) :
    answerBag (eagerTrace n bound) = eagerShared n (answerBag bound) := by
  rw [eagerTrace, answerBag_map, eagerShared, Multiset.bind_singleton]

theorem answerBag_lazyTrace (n : ℕ) (bound : Trace A E F) :
    answerBag (lazyTrace n bound) = lazyShared n (answerBag bound) := by
  by_cases zero : n = 0
  · simp [lazyTrace, lazyShared, zero, answerBag, answers, Event.answer?]
  · rw [lazyTrace, if_neg zero, answerBag_eagerTrace, lazyShared, if_neg zero, eagerShared]

/-- **Forgetting order, effects and faults sends resampling to the bag
resampling of `DemandAgreement`.** -/
theorem answerBag_resampledTrace (n : ℕ) (bound : Trace A E F) :
    answerBag (resampledTrace n bound) =
      DemandAgreement.resampledUses n (answerBag bound) := by
  induction n with
  | zero => simp [resampledTrace, answerBag, answers, Event.answer?,
      DemandAgreement.resampledUses_zero]
  | succ n ih =>
      rw [resampledTrace, answerBag_bindTrace, DemandAgreement.resampledUses_succ]
      congr 1
      funext value
      rw [answerBag_map, ih]

/-- A computation is **discardable** when it is one answer with no effect and no
fault. -/
def Discardable (bound : Trace A E F) : Prop :=
  ∃ value, bound = [.answer value]

/-- A computation is **copyable** when it has no answer, or is discardable. -/
def Copyable (bound : Trace A E F) : Prop :=
  answers bound = [] ∨ Discardable bound

/-- **Eager and lazy evaluation agree on the ordered observer exactly when the
binding is used, or the computation is discardable.** -/
theorem eagerTrace_eq_lazyTrace_iff (n : ℕ) (bound : Trace A E F) :
    eagerTrace n bound = lazyTrace n bound ↔ 1 ≤ n ∨ Discardable bound := by
  by_cases zero : n = 0
  · subst zero
    simp only [lazyTrace, if_true, Nat.one_ne_zero, Nat.le_zero, false_or]
    constructor
    · intro same
      have single : bound.length = 1 := by
        simpa [eagerTrace] using congrArg List.length same
      obtain ⟨event, rfl⟩ := List.length_eq_one_iff.mp single
      cases event with
      | answer value => exact ⟨value, rfl⟩
      | effect committed => simp [eagerTrace, Event.mapAnswer] at same
      | fault failure => simp [eagerTrace, Event.mapAnswer] at same
    · rintro ⟨value, rfl⟩
      simp [eagerTrace, Event.mapAnswer, shareTuple]
  · simp [lazyTrace, zero, Nat.one_le_iff_ne_zero]

private theorem bindTrace_of_no_answers {bound : Trace A E F} (none : answers bound = [])
    (next : A → Trace B E F) (f : A → B) :
    bindTrace bound next = bound.map (Event.mapAnswer f) := by
  induction bound with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | answer value => simp [answers_cons, Event.answer?] at none
      | effect committed =>
          simp only [answers_cons, Event.answer?, Option.toList_none, List.nil_append] at none
          simp [Event.bind, Event.mapAnswer, ih none]
      | fault failure =>
          simp only [answers_cons, Event.answer?, Option.toList_none, List.nil_append] at none
          simp [Event.bind, Event.mapAnswer, ih none]

private theorem map_mapAnswer_of_no_answers {bound : Trace A E F} (none : answers bound = [])
    (f g : A → B) : bound.map (Event.mapAnswer f) = bound.map (Event.mapAnswer g) := by
  rw [← bindTrace_of_no_answers none (fun value => [.answer (f value)]) f,
    bindTrace_of_no_answers none _ g]

private theorem resampledTrace_single (value : A) (n : ℕ) :
    resampledTrace n ([.answer value] : Trace A E F) = [.answer (List.replicate n value)] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [resampledTrace, Event.bind, ih, Event.mapAnswer, List.replicate_succ]

private theorem resampledTrace_one (bound : Trace A E F) :
    resampledTrace 1 bound = bound.map (Event.mapAnswer fun value => [value]) := by
  rw [← bindTrace_map]
  simp [resampledTrace, Event.mapAnswer]

/-- Length accounting: every answer is replaced by a run of fixed length. -/
private theorem length_bindTrace_const {L : ℕ} (bound : Trace A E F) (next : A → Trace B E F)
    (constant : ∀ value, (next value).length = L) :
    (bindTrace bound next).length + (answers bound).length =
      bound.length + (answers bound).length * L := by
  induction bound with
  | nil => simp [answers]
  | cons event rest ih =>
      cases event with
      | answer value =>
          simp only [bindTrace_cons, Event.bind, List.length_append, constant, answers_cons,
            Event.answer?, Option.toList_some, List.singleton_append, List.length_cons]
          nlinarith [ih]
      | effect committed =>
          simp only [bindTrace_cons, Event.bind, List.length_append, answers_cons,
            Event.answer?, Option.toList_none, List.nil_append, List.length_cons,
            List.length_nil]
          omega
      | fault failure =>
          simp only [bindTrace_cons, Event.bind, List.length_append, answers_cons,
            Event.answer?, Option.toList_none, List.nil_append, List.length_cons,
            List.length_nil]
          omega

private theorem length_resampledTrace_succ (n : ℕ) (bound : Trace A E F) :
    (resampledTrace (n + 1) bound).length + (answers bound).length =
      bound.length + (answers bound).length * (resampledTrace n bound).length :=
  length_bindTrace_const bound _ fun _ => List.length_map _

private theorem answers_length_le (bound : Trace A E F) :
    (answers bound).length ≤ bound.length := by
  simpa [answers] using List.length_filterMap_le Event.answer? bound

private theorem length_le_resampledTrace (n : ℕ) (bound : Trace A E F) (positive : 1 ≤ n) :
    bound.length ≤ (resampledTrace n bound).length := by
  induction n with
  | zero => omega
  | succ n ih =>
      have step := length_resampledTrace_succ n bound
      have fewer := answers_length_le bound
      by_cases zero : n = 0
      · subst zero
        rw [show (resampledTrace 0 bound).length = 1 from rfl, Nat.mul_one] at step
        omega
      · have previous := ih (by omega)
        by_cases none : (answers bound).length = 0
        · rw [none] at step
          omega
        · have atLeast : (answers bound).length ≤
              (answers bound).length * (resampledTrace n bound).length := by
            apply Nat.le_mul_of_pos_right
            omega
          omega

private theorem length_lt_resampledTrace (n : ℕ) (bound : Trace A E F) (two : 2 ≤ n)
    (someAnswer : answers bound ≠ []) (long : 2 ≤ bound.length) :
    bound.length < (resampledTrace n bound).length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have step := length_resampledTrace_succ m bound
  have previous := length_le_resampledTrace m bound (by omega)
  have positive : 0 < (answers bound).length := List.length_pos_iff.mpr someAnswer
  have grow : (answers bound).length * bound.length ≤
      (answers bound).length * (resampledTrace m bound).length :=
    Nat.mul_le_mul_left _ previous
  nlinarith

/-- **Sharing and resampling agree on the ordered observer exactly when there is
at most one use, or the computation is copyable.**  A committed effect or a
fault beside an answer is repeated by resampling. -/
theorem lazyTrace_eq_resampledTrace_iff (n : ℕ) (bound : Trace A E F) :
    lazyTrace n bound = resampledTrace n bound ↔ n ≤ 1 ∨ Copyable bound := by
  constructor
  · intro same
    by_contra bad
    simp only [not_or, Copyable, Discardable, not_exists] at bad
    obtain ⟨many, someAnswer, notSingle⟩ := bad
    have long : 2 ≤ bound.length := by
      match bound, someAnswer, notSingle with
      | [], someAnswer, _ => exact absurd rfl someAnswer
      | [event], someAnswer, notSingle =>
          cases event with
          | answer value => exact absurd rfl (notSingle value)
          | effect committed => simp [answers, Event.answer?] at someAnswer
          | fault failure => simp [answers, Event.answer?] at someAnswer
      | _ :: _ :: _, _, _ => simp
    have lengths := congrArg List.length same
    have strict := length_lt_resampledTrace n bound (by omega) someAnswer long
    simp only [lazyTrace, if_neg (by omega : n ≠ 0), eagerTrace, List.length_map] at lengths
    omega
  · rintro (few | copyable)
    · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · rfl
      · rw [resampledTrace_one]
        rfl
    · rcases copyable with none | ⟨value, rfl⟩
      · cases n with
        | zero => rfl
        | succ n =>
            simp only [lazyTrace, Nat.succ_ne_zero, if_false, eagerTrace, resampledTrace]
            rw [bindTrace_of_no_answers none _ (shareTuple (n + 1))]
      · cases n with
        | zero => rfl
        | succ n =>
            rw [resampledTrace_single]
            simp [lazyTrace, eagerTrace, Event.mapAnswer, shareTuple]

/-- Ordered agreement is stronger than bag agreement: it implies the bag laws
of `DemandAgreement`. -/
theorem bag_agreement_of_ordered (n : ℕ) (bound : Trace A E F)
    (eagerLazy : eagerTrace n bound = lazyTrace n bound)
    (lazyResampled : lazyTrace n bound = resampledTrace n bound) :
    eagerShared n (answerBag bound) = lazyShared n (answerBag bound) ∧
      lazyShared n (answerBag bound) = DemandAgreement.resampledUses n (answerBag bound) := by
  rw [← answerBag_eagerTrace, ← answerBag_lazyTrace, ← answerBag_resampledTrace,
    eagerLazy, lazyResampled]
  exact ⟨rfl, rfl⟩

/-! ## Completion and fusion -/

/-- **Fusion licence.**  Feeding a producer's live stream to a consumer, in
place of its completion, preserves the observation for every consumer exactly
when the completion policy leaves the producer's trace unchanged. -/
theorem fusion_licence_iff (complete : Trace A E F → Trace A E F) (producer : Trace A E F) :
    (∀ (B : Type) (consumer : A → Trace B E F),
      bindTrace (complete producer) consumer = bindTrace producer consumer) ↔
      complete producer = producer := by
  constructor
  · intro fused
    simpa using fused A fun value => [.answer value]
  · intro same B consumer
    rw [same]

/-- **Success priority**, the completion used by HE: if any answer occurred, the
faults are dropped; otherwise the run is kept. -/
def successPriority (trace : Trace A E F) : Trace A E F :=
  if answers trace = [] then trace else trace.filter fun event => !event.isFault

theorem successPriority_eq_self_iff (trace : Trace A E F) :
    successPriority trace = trace ↔ answers trace = [] ∨ ∀ event ∈ trace, event.isFault = false := by
  by_cases none : answers trace = []
  · simp [successPriority, none]
  · rw [successPriority, if_neg none, List.filter_eq_self]
    simp [none]

/-! ## Controls: the bag laws do not license these transformations -/

namespace Controls

/-- An answer after a committed effect. -/
def effectThenAnswer : Trace ℕ Unit Unit := [.effect (), .answer 1]

/-- **Changed demand of an unused effect.**  The bag law licenses discarding:
there is one answer.  The ordered observer sees the effect committed eagerly and
never lazily. -/
theorem unused_effect_control :
    eagerShared 0 (answerBag effectThenAnswer) = lazyShared 0 (answerBag effectThenAnswer) ∧
      eagerTrace 0 effectThenAnswer ≠ lazyTrace 0 effectThenAnswer := by
  constructor
  · exact (DemandAgreement.eagerShared_eq_lazyShared_iff 0 _).mpr (Or.inr rfl)
  · rw [Ne, eagerTrace_eq_lazyTrace_iff]
    rintro (impossible | ⟨value, equal⟩)
    · omega
    · simp [effectThenAnswer] at equal

/-- **A repeated committed effect.**  The bag law licenses resampling in place
of sharing: there is at most one answer.  The ordered observer sees the effect
committed twice. -/
theorem repeated_effect_control :
    lazyShared 2 (answerBag effectThenAnswer) =
        DemandAgreement.resampledUses 2 (answerBag effectThenAnswer) ∧
      lazyTrace 2 effectThenAnswer ≠ resampledTrace 2 effectThenAnswer ∧
      resampledTrace 2 effectThenAnswer = [.effect (), .effect (), .answer [1, 1]] := by
  refine ⟨(DemandAgreement.lazyShared_eq_resampledUses_iff 2 _).mpr (Or.inr (by decide)),
    ?_, by decide⟩
  rw [Ne, lazyTrace_eq_resampledTrace_iff]
  rintro (impossible | none | ⟨value, equal⟩)
  · omega
  · simp [effectThenAnswer, answers, Event.answer?] at none
  · simp [effectThenAnswer] at equal

/-- **Reordered answers**: equal bags, different ordered observations. -/
theorem reordering_control :
    answerBag ([.answer 1, .answer 2] : Trace ℕ Unit Unit) =
        answerBag ([.answer 2, .answer 1] : Trace ℕ Unit Unit) ∧
      ([.answer 1, .answer 2] : Trace ℕ Unit Unit) ≠ [.answer 2, .answer 1] := by
  refine ⟨?_, by decide⟩
  simp only [answerBag, answers, Event.answer?, List.filterMap_cons, List.filterMap_nil]
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap 2 1 [])

/-- **Lost equal occurrences**: equal answer sets, different ordered
observations. -/
theorem lost_occurrence_control :
    (answerBag ([.answer 1, .answer 1] : Trace ℕ Unit Unit)).toFinset =
        (answerBag ([.answer 1] : Trace ℕ Unit Unit)).toFinset ∧
      ([.answer 1, .answer 1] : Trace ℕ Unit Unit) ≠ [.answer 1] := by
  refine ⟨?_, by decide⟩
  simp [answerBag, answers, Event.answer?]

/-- The producer `[fault, 1, 1]`. -/
def faultThenTwo : Trace ℕ Unit Unit := [.fault (), .answer 1, .answer 1]

/-- A consumer that returns no answer. -/
def answerless : ℕ → Trace ℕ Unit Unit := fun _ => []

/-- **Early fault publication.**  `[fault, 1, 1]` completes to `[1, 1]`.  Its
completion consumed by an answerless consumer publishes nothing; its live
stream publishes the fault.  The answer bags of the two agree, so no bag law
can tell them apart. -/
theorem early_fault_control :
    successPriority faultThenTwo = [.answer 1, .answer 1] ∧
      bindTrace (successPriority faultThenTwo) answerless = [] ∧
      bindTrace faultThenTwo answerless = [.fault ()] ∧
      answerBag (bindTrace (successPriority faultThenTwo) answerless) =
        answerBag (bindTrace faultThenTwo answerless) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The completion observer and the streaming observer are different: fusion is
not licensed for this producer. -/
theorem streaming_is_not_completion :
    ¬ ∀ (B : Type) (consumer : ℕ → Trace B Unit Unit),
      bindTrace (successPriority faultThenTwo) consumer = bindTrace faultThenTwo consumer := by
  rw [fusion_licence_iff]
  decide

/-- Positive: a producer without faults may be fused. -/
theorem faultless_fusion (B : Type) (consumer : ℕ → Trace B Unit Unit) :
    bindTrace (successPriority ([.answer 1, .answer 1] : Trace ℕ Unit Unit)) consumer =
      bindTrace [.answer 1, .answer 1] consumer :=
  (fusion_licence_iff successPriority _).mpr (by decide) B consumer

/-- Positive: a single answer is discardable and copyable. -/
theorem single_answer_licences :
    eagerTrace 0 ([.answer 1] : Trace ℕ Unit Unit) = lazyTrace 0 [.answer 1] ∧
      lazyTrace 3 ([.answer 1] : Trace ℕ Unit Unit) = resampledTrace 3 [.answer 1] :=
  ⟨(eagerTrace_eq_lazyTrace_iff 0 _).mpr (Or.inr ⟨1, rfl⟩),
    (lazyTrace_eq_resampledTrace_iff 3 _).mpr (Or.inr (Or.inr ⟨1, rfl⟩))⟩

end Controls

end Mettapedia.GSLT.Dynamics.OrderedDemand
