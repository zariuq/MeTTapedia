import Mettapedia.GSLT.Dynamics.ContextualEffectValuation

/-!
# Interleaving realizations of effect traces

An effectful nondeterministic program does not need commuting effects in order
to run.  It needs a realization whose global trace preserves the local order
of every branch.  Commutation is a stronger fact: it proves that all such
traces have the same denotation and therefore licenses reordering, batching,
or a deterministic parallel optimization.

This module presents that distinction at the trace boundary below contextual
effect handlers.  `Shuffle left right trace` is the free interleaving product
of two chronological traces.  A `Realization` retains the selected trace and
its order-preservation proof.  The two serialized traces are always legal, so
resource capabilities can select a realization without becoming permissions
to execute the source program.

When every cross-branch pair commutes as state endomorphisms, every legal
interleaving has the same endpoint as the left-then-right trace.  The negative
example shows why this theorem must remain an optimization license: two legal
serialized realizations of noncommuting writes can expose different states.

Grouping a trace with `block` makes its internal steps one atomic action at
the next layer.  This is the algebraic seam used by mutex and transactional
realizations; atomic grouping restricts interleavings without rejecting the
underlying computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.EffectTraceInterleaving

universe uEvent uState

/-! ## The shuffle product -/

/-- A chronological trace obtained by interleaving two branch-local traces
while preserving the order within each branch.  Equal event payloads remain
distinct occurrences because the derivation records which branch supplied
each head. -/
inductive Shuffle {Event : Type uEvent} :
    List Event → List Event → List Event → Prop
  | nil : Shuffle [] [] []
  | left {event : Event} {left right trace : List Event} :
      Shuffle left right trace →
      Shuffle (event :: left) right (event :: trace)
  | right {event : Event} {left right trace : List Event} :
      Shuffle left right trace →
      Shuffle left (event :: right) (event :: trace)

namespace Shuffle

variable {Event : Type uEvent}

/-- An empty left branch leaves the right trace unchanged. -/
theorem nil_left (right : List Event) : Shuffle [] right right := by
  induction right with
  | nil => exact .nil
  | cons event tail inductionHypothesis =>
      exact .right inductionHypothesis

/-- Running the complete left trace before the right trace is always a legal
interleaving. -/
theorem append (left right : List Event) :
    Shuffle left right (left ++ right) := by
  induction left with
  | nil => exact nil_left right
  | cons event tail inductionHypothesis =>
      exact .left inductionHypothesis

/-- Running the complete right trace before the left trace is also legal. -/
theorem append_commuted (left right : List Event) :
    Shuffle left right (right ++ left) := by
  induction right with
  | nil => simpa using append left []
  | cons event tail inductionHypothesis =>
      exact .right inductionHypothesis

/-- Every legal interleaving contains exactly the occurrences of both source
traces. -/
theorem perm_append {left right trace : List Event}
    (legal : Shuffle left right trace) : trace.Perm (left ++ right) := by
  induction legal with
  | nil => exact List.Perm.refl []
  | left legal inductionHypothesis =>
      exact inductionHypothesis.cons _
  | @right event left right trace legal inductionHypothesis =>
      exact (inductionHypothesis.cons event).trans (by
        simpa only [List.cons_append] using
          (@List.perm_middle Event event left right).symm)

end Shuffle

/-! ## Total realization choice -/

/-- One physical scheduling realization of two authored branch traces. -/
structure Realization {Event : Type uEvent}
    (left right : List Event) where
  trace : List Event
  legal : Shuffle left right trace

namespace Realization

variable {Event : Type uEvent}

/-- Canonical left-to-right serialized realization. -/
def leftSerial (left right : List Event) : Realization left right :=
  ⟨left ++ right, Shuffle.append left right⟩

/-- Canonical right-to-left serialized realization. -/
def rightSerial (left right : List Event) : Realization left right :=
  ⟨right ++ left, Shuffle.append_commuted left right⟩

/-- No pair of traces is refused merely because a backend cannot establish a
parallel commutation certificate: serialization always supplies a lawful
realization. -/
theorem inhabited (left right : List Event) :
    Nonempty (Realization left right) :=
  ⟨leftSerial left right⟩

/-- A realization preserves exact occurrence multiplicity. -/
theorem trace_perm_append {left right : List Event}
    (realization : Realization left right) :
    realization.trace.Perm (left ++ right) :=
  realization.legal.perm_append

end Realization

/-! ## Denotation and the commutation license -/

/-- Execute an atomic event trace as a chronological fold. -/
def run {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (initial : State) :
    List Event → State :=
  List.foldl step initial

@[simp] theorem run_nil {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (initial : State) :
    run step initial [] = initial :=
  rfl

@[simp] theorem run_cons {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (initial : State)
    (event : Event) (trace : List Event) :
    run step initial (event :: trace) =
      run step (step initial event) trace :=
  rfl

theorem run_append {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (initial : State)
    (first second : List Event) :
    run step initial (first ++ second) =
      run step (run step initial first) second := by
  simp [run, List.foldl_append]

/-- Every event of the left branch commutes with every event of the right
branch as a state endomorphism. -/
def CrossCommutes {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (left right : List Event) : Prop :=
  ∀ leftEvent ∈ left, ∀ rightEvent ∈ right, ∀ state,
    step (step state leftEvent) rightEvent =
      step (step state rightEvent) leftEvent

private theorem run_after_right_eq_right_after_run
    {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (rightEvent : Event)
    (left : List Event)
    (commutes : ∀ leftEvent ∈ left, ∀ state,
      step (step state leftEvent) rightEvent =
        step (step state rightEvent) leftEvent)
    (initial : State) :
    run step (step initial rightEvent) left =
      step (run step initial left) rightEvent := by
  induction left generalizing initial with
  | nil => rfl
  | cons leftEvent tail inductionHypothesis =>
      rw [run_cons, (commutes leftEvent (by simp) initial).symm]
      exact inductionHypothesis
        (fun event member => commutes event (by simp [member]))
        (step initial leftEvent)

/-- Pairwise cross-branch commutation makes every legal interleaving agree
with the canonical left-to-right serialized endpoint. -/
theorem run_eq_leftSerial_of_crossCommutes
    {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State)
    {left right trace : List Event}
    (legal : Shuffle left right trace)
    (commutes : CrossCommutes step left right)
    (initial : State) :
    run step initial trace = run step initial (left ++ right) := by
  induction legal generalizing initial with
  | nil => rfl
  | @left event left right trace legal inductionHypothesis =>
      rw [run_cons, List.cons_append, run_cons]
      exact inductionHypothesis
        (fun leftEvent member rightEvent rightMember state =>
          commutes leftEvent (by simp [member])
            rightEvent rightMember state)
        (step initial event)
  | @right event left right trace legal inductionHypothesis =>
      have tailCommutes : CrossCommutes step left right :=
        fun leftEvent leftMember rightEvent rightMember state =>
          commutes leftEvent leftMember rightEvent
            (by simp [rightMember]) state
      have eventCommutes : ∀ leftEvent ∈ left, ∀ state,
          step (step state leftEvent) event =
            step (step state event) leftEvent :=
        fun leftEvent leftMember state =>
          commutes leftEvent leftMember event (by simp) state
      calc
        run step initial (event :: trace) =
            run step (step initial event) trace := rfl
        _ = run step (step initial event) (left ++ right) :=
            inductionHypothesis tailCommutes (step initial event)
        _ = run step
              (run step (step initial event) left) right :=
            run_append step (step initial event) left right
        _ = run step
              (step (run step initial left) event) right := by
            rw [run_after_right_eq_right_after_run
              step event left eventCommutes initial]
        _ = run step initial (left ++ event :: right) := by
            rw [run_append, run_cons]

/-- The theorem packaged at the physical-realization boundary. -/
theorem realization_endpoint_unique_of_crossCommutes
    {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State)
    {left right : List Event}
    (realization : Realization left right)
    (commutes : CrossCommutes step left right)
    (initial : State) :
    run step initial realization.trace =
      run step initial (Realization.leftSerial left right).trace :=
  run_eq_leftSerial_of_crossCommutes step realization.legal commutes initial

/-! ## Atomic grouping -/

/-- Treat a complete chronological trace as one atomic action at the next
interleaving layer. -/
def block {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (events : List Event) : State → State :=
  fun initial => run step initial events

/-- Grouping respects chronological composition. -/
theorem block_append {Event : Type uEvent} {State : Type uState}
    (step : State → Event → State) (first second : List Event)
    (initial : State) :
    block step (first ++ second) initial =
      block step second (block step first initial) :=
  run_append step initial first second

/-! ## Positive and negative controls -/

namespace Canary

/-- Additive state effects commute across branches. -/
def addStep (state event : Nat) : Nat := state + event

theorem additive_crossCommutes (left right : List Nat) :
    CrossCommutes addStep left right := by
  intro leftEvent _ rightEvent _ state
  simp [addStep, Nat.add_comm, Nat.add_left_comm]

/-- Every physical schedule of additive effects has the same endpoint. -/
theorem additive_realizations_agree
    (left right : List Nat) (realization : Realization left right)
    (initial : Nat) :
    run addStep initial realization.trace =
      run addStep initial (left ++ right) :=
  run_eq_leftSerial_of_crossCommutes addStep realization.legal
    (additive_crossCommutes left right) initial

inductive Write where
  | setOne
  | double
deriving DecidableEq

/-- Two deliberately noncommuting shared-state actions. -/
def writeStep (state : Nat) : Write → Nat
  | .setOne => 1
  | .double => state * 2

def setThenDouble : Realization [Write.setOne] [Write.double] :=
  Realization.leftSerial _ _

def doubleThenSet : Realization [Write.setOne] [Write.double] :=
  Realization.rightSerial _ _

/-- Both schedules are legal, yet their observable states differ.  Hence
commutation cannot be an admission condition for effectful concurrency. -/
theorem noncommuting_realizations_are_both_legal_and_distinct :
    Shuffle [Write.setOne] [Write.double] setThenDouble.trace ∧
      Shuffle [Write.setOne] [Write.double] doubleThenSet.trace ∧
      run writeStep 3 setThenDouble.trace = 2 ∧
      run writeStep 3 doubleThenSet.trace = 1 := by
  exact ⟨setThenDouble.legal, doubleThenSet.legal, rfl, rfl⟩

/-- The negative control bites the commutation premise itself. -/
theorem writes_do_not_crossCommute :
    ¬ CrossCommutes writeStep [Write.setOne] [Write.double] := by
  intro commutes
  have impossible := commutes Write.setOne (by simp) Write.double
    (by simp) 3
  simp [writeStep] at impossible

end Canary

/-! ## Axiom audit -/

#print axioms Shuffle.perm_append
#print axioms Realization.inhabited
#print axioms run_eq_leftSerial_of_crossCommutes
#print axioms realization_endpoint_unique_of_crossCommutes
#print axioms block_append
#print axioms Canary.additive_realizations_agree
#print axioms Canary.noncommuting_realizations_are_both_legal_and_distinct
#print axioms Canary.writes_do_not_crossCommute

end Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
