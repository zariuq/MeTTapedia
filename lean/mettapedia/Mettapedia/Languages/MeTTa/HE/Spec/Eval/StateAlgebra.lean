/-!
# Ordered state/list evaluation algebra

The published evaluator describes ordered loops whose bodies may emit many
results.  A stateful implementation must therefore thread one state through
the source list: later alternatives observe effects produced by earlier
alternatives.  A per-result may relation cannot express that chronology.

`OrderedStateFlatMapRel` is the executable-independent relational boundary
for those loops.  It mentions neither a concrete evaluator state nor a
concrete scheduler.  The state type and one-source transition relation remain
parameters; the relation records only source order, concatenation of emitted
results, and the final state.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra

/-- Relational `StateT state List` traversal in source order.  Each source
element sees the state returned by its predecessor, may emit any finite list
of results, and contributes those results before the tail's results. -/
inductive OrderedStateFlatMapRel
    (step : source → state → List result → state → Prop) :
    List source → state → List result → state → Prop where
  | nil (initial : state) :
      OrderedStateFlatMapRel step [] initial [] initial
  | cons {head : source} {tail : List source}
      {initial middle final : state}
      {headResults tailResults : List result} :
      step head initial headResults middle →
      OrderedStateFlatMapRel step tail middle tailResults final →
      OrderedStateFlatMapRel step (head :: tail) initial
        (headResults ++ tailResults) final

/-- One source transition is the singleton traversal. -/
theorem OrderedStateFlatMapRel.singleton
    {step : source → state → List result → state → Prop}
    {source : source} {initial final : state} {results : List result}
    (transition : step source initial results final) :
    OrderedStateFlatMapRel step [source] initial results final := by
  simpa using OrderedStateFlatMapRel.cons transition
    (OrderedStateFlatMapRel.nil final)

/-- Adjacent traversals compose without reordering their result blocks. -/
theorem OrderedStateFlatMapRel.append
    {step : source → state → List result → state → Prop}
    {left right : List source} {initial middle final : state}
    {leftResults rightResults : List result}
    (leftRun : OrderedStateFlatMapRel step left initial leftResults middle)
    (rightRun : OrderedStateFlatMapRel step right middle rightResults final) :
    OrderedStateFlatMapRel step (left ++ right) initial
      (leftResults ++ rightResults) final := by
  induction leftRun with
  | nil => simpa using rightRun
  | @cons head tail initial firstMiddle middle headResults tailResults
      headStep tailRun inductionHypothesis =>
      simpa [List.append_assoc] using
        OrderedStateFlatMapRel.cons headStep
          (inductionHypothesis rightRun)

/-- A traversal of no sources is forced to emit no results and preserve the
state.  This is the negative boundary that rules out hidden empty-input
effects. -/
theorem OrderedStateFlatMapRel.nil_iff
    {step : source → state → List result → state → Prop}
    {initial final : state} {results : List result} :
    OrderedStateFlatMapRel step [] initial results final ↔
      results = [] ∧ final = initial := by
  constructor
  · intro run
    cases run
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact OrderedStateFlatMapRel.nil _

/-! ## Chronology canaries -/

/-- A tiny stateful step: emit the updated counter and retain it as state. -/
private def addStep
    (increment initial : Nat) (results : List Nat) (final : Nat) : Prop :=
  results = [initial + increment] ∧ final = initial + increment

/-- Positive: the second alternative observes the state produced by the
first, so the outputs are `1` and then `3`. -/
theorem ordered_state_threads_across_alternatives :
    OrderedStateFlatMapRel addStep [1, 2] 0 [1, 3] 3 := by
  apply OrderedStateFlatMapRel.cons
      (middle := 1) (headResults := [1]) (tailResults := [3])
  · exact ⟨rfl, rfl⟩
  · apply OrderedStateFlatMapRel.cons
        (middle := 3) (headResults := [3]) (tailResults := [])
    · exact ⟨rfl, rfl⟩
    · exact .nil 3

private theorem addStep_final_state
    {increments : List Nat} {initial final : Nat} {results : List Nat}
    (run : OrderedStateFlatMapRel addStep increments initial results final) :
    final = initial + increments.sum := by
  induction run with
  | nil => simp
  | @cons increment increments initial middle final
      headResults tailResults headStep _ inductionHypothesis =>
      rcases headStep with ⟨_headResults, rfl⟩
      rw [inductionHypothesis]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Negative: interpreting sibling alternatives from the same initial state
would emit `[1, 2]` and finish at `2`; that branch-isolated behavior is not an
ordered state traversal. -/
theorem branch_isolated_state_is_rejected :
    ¬OrderedStateFlatMapRel addStep [1, 2] 0 [1, 2] 2 := by
  intro run
  have finalState := addStep_final_state run
  simp at finalState

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.StateAlgebra
