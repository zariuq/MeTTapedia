import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2

/-!
# Ordered-state chronology: one reusable relational left fold

## Why this file exists

An evaluator whose step function returns a *list of result alternatives* paired
with a *single* final state has state effects that are ordered **across**
alternatives: the second alternative is computed in the state left behind by the
first.  A specification that pairs each alternative with its own private state,
or that quotients the alternatives by permutation, silently deletes that
sequencing.  So the chronology must be written down, not quotiented away.

The quotient-by-order discipline that is appropriate for *bindings* (a
substitution is a finite map, and the order in which its entries were discovered
carries no meaning) is therefore emphatically **not** appropriate for *state*.
Two orders of the same steps are two different runs whenever the steps interact
through the state.  The negative witness at the end of this file exhibits
exactly such a pair, so the reader can see that the relation defined here really
does distinguish them.

## Why one combinator instead of a rule per judgment

Every branching point of the evaluator — alternatives of a match, arguments of
an application, members of a space query — threads state the same way: run the
first, hand its state to the second, keep the emitted results in source order.
Writing that pattern into each judgment separately would mean re-proving
associativity, determinism transfer and order preservation once per judgment,
and would let the copies drift apart.  Instead `StateFoldRel` is stated once,
its structural laws are proved once, and each judgment cites them.

## Why it is parametric in the state type

The state type `sigma` is a parameter and is never instantiated here.  Keeping
it abstract is what lets this module sit *below* the runtime in the dependency
order: the specification of sequencing must not import the runtime's state
carrier, otherwise the specification could not be used to judge that carrier.
The file consequently imports nothing but `Mathlib.Data.List.Basic`.

## Shape of the step relation

`step : sigma → input → output → sigma → Prop` reads "from state `s`, input `i`
may produce output `o` and continue in state `s'`".  It is a *relation*, not a
function, because the evaluator is nondeterministic; it produces exactly one
output per input, because the fan-out into several alternatives is handled by
the surrounding judgment rather than by the chronology combinator.  That choice
is what makes `length` preservation exact, and it is the sharpest available
statement that outputs stay aligned with their inputs.
-/

namespace Mettapedia.Languages.MeTTa.HE.StateFoldChronology

universe u v w

/-- Relational left fold in input order.

`StateFoldRel step s₀ inputs outputs sₙ` holds when the inputs were consumed
left to right starting from `s₀`, each consuming step handing its resulting
state to its successor, ending in `sₙ`, with the emitted outputs listed in the
same order as the inputs that produced them.

The intermediate states are existentially quantified inside the `cons`
constructor rather than exposed in the conclusion.  That is deliberate: a client
judgment should be able to say "these inputs ran in this order" without having
to name, or agree on, the entire trace of intermediate states. -/
inductive StateFoldRel {sigma : Type u} {input : Type v} {output : Type w}
    (step : sigma → input → output → sigma → Prop) :
    sigma → List input → List output → sigma → Prop where
  /-- No inputs: no outputs are emitted and the state is handed on untouched. -/
  | nil (state : sigma) : StateFoldRel step state [] [] state
  /-- One step from `initial` to `middle`, then the remaining inputs from
  `middle`.  The head's output is placed *before* the tail's outputs, which is
  precisely the recorded chronology. -/
  | cons {initial middle final : sigma} {head : input} {tail : List input}
      {headOutput : output} {tailOutputs : List output} :
      step initial head headOutput middle →
      StateFoldRel step middle tail tailOutputs final →
      StateFoldRel step initial (head :: tail) (headOutput :: tailOutputs) final

variable {sigma : Type u} {input : Type v} {output : Type w}
variable {step : sigma → input → output → sigma → Prop}

/-! ## Inversion at the two ends -/

/-- Running no inputs is forced: nothing is emitted and the state is unchanged.
This is the fact that lets a client discharge the empty branch of a judgment
without an ad hoc argument. -/
theorem StateFoldRel.nil_inv {initial final : sigma} {outputs : List output}
    (run : StateFoldRel step initial [] outputs final) :
    outputs = [] ∧ final = initial := by
  cases run with
  | nil => exact ⟨rfl, rfl⟩

/-- Running one input is exactly one step of `step`. -/
theorem StateFoldRel.single {initial final : sigma} {i : input} {o : output}
    (transition : step initial i o final) :
    StateFoldRel step initial [i] [o] final :=
  StateFoldRel.cons transition (StateFoldRel.nil final)

/-- The converse of `StateFoldRel.single`: a one-input run contains no hidden
sequencing, so the combinator does not add structure at the leaves. -/
theorem StateFoldRel.single_inv {initial final : sigma} {i : input}
    {outputs : List output}
    (run : StateFoldRel step initial [i] outputs final) :
    ∃ o : output, outputs = [o] ∧ step initial i o final := by
  cases run with
  | cons headStep tailRun =>
      obtain ⟨tailNil, stateEq⟩ := StateFoldRel.nil_inv tailRun
      subst tailNil
      subst stateEq
      exact ⟨_, rfl, headStep⟩

/-- Peeling the first input off a run.  Stated separately from `cases` so that
downstream proofs get the intermediate state as a named witness. -/
theorem StateFoldRel.cons_inv {initial final : sigma} {head : input}
    {tail : List input} {outputs : List output}
    (run : StateFoldRel step initial (head :: tail) outputs final) :
    ∃ (middle : sigma) (headOutput : output) (tailOutputs : List output),
      outputs = headOutput :: tailOutputs ∧
        step initial head headOutput middle ∧
        StateFoldRel step middle tail tailOutputs final := by
  cases run with
  | cons headStep tailRun => exact ⟨_, _, _, rfl, headStep, tailRun⟩

/-! ## Composition -/

/-- Adjacent runs compose, threading the intermediate state and concatenating
the output blocks in order.  This is the associativity law that makes it
legitimate to chunk a branching point however is convenient. -/
theorem StateFoldRel.append {left right : List input}
    {initial middle final : sigma} {leftOutputs rightOutputs : List output}
    (leftRun : StateFoldRel step initial left leftOutputs middle)
    (rightRun : StateFoldRel step middle right rightOutputs final) :
    StateFoldRel step initial (left ++ right) (leftOutputs ++ rightOutputs)
      final := by
  induction leftRun with
  | nil => simpa using rightRun
  | cons headStep _ inductionHypothesis =>
      exact StateFoldRel.cons headStep (inductionHypothesis rightRun)

/-- The converse split: any run of a concatenation factors through a unique
segmentation point.  Without this direction the composition law would only let
one build runs, never analyse them, and client judgments need to analyse. -/
theorem StateFoldRel.append_inv {left right : List input}
    {initial final : sigma} {outputs : List output}
    (run : StateFoldRel step initial (left ++ right) outputs final) :
    ∃ (middle : sigma) (leftOutputs rightOutputs : List output),
      outputs = leftOutputs ++ rightOutputs ∧
        StateFoldRel step initial left leftOutputs middle ∧
        StateFoldRel step middle right rightOutputs final := by
  induction left generalizing initial outputs with
  | nil => exact ⟨initial, [], outputs, rfl, StateFoldRel.nil initial, run⟩
  | cons head tail inductionHypothesis =>
      obtain ⟨after, headOutput, restOutputs, outputsEq, headStep, restRun⟩ :=
        StateFoldRel.cons_inv run
      obtain ⟨middle, leftOutputs, rightOutputs, restEq, leftRun, rightRun⟩ :=
        inductionHypothesis restRun
      refine ⟨middle, headOutput :: leftOutputs, rightOutputs, ?_,
        StateFoldRel.cons headStep leftRun, rightRun⟩
      subst outputsEq
      subst restEq
      simp

/-! ## Order preservation -/

/-- Outputs are positionally aligned with the inputs that produced them: the
`n`-th output is the output of some transition on the `n`-th input.  This is the
precise sense in which the fold "keeps input order" — it rules out any
reshuffling, duplication or dropping of outputs. -/
theorem StateFoldRel.positionwise {initial final : sigma} {inputs : List input}
    {outputs : List output}
    (run : StateFoldRel step initial inputs outputs final) :
    List.Forall₂ (fun i o => ∃ a b : sigma, step a i o b) inputs outputs := by
  induction run with
  | nil => exact List.Forall₂.nil
  | cons headStep _ inductionHypothesis =>
      exact List.Forall₂.cons ⟨_, _, headStep⟩ inductionHypothesis

/-- Exactly one output per input. -/
theorem StateFoldRel.length_eq {initial final : sigma} {inputs : List input}
    {outputs : List output}
    (run : StateFoldRel step initial inputs outputs final) :
    outputs.length = inputs.length :=
  (run.positionwise.length_eq).symm

/-- A rejection witness at the level of the general combinator: a nonempty input
list can never run to an empty output list.  A relation that accepted this would
be useless as a specification, so it is worth recording that this one does not.
-/
theorem StateFoldRel.not_cons_nil {initial final : sigma} {head : input}
    {tail : List input} :
    ¬ StateFoldRel step initial (head :: tail) [] final := by
  intro run
  have := run.length_eq
  simp at this

/-! ## Determinism transfer -/

/-- A step relation is deterministic when the state and input fix both the
output and the successor state. -/
def StepDeterministic (step : sigma → input → output → sigma → Prop) : Prop :=
  ∀ (s : sigma) (i : input) (o₁ : output) (f₁ : sigma) (o₂ : output)
    (f₂ : sigma), step s i o₁ f₁ → step s i o₂ f₂ → o₁ = o₂ ∧ f₁ = f₂

/-- Determinism transfers from the step to the whole chronology.  This is what
lets a deterministic implementation be compared against the relational
specification without a scheduling side condition. -/
theorem StateFoldRel.deterministic (hstep : StepDeterministic step)
    {initial : sigma} {inputs : List input}
    {outputs₁ outputs₂ : List output} {final₁ final₂ : sigma}
    (run₁ : StateFoldRel step initial inputs outputs₁ final₁)
    (run₂ : StateFoldRel step initial inputs outputs₂ final₂) :
    outputs₁ = outputs₂ ∧ final₁ = final₂ := by
  induction run₁ generalizing outputs₂ final₂ with
  | nil =>
      obtain ⟨outputsEq, stateEq⟩ := StateFoldRel.nil_inv run₂
      exact ⟨outputsEq.symm, stateEq.symm⟩
  | @cons initial middle final head tail headOutput tailOutputs headStep _
      inductionHypothesis =>
      obtain ⟨middle₂, headOutput₂, tailOutputs₂, outputsEq, headStep₂,
        tailRun₂⟩ := StateFoldRel.cons_inv run₂
      obtain ⟨outputEq, middleEq⟩ :=
        hstep initial head headOutput middle headOutput₂ middle₂ headStep
          headStep₂
      subst middleEq
      obtain ⟨tailEq, finalEq⟩ := inductionHypothesis tailRun₂
      subst outputsEq
      subst outputEq
      subst tailEq
      exact ⟨rfl, finalEq⟩

/-! ## The state-free fragment: chronology collapses -/

/-- A step relation is state-free when it never modifies the state.  This is the
hypothesis under which sequencing carries no information. -/
def StepStateFree (step : sigma → input → output → sigma → Prop) : Prop :=
  ∀ (s : sigma) (i : input) (o : output) (f : sigma), step s i o f → f = s

/-- If no step changes the state, no run changes the state. -/
theorem StateFoldRel.state_free_preserves (hstep : StepStateFree step)
    {initial final : sigma} {inputs : List input} {outputs : List output}
    (run : StateFoldRel step initial inputs outputs final) :
    final = initial := by
  induction run with
  | nil => rfl
  | @cons initial middle _ head _ headOutput _ headStep _ inductionHypothesis =>
      have middleEq := hstep initial head headOutput middle headStep
      subst middleEq
      exact inductionHypothesis

/-- Over a state-free step the chronology degenerates completely: a run is
nothing but a pointwise relation between inputs and outputs at the *fixed*
state, with no sequencing left to record.  This is the bridge that lets the
state-free fragment of a specification be stated without any fold at all, and it
is the exact boundary the negative witness below shows cannot be crossed in
general. -/
theorem StateFoldRel.state_free_iff (hstep : StepStateFree step)
    {initial final : sigma} {inputs : List input} {outputs : List output} :
    StateFoldRel step initial inputs outputs final ↔
      final = initial ∧
        List.Forall₂ (fun i o => step initial i o initial) inputs outputs := by
  constructor
  · intro run
    refine ⟨StateFoldRel.state_free_preserves hstep run, ?_⟩
    induction run with
    | nil => exact List.Forall₂.nil
    | @cons initial middle _ head _ headOutput _ headStep _
        inductionHypothesis =>
        have middleEq := hstep initial head headOutput middle headStep
        subst middleEq
        exact List.Forall₂.cons headStep inductionHypothesis
  · rintro ⟨rfl, pointwise⟩
    induction pointwise with
    | nil => exact StateFoldRel.nil final
    | cons headStep _ inductionHypothesis =>
        exact StateFoldRel.cons headStep inductionHypothesis

/-! ## Negative witness: the fold genuinely records chronology

Everything above is compatible with `StateFoldRel` being secretly insensitive to
order.  It is not, and the cleanest way to know that is a concrete
counterexample rather than an appeal to the shape of the definition.

`pushPrefix` uses `List Nat` as the state and pushes each input onto it.  It is
about as small as a non-commutative effect can be, and the state carrier is
plainly unrelated to any runtime, which is the point: order sensitivity is a
property of the combinator, not of any particular evaluator. -/

/-- Push the input onto the state stack and echo it as the output. -/
def pushPrefix : List Nat → Nat → Nat → List Nat → Prop :=
  fun state i o state' => o = i ∧ state' = i :: state

theorem pushPrefix_deterministic : StepDeterministic pushPrefix := by
  rintro s i o₁ f₁ o₂ f₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-- Positive witness: `[1, 2]` really does run, emitting `[1, 2]` and ending in
the reversed stack `[2, 1]`. -/
theorem pushPrefix_run_one_two :
    StateFoldRel pushPrefix [] [1, 2] [1, 2] [2, 1] :=
  StateFoldRel.cons ⟨rfl, rfl⟩ (StateFoldRel.single ⟨rfl, rfl⟩)

/-- Positive witness for the swapped input order.  Same multiset of steps, same
starting state, **different** final state. -/
theorem pushPrefix_run_two_one :
    StateFoldRel pushPrefix [] [2, 1] [2, 1] [1, 2] :=
  StateFoldRel.cons ⟨rfl, rfl⟩ (StateFoldRel.single ⟨rfl, rfl⟩)

/-- Negative witness: the swapped run cannot reach the unswapped final state.
Proved from determinism rather than by raw inversion, so it also exercises
`StateFoldRel.deterministic`. -/
theorem pushPrefix_swap_rejected :
    ¬ StateFoldRel pushPrefix [] [2, 1] [2, 1] [2, 1] := by
  intro run
  obtain ⟨_, finalEq⟩ :=
    StateFoldRel.deterministic pushPrefix_deterministic run
      pushPrefix_run_two_one
  exact absurd finalEq (by decide)

/-- Negative witness of the second kind: the outputs are constrained too, so the
relation rejects a mismatched output list as well as a mismatched state. -/
theorem pushPrefix_wrong_output_rejected :
    ¬ StateFoldRel pushPrefix [] [1, 2] [2, 1] [2, 1] := by
  intro run
  obtain ⟨outputsEq, _⟩ :=
    StateFoldRel.deterministic pushPrefix_deterministic run
      pushPrefix_run_one_two
  exact absurd outputsEq (by decide)

/-- Negative witness of the third kind: the input list must be consumed
entirely, so a short output list is rejected. -/
theorem pushPrefix_short_output_rejected :
    ¬ StateFoldRel pushPrefix [] [1, 2] [1] [2, 1] := by
  intro run
  have := run.length_eq
  simp at this

/-- The chronology is not order-insensitive: there are two runs of the *same*
step relation on permuted input lists, from the same initial state, whose final
states differ.  Consequently no specification built on `StateFoldRel` may be
quotiented by permutation of the inputs, and the state-free collapse above is a
genuinely restricted bridge rather than a general theorem. -/
theorem chronology_is_order_sensitive :
    ∃ (inputs₁ inputs₂ : List Nat) (outputs₁ outputs₂ : List Nat)
      (final₁ final₂ : List Nat),
      inputs₁.Perm inputs₂ ∧
        StateFoldRel pushPrefix [] inputs₁ outputs₁ final₁ ∧
        StateFoldRel pushPrefix [] inputs₂ outputs₂ final₂ ∧
        final₁ ≠ final₂ :=
  ⟨[1, 2], [2, 1], [1, 2], [2, 1], [2, 1], [1, 2],
    List.Perm.swap 2 1 [], pushPrefix_run_one_two, pushPrefix_run_two_one,
    by decide⟩

/-- Contrast case, to show the state-free bridge is not vacuous: a step that
only echoes its input is state-free, and its runs are exactly the identity
pairings, with the state untouched. -/
def echoOnly : List Nat → Nat → Nat → List Nat → Prop :=
  fun state i o state' => o = i ∧ state' = state

theorem echoOnly_state_free : StepStateFree echoOnly := by
  rintro s i o f ⟨_, rfl⟩
  rfl

/-- Positive witness on the collapsed side: with a state-free step both input
orders end in the same state, so the chronology carries no information there. -/
theorem echoOnly_order_irrelevant
    {inputs₁ inputs₂ outputs₁ outputs₂ final₁ final₂ : List Nat}
    {initial : List Nat}
    (run₁ : StateFoldRel echoOnly initial inputs₁ outputs₁ final₁)
    (run₂ : StateFoldRel echoOnly initial inputs₂ outputs₂ final₂) :
    final₁ = final₂ := by
  rw [StateFoldRel.state_free_preserves echoOnly_state_free run₁,
    StateFoldRel.state_free_preserves echoOnly_state_free run₂]

/-- And the collapsed form really is the pointwise one. -/
theorem echoOnly_run_iff {initial final : List Nat}
    {inputs outputs : List Nat} :
    StateFoldRel echoOnly initial inputs outputs final ↔
      final = initial ∧ outputs = inputs := by
  rw [StateFoldRel.state_free_iff echoOnly_state_free]
  constructor
  · rintro ⟨stateEq, pointwise⟩
    refine ⟨stateEq, ?_⟩
    induction pointwise with
    | nil => rfl
    | cons headStep _ inductionHypothesis =>
        rw [headStep.1, inductionHypothesis]
  · rintro ⟨stateEq, rfl⟩
    refine ⟨stateEq, ?_⟩
    induction outputs with
    | nil => exact List.Forall₂.nil
    | cons head tail inductionHypothesis =>
        exact List.Forall₂.cons ⟨rfl, rfl⟩ inductionHypothesis

end Mettapedia.Languages.MeTTa.HE.StateFoldChronology
