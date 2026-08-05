import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Forward-unlocked signal propagation

Kohan, Rietman, and Siegelmann, *Signal Propagation: A Framework for Learning
and Inference In a Forward Pass* (IEEE TNNLS 2022, arXiv:2204.01723),
propagate an input activation and a generated learning target through the same
forward layers.  Each layer compares its two local outputs and can emit its
update as soon as that layer is reached.

This file isolates the structural theorem behind that claim.  A
`ForwardSignalLayer` has one forward map, used identically by the activation
and target streams, and a local update readout.  The resulting execution:

* is exactly two applications of the ordinary forward path;
* factors over concatenated layer schedules;
* emits every prefix's updates independently of every suffix; and
* admits a streaming implementation equal to the corresponding stored trace.

The prefix theorem requires the initial target generator to be independent of
the downstream suffix.  The source's target-only and target-input generators
have this property.  Its output-conditioned target-loop construction does not
have it as a single acyclic pass: a concrete fixture shows that appending a
downstream layer can change the first update.  Such a loop must instead be
given an explicit recurrent-time or delayed-output semantics.

These are dependency and scheduling results.  They do not assert that a local
signal is a gradient, that it aligns with backpropagation, or that it improves
a task objective.

Source artifact SHA-256:
`8db57a91ed76fa22058c1fe9e4b6b7dfd5a22ceebc9990ebf34324305c9d8ef1`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SignalPropagationForwardUnlock

/-- A layer applies one and the same forward computation to ordinary
activations and generated targets.  Its update readout is local to the two
outputs of that layer. -/
structure ForwardSignalLayer (State Update : Type) where
  forward : State → State
  localUpdate : State → State → Update

variable {State Update Context : Type}

/-- Advance both the activation and target streams through the same layer. -/
def ForwardSignalLayer.step
    (layer : ForwardSignalLayer State Update)
    (state : State × State) : State × State :=
  (layer.forward state.1, layer.forward state.2)

/-- Advance one ordinary stream through a list of forward layers. -/
def propagate
    (layers : List (ForwardSignalLayer State Update))
    (state : State) : State :=
  match layers with
  | [] => state
  | layer :: rest => propagate rest (layer.forward state)

/-- Final paired state after propagating activation and target together. -/
def runState
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) : State × State :=
  match layers with
  | [] => state
  | layer :: rest => runState rest (layer.step state)

/-- Stream the local update at each layer, then continue forward. -/
def runUpdates
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) : List Update :=
  match layers with
  | [] => []
  | layer :: rest =>
      let next := layer.step state
      layer.localUpdate next.1 next.2 :: runUpdates rest next

/-- Materialize every post-layer paired state.  This is the stored-trace
reference implementation, not the preferred streaming schedule. -/
def stateTrace
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) : List (State × State) :=
  match layers with
  | [] => []
  | layer :: rest =>
      let next := layer.step state
      next :: stateTrace rest next

/-- Read all local updates after first materializing the paired-state trace. -/
def storedTraceUpdates
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) : List Update :=
  List.zipWith
    (fun layer next => layer.localUpdate next.1 next.2)
    layers
    (stateTrace layers state)

/-- Streaming each update immediately is extensionally equal to materializing
the entire paired-state trace and reading it afterward. -/
theorem runUpdates_eq_storedTraceUpdates
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) :
    runUpdates layers state = storedTraceUpdates layers state := by
  induction layers generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [runUpdates, storedTraceUpdates, stateTrace, List.zipWith_cons_cons]
      rw [ih]
      rfl

/-- The paired executor is exactly the ordinary forward executor applied once
to each component. -/
theorem runState_eq_pair_propagate
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) :
    runState layers state =
      (propagate layers state.1, propagate layers state.2) := by
  induction layers generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [runState, propagate]
      exact ih (layer.step state)

/-- Forward propagation factors over schedule concatenation. -/
theorem propagate_append
    (front suffix : List (ForwardSignalLayer State Update))
    (state : State) :
    propagate (front ++ suffix) state =
      propagate suffix (propagate front state) := by
  induction front generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.cons_append, propagate]
      exact ih (layer.forward state)

/-- Paired propagation factors over schedule concatenation. -/
theorem runState_append
    (front suffix : List (ForwardSignalLayer State Update))
    (state : State × State) :
    runState (front ++ suffix) state =
      runState suffix (runState front state) := by
  induction front generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.cons_append, runState]
      exact ih (layer.step state)

/-- The streamed update trace factors into a completed prefix followed by the
suffix starting from the prefix's final state. -/
theorem runUpdates_append
    (front suffix : List (ForwardSignalLayer State Update))
    (state : State × State) :
    runUpdates (front ++ suffix) state =
      runUpdates front state ++
        runUpdates suffix (runState front state) := by
  induction front generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.cons_append, runUpdates, runState, List.cons_append]
      rw [ih]

/-- Exactly one update is emitted per forward layer. -/
theorem length_runUpdates
    (layers : List (ForwardSignalLayer State Update))
    (state : State × State) :
    (runUpdates layers state).length = layers.length := by
  induction layers generalizing state with
  | nil => rfl
  | cons layer rest ih =>
      simp only [runUpdates, List.length_cons]
      rw [ih]

/-- Once a layer is reached, its update is independent of every downstream
suffix. -/
theorem firstUpdate_suffix_independent
    (layer : ForwardSignalLayer State Update)
    (left right : List (ForwardSignalLayer State Update))
    (state : State × State) :
    (runUpdates (layer :: left) state).head? =
      (runUpdates (layer :: right) state).head? := by
  rfl

/-- All updates emitted by a prefix are independent of every suffix. -/
theorem prefixUpdates_suffix_independent
    (front left right : List (ForwardSignalLayer State Update))
    (state : State × State) :
    (runUpdates (front ++ left) state).take front.length =
      (runUpdates (front ++ right) state).take front.length := by
  rw [runUpdates_append, runUpdates_append]
  rw [← length_runUpdates front state]
  simp only [List.take_left]

/-! ## Target-generator boundary -/

/-- A target generator is suffix-independent when extending or changing the
network after a fixed prefix cannot change the generated initial target. -/
def TargetGeneratorSuffixIndependent
    (generator :
      List (ForwardSignalLayer State Update) → Context → State) : Prop :=
  ∀ front left right context,
    generator (front ++ left) context =
      generator (front ++ right) context

/-- Target-only and target-input generators, represented by a fixed function
of context, are suffix-independent. -/
theorem fixedTargetGenerator_suffixIndependent
    (generator : Context → State) :
    @TargetGeneratorSuffixIndependent State Update Context
      (fun _ context => generator context) := by
  intro front left right context
  rfl

/-- Run signal propagation using an explicit target generator. -/
def generatedUpdates
    (generator :
      List (ForwardSignalLayer State Update) → Context → State)
    (layers : List (ForwardSignalLayer State Update))
    (input : State)
    (context : Context) : List Update :=
  runUpdates layers (input, generator layers context)

/-- A suffix-independent target generator preserves the full prefix-unlocking
theorem. -/
theorem generatedPrefixUpdates_suffix_independent
    (generator :
      List (ForwardSignalLayer State Update) → Context → State)
    (hgenerator : TargetGeneratorSuffixIndependent generator)
    (front left right : List (ForwardSignalLayer State Update))
    (input : State)
    (context : Context) :
    (generatedUpdates generator (front ++ left) input context).take
        front.length =
      (generatedUpdates generator (front ++ right) input context).take
        front.length := by
  have htarget := hgenerator front left right context
  unfold generatedUpdates
  rw [htarget]
  exact
    prefixUpdates_suffix_independent
      front left right
      (input, generator (front ++ right) context)

/-! ## Executable positive and negative fixtures -/

/-- A layer that doubles both streams and reports their difference. -/
def doubleDifferenceLayer : ForwardSignalLayer ℤ ℤ where
  forward x := 2 * x
  localUpdate activation target := target - activation

/-- A layer that increments both streams and reports their difference. -/
def incrementDifferenceLayer : ForwardSignalLayer ℤ ℤ where
  forward x := x + 1
  localUpdate activation target := target - activation

/-- The two-layer positive fixture demonstrates that the same forward
computation is applied to both streams and each update is emitted in order. -/
theorem twoLayer_streaming :
    runState
        [doubleDifferenceLayer, incrementDifferenceLayer]
        (1, 3) =
      (3, 7) ∧
    runUpdates
        [doubleDifferenceLayer, incrementDifferenceLayer]
        (1, 3) =
      [4, 4] := by
  norm_num
    [runState, runUpdates, ForwardSignalLayer.step,
      doubleDifferenceLayer, incrementDifferenceLayer]

/-- An identity observation layer used to expose an output-conditioned target
generator's suffix dependency. -/
def identityDifferenceLayer : ForwardSignalLayer ℤ ℤ where
  forward x := x
  localUpdate activation target := target - activation

/-- An output-conditioned generator feeds the final forward output back as the
initial target.  This models the within-pass dependency of the source's
target-loop equations when no recurrent delay is specified. -/
def outputConditionedTarget
    (layers : List (ForwardSignalLayer ℤ ℤ))
    (context : ℤ) : ℤ :=
  propagate layers context

/-- Appending an increment layer changes the first update from zero to one:
single-pass prefix unlocking fails for an output-conditioned target. -/
theorem outputConditionedTarget_breaks_prefix_unlock :
    (generatedUpdates
        outputConditionedTarget
        [identityDifferenceLayer]
        0
        0).take 1 ≠
      (generatedUpdates
        outputConditionedTarget
        [identityDifferenceLayer, incrementDifferenceLayer]
        0
        0).take 1 := by
  norm_num
    [generatedUpdates, outputConditionedTarget, propagate, runUpdates,
      ForwardSignalLayer.step, identityDifferenceLayer,
      incrementDifferenceLayer]

/-- Consequently, the output-conditioned generator is not
suffix-independent. -/
theorem outputConditionedTarget_not_suffixIndependent :
    ¬ TargetGeneratorSuffixIndependent outputConditionedTarget := by
  intro h
  have htarget :=
    h [identityDifferenceLayer] [] [incrementDifferenceLayer] 0
  norm_num
    [outputConditionedTarget, propagate, identityDifferenceLayer,
      incrementDifferenceLayer] at htarget

end SignalPropagationForwardUnlock

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
