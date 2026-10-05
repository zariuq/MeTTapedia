import Mettapedia.GSLT.Weighting.WeightTheory
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls
import Mathlib.Tactic.NormNum

/-!
# Dynamic weights are a property of configurations

Two channels, `a` and `b`. Communication on `a` adds one to the weight of `a`.
Communication on `b` doubles it. The two updates do not commute. A term offers
one redex on each channel; firing both, in either order, reaches the same term,
which offers one more redex on `a`. From weight one, firing `a` first leaves
weight `(1 + 1) · 2 = 4`, firing `b` first leaves `1 · 2 + 1 = 3`. So the same
term is reached with two maps, and the rate of its redex is four or three: no
rate that is a function of the term alone gives both.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.DynamicWeights

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

/-- The two channels. -/
inductive Channel where
  | a
  | b
  deriving DecidableEq

/-- The steps on each channel, between five states: from `0` both channels are
offered; after both have fired the state `3` offers one more `a`. -/
def onChannel : Channel → Fin 5 → Fin 5 → Prop
  | .a, source, target => (source.val, target.val) ∈ [(0, 1), (2, 3), (3, 4)]
  | .b, source, target => (source.val, target.val) ∈ [(0, 2), (1, 3)]

def stateTheory : GSLT where
  Term := Fin 5
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := ∃ channel, onChannel channel source target
  rewrites_resp_left := by
    intro source source' target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    exact equal ▸ step

def presentation : InteractionPresentation stateTheory where
  Site := Channel
  Event channel source target := PLift (onChannel channel source target)
  sound evidence := ⟨_, evidence.down⟩

/-- One key per channel: the channel itself. -/
def keys : Keyed presentation where
  Key _ := Unit
  classify _ := ()

instance : DecidableEq (Σ rule : presentation.Site, keys.Key rule) :=
  inferInstanceAs (DecidableEq (Σ _ : Channel, Unit))

/-- The key of channel `a`. -/
def aKey : Σ channel, keys.Key channel := ⟨.a, ()⟩

/-- Communication on `a` adds one to the weight of `a`; on `b` it doubles it. -/
def augmented : Augmented keys ℚ where
  initial _ := 1
  update key map :=
    match key.1 with
    | .a => Function.update map aKey (map aKey + 1)
    | .b => Function.update map aKey (2 * map aKey)
  Context := PEmpty.{1}
  address _ := []
  geometric _ := 1
  fold _ map := map

def state (n : Fin 5) : stateTheory.Term := n

def a01 : presentation.Event .a (state 0) (state 1) := ⟨show ((0 : ℕ), (1 : ℕ)) ∈ _ by decide⟩
def b13 : presentation.Event .b (state 1) (state 3) := ⟨show ((1 : ℕ), (3 : ℕ)) ∈ _ by decide⟩
def b02 : presentation.Event .b (state 0) (state 2) := ⟨show ((0 : ℕ), (2 : ℕ)) ∈ _ by decide⟩
def a23 : presentation.Event .a (state 2) (state 3) := ⟨show ((2 : ℕ), (3 : ℕ)) ∈ _ by decide⟩
def a34 : presentation.Event .a (state 3) (state 4) := ⟨show ((3 : ℕ), (4 : ℕ)) ∈ _ by decide⟩

/-- The map after firing `a` then `b`. -/
def aThenB : WeightMap keys ℚ := augmented.next b13 (augmented.next a01 augmented.initial)

/-- The map after firing `b` then `a`. -/
def bThenA : WeightMap keys ℚ := augmented.next a23 (augmented.next b02 augmented.initial)

theorem aThenB_a : aThenB aKey = 4 := by
  simp [aThenB, Augmented.next, Augmented.keyOf, augmented, aKey]
  norm_num

theorem bThenA_a : bThenA aKey = 3 := by
  simp [bThenA, Augmented.next, Augmented.keyOf, augmented, aKey]
  norm_num

/-- The redex on `a` offered by the state both orders reach. -/
def lastRedex : presentation.Enabled (state 3) := ⟨.a, state 4, a34⟩

/-- **Two orders, one term, two rates.** Both orders reach the same term in the
weighted theory, and the redex it offers weighs four after one order and three
after the other. -/
theorem same_term_two_rates :
    augmented.weightedTheory.MultiStep (state 0, augmented.initial) (state 3, aThenB) ∧
      augmented.weightedTheory.MultiStep (state 0, augmented.initial) (state 3, bThenA) ∧
      augmented.redexWeight (fun _ => True) aThenB lastRedex = 4 ∧
      augmented.redexWeight (fun _ => True) bThenA lastRedex = 3 := by
  refine ⟨.step (augmented.step_of_event a01 _) (.step (augmented.step_of_event b13 _) (.refl _)),
    .step (augmented.step_of_event b02 _) (.step (augmented.step_of_event a23 _) (.refl _)),
    ?_, ?_⟩
  · simp only [Augmented.redexWeight, Augmented.gate, if_pos trivial, mul_one]
    change aThenB aKey * 1 = 4
    rw [mul_one, aThenB_a]
  · simp only [Augmented.redexWeight, Augmented.gate, if_pos trivial, mul_one]
    change bThenA aKey * 1 = 3
    rw [mul_one, bThenA_a]

/-- **No rate is a function of the term alone**: the rate of the redex at the
reached term depends on the map. -/
theorem no_term_rate :
    ¬ ∃ rate : stateTheory.Term → ℚ, ∀ map : WeightMap keys ℚ,
      augmented.weightedTheory.MultiStep (state 0, augmented.initial) (state 3, map) →
        augmented.redexWeight (fun _ => True) map lastRedex = rate (state 3) := by
  rintro ⟨rate, determined⟩
  obtain ⟨reachAB, reachBA, weightAB, weightBA⟩ := same_term_two_rates
  have four := (determined _ reachAB).symm.trans weightAB
  have three := (determined _ reachBA).symm.trans weightBA
  rw [four] at three
  norm_num at three

/-! ## The shared handler retains the dynamic map -/

open Mettapedia.GSLT.Dynamics

/-- The final redex is the sole supplied occurrence in this local observation. -/
def lastCatalogue (source : stateTheory.Term) : List (presentation.Enabled source) := by
  letI : DecidableEq stateTheory.Term := inferInstanceAs (DecidableEq (Fin 5))
  exact if equal : source = state 3 then equal.symm ▸ [lastRedex] else []

/-- The existing two rates remain distinct after interpretation through the
common weighted resumption handler. -/
theorem common_handler_two_rates :
    WeightedResumption.total
        (WeightedResumption.interpret
          (augmented.responses (fun _ => True) lastCatalogue)
          (augmented.stepComputation (state 3, aThenB))) = 4 ∧
      WeightedResumption.total
        (WeightedResumption.interpret
          (augmented.responses (fun _ => True) lastCatalogue)
          (augmented.stepComputation (state 3, bThenA))) = 3 := by
  obtain ⟨_, _, four, three⟩ := same_term_two_rates
  constructor
  · rw [augmented.interpret_step (fun _ => True) lastCatalogue]
    simpa [lastCatalogue, WeightedResumption.total, SemiringTraversal.weightSum] using four
  · rw [augmented.interpret_step (fun _ => True) lastCatalogue]
    simpa [lastCatalogue, WeightedResumption.total, SemiringTraversal.weightSum] using three

end Mettapedia.GSLT.Weighting.DynamicWeights

namespace Mettapedia.GSLT.Weighting.ResumptionControls

open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics

/-- Reuse the two distinct sites with the same endpoint from InteractionEvent. -/
def loopKeys : Keyed Canary.loopPresentation where
  Key _ := Unit
  classify _ := ()

def loopCatalogue (source : Canary.loopTheory.Term) :
    List (Canary.loopPresentation.Enabled source) :=
  [⟨.cheap, (), ()⟩, ⟨.dear, (), ()⟩]

def oppositeWeights : WeightMap loopKeys ℤ := fun key =>
  match key.1 with
  | .cheap => 1
  | .dear => -1

def loopState : Canary.loopTheory.Term := ()

/-- Both supplied occurrences are real and distinct despite equal endpoints. -/
theorem loop_occurrences_distinct :
    Canary.cheapEvent.target = Canary.dearEvent.target ∧
      Canary.cheapEvent ≠ Canary.dearEvent := by
  refine ⟨rfl, ?_⟩
  intro equal
  have sites := congrArg InteractionPresentation.Enabled.site equal
  cases sites

/-- Cancellation in the shared handler retains both occurrence contributions. -/
theorem cancelling_events_remain :
    let answers := WeightedResumption.interpret
      ((uniform loopKeys ℤ).responses (fun _ => True) loopCatalogue)
      ((uniform loopKeys ℤ).stepComputation (loopState, oppositeWeights))
    WeightedResumption.total answers = 0 ∧ answers.length = 2 := by
  dsimp only
  simp [Augmented.stepComputation, WeightedResumption.interpret_perform,
    WeightedResumption.interpret_pure, WeightedResumption.sequence, Augmented.responses,
    loopCatalogue, oppositeWeights, Augmented.redexWeight, Augmented.keyOf,
    Augmented.geometricFactor, Augmented.gate, Augmented.successor, uniform,
    WeightedResumption.total, SemiringTraversal.weightSum]

/-- A zero funding coefficient retains the same two events in attachment. -/
theorem unfunded_events_remain :
    let answers := WeightedResumption.interpret
      ((uniform loopKeys ℤ).responses (fun _ => False) loopCatalogue)
      ((uniform loopKeys ℤ).stepComputation (loopState, oppositeWeights))
    WeightedResumption.total answers = 0 ∧ answers.length = 2 := by
  dsimp only
  simp [Augmented.stepComputation, WeightedResumption.interpret_perform,
    WeightedResumption.interpret_pure, WeightedResumption.sequence, Augmented.responses,
    loopCatalogue, Augmented.redexWeight, Augmented.gate,
    WeightedResumption.total, SemiringTraversal.weightSum]

/-- Uniform positive coefficients count both physical event occurrences. -/
theorem uniform_events_counted :
    WeightedResumption.total
      (WeightedResumption.interpret
        ((uniform loopKeys ℤ).responses (fun _ => True) loopCatalogue)
        ((uniform loopKeys ℤ).stepComputation (loopState, (uniform loopKeys ℤ).initial))) = 2 := by
  simp [Augmented.stepComputation, WeightedResumption.interpret_perform,
    WeightedResumption.interpret_pure, WeightedResumption.sequence, Augmented.responses,
    loopCatalogue, Augmented.redexWeight,
    Augmented.geometricFactor, Augmented.gate, uniform,
    WeightedResumption.total, SemiringTraversal.weightSum]

open WeightedResumptionControls (TwoByTwo upper lower)

/-- Two actual address orders of the existing two-site presentation. -/
def orderedContexts : Augmented loopKeys TwoByTwo where
  initial _ := 1
  update _ map := map
  Context := Bool
  address := fun {rule} {_source} {_target} _ => match rule with
    | .cheap => [false, true]
    | .dear => [true, false]
  geometric := fun context => if context then lower else upper
  fold _ map := map

def siteCatalogue (site : Canary.LoopSite) (source : Canary.loopTheory.Term) :
    List (Canary.loopPresentation.Enabled source) :=
  [⟨site, (), ()⟩]

/-- The common handler preserves address order for matrix coefficients.
Reversing that order changes the readout even with the same term endpoints. -/
theorem context_order_changes_matrix_readout :
    WeightedResumption.total
      (WeightedResumption.interpret
        (orderedContexts.responses (fun _ => True) (siteCatalogue .cheap))
        (orderedContexts.stepComputation (loopState, orderedContexts.initial))) ≠
      WeightedResumption.total
        (WeightedResumption.interpret
          (orderedContexts.responses (fun _ => True) (siteCatalogue .dear))
          (orderedContexts.stepComputation (loopState, orderedContexts.initial))) := by
  simpa [Augmented.stepComputation, WeightedResumption.interpret_perform,
    WeightedResumption.interpret_pure, WeightedResumption.sequence, Augmented.responses,
    siteCatalogue, Augmented.redexWeight, Augmented.geometricFactor, Augmented.gate,
    orderedContexts, WeightedResumption.total, SemiringTraversal.weightSum] using
    WeightedResumptionControls.matrix_composition_is_ordered

end Mettapedia.GSLT.Weighting.ResumptionControls
