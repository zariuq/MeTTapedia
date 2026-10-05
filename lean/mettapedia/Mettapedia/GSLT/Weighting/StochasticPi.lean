import Mettapedia.GSLT.Weighting.WeightTheory
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Conservativity over summation-free stochastic π

A summation-free π process at top level is a bag of input and output prefixes.
Its communication redexes are selections: one copy of an input on a channel and
one copy of an output on the same channel, any payload. With one key per
channel, static weights and free addressing, the propensity of channel `x` is
its weight times the number of inputs on `x` times the number of outputs on
`x`. This is the activity of the Stochastic Pi Machine on the summation-free
fragment: inputs times outputs, the correction for mixed summations being empty
without summation, and the copies counted.

Keys that read the payload price two outputs on one channel differently, so two
bags with the same counts on every channel can have different propensities.
Updates of the weights make the rate depend on the history
(`DynamicWeights.no_term_rate`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.StochasticPi

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

/-- A top-level prefix: an input on a channel, or an output of a payload on a
channel. Continuations are left out; they do not change the activity of the
current bag. -/
inductive Prefix (C V : Type) where
  | input (channel : C)
  | output (channel : C) (payload : V)
  deriving DecidableEq

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- The bag left after a communication on a channel with a payload. -/
def afterComm (soup : Multiset (Prefix C V)) (channel : C) (payload : V) :
    Multiset (Prefix C V) :=
  soup - {.input channel, .output channel payload}

variable (C V) in
/-- Communication on a bag of prefixes. -/
def soupTheory : GSLT where
  Term := Multiset (Prefix C V)
  equations := ⟨Eq, eq_equivalence⟩
  rewrites soup next := ∃ channel payload, Prefix.input channel ∈ soup ∧
    Prefix.output channel payload ∈ soup ∧ next = afterComm soup channel payload
  rewrites_resp_left := by
    intro soup soup' next equal step
    exact ⟨next, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro soup next next' step equal
    exact equal ▸ step

/-- A communication redex: a channel, a payload, a copy of an input on the
channel and a copy of the output. -/
abbrev Selection (soup : Multiset (Prefix C V)) :=
  Σ (channel : C) (payload : V),
    Fin (soup.count (.input channel)) × Fin (soup.count (.output channel payload))

variable (C V) in
/-- The redexes of the communication rule, counted as selections from the bag. -/
def presentation : InteractionPresentation (soupTheory C V) where
  Site := Unit
  Event _ soup next := {selection : Selection soup //
    next = afterComm soup selection.1 selection.2.1}
  sound := by
    rintro _ soup next ⟨⟨channel, payload, inputCopy, outputCopy⟩, rfl⟩
    exact ⟨channel, payload, Multiset.count_pos.mp (Fin.pos inputCopy),
      Multiset.count_pos.mp (Fin.pos outputCopy), rfl⟩

/-- The enabled redexes of a bag are its selections. -/
def enabledEquiv (soup : Multiset (Prefix C V)) :
    (presentation C V).Enabled soup ≃ Selection soup where
  toFun redex := redex.evidence.val
  invFun selection := ⟨(), afterComm soup selection.1 selection.2.1, ⟨selection, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟩, next, ⟨selection, rfl⟩⟩
    rfl
  right_inv _ := rfl

variable [Fintype C] [Fintype V]

instance instFintypeEnabled (soup : (soupTheory C V).Term) :
    Fintype ((presentation C V).Enabled soup) :=
  Fintype.ofEquiv _ (enabledEquiv soup).symm

/-- The number of outputs on a channel, any payload. -/
def outputs (soup : Multiset (Prefix C V)) (channel : C) : ℕ :=
  ∑ payload : V, soup.count (.output channel payload)

/-- The activity of a channel in the summation-free fragment of the Stochastic
Pi Machine: inputs on the channel times outputs on it. -/
def activity (soup : Multiset (Prefix C V)) (channel : C) : ℕ :=
  soup.count (.input channel) * outputs soup channel

/-! ## Channel keys -/

variable (C V) in
/-- One key per channel: the communication happens on that channel. -/
def channelKeys : Keyed (presentation C V) where
  Key _ := C
  classify event := event.val.1

instance : DecidableEq (Σ rule : (presentation C V).Site, (channelKeys C V).Key rule) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, C))

variable (C V) in
/-- Static weights from rates per channel, no updates, free addressing. -/
def channelRates (rate : C → ℝ) : Augmented (channelKeys C V) ℝ where
  initial key := rate key.2
  update _ map := map
  Context := PEmpty.{1}
  address _ := []
  geometric _ := 1
  fold _ map := map

/-- The redexes of a channel are its selections on that channel. -/
theorem card_channel_redexes (soup : (soupTheory C V).Term) (channel : C) :
    (Finset.univ.filter fun redex : (presentation C V).Enabled soup =>
        Augmented.keyOf (K := channelKeys C V) redex.evidence = ⟨(), channel⟩).card =
      activity soup channel := by
  rw [← Finset.card_map (enabledEquiv soup).toEmbedding]
  have image : (Finset.univ.filter fun redex : (presentation C V).Enabled soup =>
        Augmented.keyOf (K := channelKeys C V) redex.evidence = ⟨(), channel⟩).map
        (enabledEquiv soup).toEmbedding =
      Finset.univ.filter fun selection : Selection soup => selection.1 = channel := by
    ext selection
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro same
      have := congrArg Sigma.snd same
      simpa [Augmented.keyOf, channelKeys, enabledEquiv] using this
    · intro same
      simp [Augmented.keyOf, channelKeys, enabledEquiv, same]
  rw [image, Finset.card_filter, Fintype.sum_sigma, Finset.sum_eq_single channel]
  · simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, activity, outputs, Finset.mul_sum]
  · intro other _ different
    simp [different]
  · intro absent
    exact absurd (Finset.mem_univ channel) absent

/-- **Conservativity over summation-free stochastic π.** With one key per
channel, static weights, free addressing and every redex funded, the propensity
of a channel is its rate times its activity. -/
theorem propensity_eq_activity (rate : C → ℝ) (soup : (soupTheory C V).Term) (channel : C) :
    (channelRates C V rate).propensity (fun _ => True) (channelRates C V rate).initial soup
        ⟨(), channel⟩ =
      rate channel * activity soup channel := by
  unfold Augmented.propensity
  congr 1
  rw [← card_channel_redexes soup channel, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun redex _ => ?_
  simp [Augmented.geometricFactor, Augmented.gate, channelRates]

/-! ## Keys that read the payload -/

variable (C V) in
/-- One key per channel and payload. -/
def payloadKeys : Keyed (presentation C V) where
  Key _ := C × V
  classify event := (event.val.1, event.val.2.1)

instance : DecidableEq (Σ rule : (presentation C V).Site, (payloadKeys C V).Key rule) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, C × V))

variable (C V) in
/-- Static weights per channel and payload. -/
def payloadRates (rate : C × V → ℝ) : Augmented (payloadKeys C V) ℝ where
  initial key := rate key.2
  update _ map := map
  Context := PEmpty.{1}
  address _ := []
  geometric _ := 1
  fold _ map := map

/-- The redexes of a channel and payload: the inputs on the channel times the
outputs of that payload on it. -/
theorem card_payload_redexes (soup : (soupTheory C V).Term) (channel : C) (payload : V) :
    (Finset.univ.filter fun redex : (presentation C V).Enabled soup =>
        Augmented.keyOf (K := payloadKeys C V) redex.evidence = ⟨(), (channel, payload)⟩).card =
      soup.count (.input channel) * soup.count (.output channel payload) := by
  rw [← Finset.card_map (enabledEquiv soup).toEmbedding]
  have image : (Finset.univ.filter fun redex : (presentation C V).Enabled soup =>
        Augmented.keyOf (K := payloadKeys C V) redex.evidence = ⟨(), (channel, payload)⟩).map
        (enabledEquiv soup).toEmbedding =
      Finset.univ.filter fun selection : Selection soup =>
        selection.1 = channel ∧ selection.2.1 = payload := by
    ext selection
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro same
      have := congrArg Sigma.snd same
      simpa [Augmented.keyOf, payloadKeys, enabledEquiv] using this
    · rintro ⟨sameChannel, samePayload⟩
      simp [Augmented.keyOf, payloadKeys, enabledEquiv, sameChannel, samePayload]
  rw [image, Finset.card_filter, Fintype.sum_sigma, Finset.sum_eq_single channel]
  · rw [Fintype.sum_sigma, Finset.sum_eq_single payload]
    · simp
    · intro other _ different
      simp [different]
    · intro absent
      exact absurd (Finset.mem_univ payload) absent
  · intro other _ different
    simp [different]
  · intro absent
    exact absurd (Finset.mem_univ channel) absent

/-- With payload keys the propensity of a channel and payload is its rate times
the inputs on the channel times the outputs of that payload. -/
theorem payload_propensity (rate : C × V → ℝ) (soup : (soupTheory C V).Term) (channel : C)
    (payload : V) :
    (payloadRates C V rate).propensity (fun _ => True) (payloadRates C V rate).initial soup
        ⟨(), (channel, payload)⟩ =
      rate (channel, payload) *
        (soup.count (.input channel) * soup.count (.output channel payload) : ℕ) := by
  unfold Augmented.propensity
  congr 1
  rw [← card_payload_redexes soup channel payload, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_one]
  refine Finset.sum_congr rfl fun redex _ => ?_
  simp [Augmented.geometricFactor, Augmented.gate, payloadRates]

end Mettapedia.GSLT.Weighting.StochasticPi

namespace Mettapedia.GSLT.Weighting.StochasticPi.Strictness

open Mettapedia.GSLT.Weighting.StochasticPi

/-- An input and an output of `false` on the one channel. -/
def withFalse : (soupTheory Unit Bool).Term :=
  ({Prefix.input (), Prefix.output () false} : Multiset (Prefix Unit Bool))

/-- An input and an output of `true` on the one channel. -/
def withTrue : (soupTheory Unit Bool).Term :=
  ({Prefix.input (), Prefix.output () true} : Multiset (Prefix Unit Bool))

/-- Both bags have the same activity on every channel. -/
theorem same_activity : activity withFalse () = activity withTrue () := by
  decide

/-- **Payload keys see what channel keys cannot**: with the output of `false`
priced at one and of `true` at two, the two bags have different propensities,
though every channel has the same activity in both. -/
theorem payload_keys_strict :
    let rate : Unit × Bool → ℝ := fun key => if key.2 then 2 else 1
    (payloadRates Unit Bool rate).propensity (fun _ => True) (payloadRates Unit Bool rate).initial
        withFalse ⟨(), ((), false)⟩ +
      (payloadRates Unit Bool rate).propensity (fun _ => True) (payloadRates Unit Bool rate).initial
        withFalse ⟨(), ((), true)⟩ ≠
    (payloadRates Unit Bool rate).propensity (fun _ => True) (payloadRates Unit Bool rate).initial
        withTrue ⟨(), ((), false)⟩ +
      (payloadRates Unit Bool rate).propensity (fun _ => True) (payloadRates Unit Bool rate).initial
        withTrue ⟨(), ((), true)⟩ := by
  intro rate
  simp only [payload_propensity]
  have countsFalse : withFalse.count (.input ()) * withFalse.count (.output () false) = 1 ∧
      withFalse.count (.input ()) * withFalse.count (.output () true) = 0 := by decide
  have countsTrue : withTrue.count (.input ()) * withTrue.count (.output () false) = 0 ∧
      withTrue.count (.input ()) * withTrue.count (.output () true) = 1 := by decide
  rw [countsFalse.1, countsFalse.2, countsTrue.1, countsTrue.2]
  norm_num [rate]

end Mettapedia.GSLT.Weighting.StochasticPi.Strictness
