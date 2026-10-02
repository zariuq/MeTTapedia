import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelSeparation

/-!
# The encoding invents no progress, without restriction and replication

Within the fragment of the pi calculus without restriction and replication,
the encoding of a process reduces only if the process does.

The encoding of such a process is a parallel composition of the encodings of
its outputs and inputs, each on the channel the process names.  If no channel
carries both an output and an input, the channels of the outputs separate
them from the inputs and the encoding has no reduction.  If some channel
carries both, the process itself communicates there.

This reflects the existence of a step.  It does not match the target of the
step of the encoding with the encoding of a reduct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
  (separation separationHead nameCount separation_SC)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation (RestrictionFree)

open private rhoPar_to_two from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

namespace Process

/-- The channels of the outputs beneath parallel compositions only. -/
def offers : Process → List String
  | .par left right => left.offers ++ right.offers
  | .output channel _ => [channel]
  | _ => []

/-- The channels of the inputs beneath parallel compositions only. -/
def awaits : Process → List String
  | .par left right => left.awaits ++ right.awaits
  | .input channel _ _ => [channel]
  | _ => []

end Process

/-! ## The process communicates where an output meets an input -/

/-- An offered channel is the channel of an output that structural congruence
brings to the front. -/
theorem exists_output_front {channel : String} :
    ∀ process : Process, channel ∈ process.offers →
      ∃ (datum : Name) (rest : Process),
        Nonempty (process ≡ Process.par (.output channel datum) rest)
  | .nil, offered => by simp [Process.offers] at offered
  | .par left right, offered => by
      rcases List.mem_append.mp offered with inLeft | inRight
      · obtain ⟨datum, rest, ⟨front⟩⟩ := exists_output_front left inLeft
        exact ⟨datum, .par rest right,
          ⟨.trans _ _ _ (.par_cong _ _ _ _ front (.refl right)) (.par_assoc _ _ _)⟩⟩
      · obtain ⟨datum, rest, ⟨front⟩⟩ := exists_output_front right inRight
        exact ⟨datum, .par rest left,
          ⟨.trans _ _ _ (.par_comm left right)
            (.trans _ _ _ (.par_cong _ _ _ _ front (.refl left)) (.par_assoc _ _ _))⟩⟩
  | .input _ _ _, offered => by simp [Process.offers] at offered
  | .output other datum, offered => by
      obtain rfl : channel = other := List.mem_singleton.mp offered
      exact ⟨datum, .nil, ⟨.symm _ _ (.par_nil_right _)⟩⟩
  | .nu _ _, offered => by simp [Process.offers] at offered
  | .replicate _ _ _, offered => by simp [Process.offers] at offered

/-- An awaited channel is the channel of an input that structural congruence
brings to the front. -/
theorem exists_input_front {channel : String} :
    ∀ process : Process, channel ∈ process.awaits →
      ∃ (bound : Name) (body rest : Process),
        Nonempty (process ≡ Process.par (.input channel bound body) rest)
  | .nil, awaited => by simp [Process.awaits] at awaited
  | .par left right, awaited => by
      rcases List.mem_append.mp awaited with inLeft | inRight
      · obtain ⟨bound, body, rest, ⟨front⟩⟩ := exists_input_front left inLeft
        exact ⟨bound, body, .par rest right,
          ⟨.trans _ _ _ (.par_cong _ _ _ _ front (.refl right)) (.par_assoc _ _ _)⟩⟩
      · obtain ⟨bound, body, rest, ⟨front⟩⟩ := exists_input_front right inRight
        exact ⟨bound, body, .par rest left,
          ⟨.trans _ _ _ (.par_comm left right)
            (.trans _ _ _ (.par_cong _ _ _ _ front (.refl left)) (.par_assoc _ _ _))⟩⟩
  | .input other bound body, awaited => by
      obtain rfl : channel = other := List.mem_singleton.mp awaited
      exact ⟨bound, body, .nil, ⟨.symm _ _ (.par_nil_right _)⟩⟩
  | .output _ _, awaited => by simp [Process.awaits] at awaited
  | .nu _ _, awaited => by simp [Process.awaits] at awaited
  | .replicate _ _ _, awaited => by simp [Process.awaits] at awaited

/-- An input in front on one side and an output in front on the other
communicate. -/
theorem reduces_of_fronts {channel bound datum : Name} {body left right inputRest
    outputRest : Process}
    (inputFront : left ≡ Process.par (.input channel bound body) inputRest)
    (outputFront : right ≡ Process.par (.output channel datum) outputRest) :
    ∃ target : Process, Nonempty (Process.par left right ⇝ target) := by
  refine ⟨.par (body.substitute bound datum) (.par outputRest inputRest), ⟨?_⟩⟩
  refine .struct _ (.par (.par (.input channel bound body) (.output channel datum))
    (.par outputRest inputRest)) _ _ ?_
    (.par_left _ _ _ (.comm channel bound datum body)) (.refl _)
  -- (i | L) | (o | R)  ≡  (i | o) | (R | L)
  refine .trans _ _ _ (.par_cong _ _ _ _ inputFront outputFront) ?_
  refine .trans _ _ _ (.par_assoc _ _ _) ?_
  refine .trans _ _ _
    (.par_cong _ _ _ _ (.refl _) (.par_comm inputRest (.par (.output channel datum) outputRest)))
    ?_
  refine .trans _ _ _ (.par_cong _ _ _ _ (.refl _) (.par_assoc _ _ _)) ?_
  exact .symm _ _ (.par_assoc _ _ _)

/-- **A process with a channel both offered and awaited reduces.** -/
theorem reduces_of_offers_awaits {channel : String} :
    ∀ process : Process, channel ∈ process.offers → channel ∈ process.awaits →
      ∃ target : Process, Nonempty (process ⇝ target)
  | .nil, offered, _ => by simp [Process.offers] at offered
  | .par left right, offered, awaited => by
      rcases List.mem_append.mp offered with outLeft | outRight <;>
        rcases List.mem_append.mp awaited with inLeft | inRight
      · obtain ⟨target, ⟨step⟩⟩ := reduces_of_offers_awaits left outLeft inLeft
        exact ⟨_, ⟨.par_left _ _ right step⟩⟩
      · obtain ⟨datum, outputRest, ⟨outputFront⟩⟩ := exists_output_front left outLeft
        obtain ⟨bound, body, inputRest, ⟨inputFront⟩⟩ := exists_input_front right inRight
        obtain ⟨target, ⟨step⟩⟩ := reduces_of_fronts inputFront outputFront
        exact ⟨target, ⟨.struct _ _ _ _ (.par_comm left right) step (.refl _)⟩⟩
      · obtain ⟨datum, outputRest, ⟨outputFront⟩⟩ := exists_output_front right outRight
        obtain ⟨bound, body, inputRest, ⟨inputFront⟩⟩ := exists_input_front left inLeft
        exact reduces_of_fronts inputFront outputFront
      · obtain ⟨target, ⟨step⟩⟩ := reduces_of_offers_awaits right outRight inRight
        exact ⟨_, ⟨.par_right left _ _ step⟩⟩
  | .input _ _ _, offered, _ => by simp [Process.offers] at offered
  | .output _ _, _, awaited => by simp [Process.awaits] at awaited
  | .nu _ _, offered, _ => by simp [Process.offers] at offered
  | .replicate _ _ _, offered, _ => by simp [Process.offers] at offered

/-! ## The encoding separates outputs from inputs unless they share a channel -/

theorem separation_rhoPar (names : List String) (left right : Pattern) :
    separation names (rhoPar left right) = separation names left + separation names right := by
  rw [separation_SC names (rhoPar_to_two left right)]
  simp [separation]

/-- An input on a channel that is a free name counts when the name is among
the names. -/
theorem separation_input (names : List String) (channel : String) (body : Pattern) :
    separation names (.apply "PInput" [.fvar channel, body]) =
      ([channel].filter (· ∈ names)).length := by
  by_cases member : channel ∈ names <;>
    simp [separation, separationHead, nameCount, member]

/-- An output on a channel that is a free name counts when the name is not
among the names. -/
theorem separation_output (names : List String) (channel : String) (payload : Pattern) :
    separation names (.apply "POutput" [.fvar channel, payload]) =
      ([channel].filter (· ∉ names)).length := by
  by_cases member : channel ∈ names <;>
    simp [separation, separationHead, nameCount, member]

/-- The count of the encoding of a process without restriction and
replication: the outputs on channels outside the names and the inputs on
channels among them. -/
theorem separation_encode_rf (names : List String) :
    ∀ (process : Process), RestrictionFree process → ∀ n v : String,
      separation names (encode process n v) =
        (process.offers.filter (· ∉ names)).length +
          (process.awaits.filter (· ∈ names)).length
  | .nil, _, _, _ => by
      have unfolded : ∀ n v : String, encode .nil n v = .collection .hashBag [] none :=
        fun _ _ => rfl
      rw [unfolded]
      simp [separation, Process.offers, Process.awaits]
  | .par left right, free, n, v => by
      rw [encode, separation_rhoPar, separation_encode_rf names left free.1,
        separation_encode_rf names right free.2]
      simp only [Process.offers, Process.awaits, List.filter_append, List.length_append]
      omega
  | .input channel bound body, _, n, v => by
      have unfolded : encode (.input channel bound body) n v =
          .apply "PInput"
            [.fvar channel,
              .lambda none
                (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 bound (encode body n v))] :=
        rfl
      rw [unfolded, separation_input names channel]
      simp [Process.offers, Process.awaits]
  | .output channel datum, _, n, v => by
      have unfolded : encode (.output channel datum) n v =
          .apply "POutput" [.fvar channel, .apply "PDrop" [.fvar datum]] := rfl
      rw [unfolded, separation_output names channel]
      simp [Process.offers, Process.awaits]
  | .nu _ _, free, _, _ => absurd free id
  | .replicate _ _ _, free, _, _ => absurd free id

/-- **The encoding invents no progress.**  If the encoding of a process
without restriction and replication reduces, the process reduces. -/
theorem reduces_of_encode_reduces_rf {process : Process} (free : RestrictionFree process)
    {n v : String} {reached : Pattern}
    (step : Nonempty (RhoCalculus.Reduction.Reduces (encode process n v) reached)) :
    ∃ target : Process, Nonempty (process ⇝ target) := by
  by_cases shared : ∃ channel ∈ process.offers, channel ∈ process.awaits
  · obtain ⟨channel, offered, awaited⟩ := shared
    exact reduces_of_offers_awaits process offered awaited
  · exfalso
    obtain ⟨reduction⟩ := step
    have positive := RhoCalculus.Reduction.separation_pos_of_reduces process.offers reduction
    rw [separation_encode_rf process.offers process free n v] at positive
    have noOffer : process.offers.filter (· ∉ process.offers) = [] :=
      List.filter_eq_nil_iff.mpr fun channel member => by simpa using member
    have noAwait : process.awaits.filter (· ∈ process.offers) = [] :=
      List.filter_eq_nil_iff.mpr fun channel member => by
        simpa using fun offered => shared ⟨channel, offered, member⟩
    rw [noOffer, noAwait] at positive
    simp at positive

end Mettapedia.Languages.ProcessCalculi.PiCalculus
