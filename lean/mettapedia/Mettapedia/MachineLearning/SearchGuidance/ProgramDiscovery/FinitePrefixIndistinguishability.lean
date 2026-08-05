import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CostAwareOpportunityControl

/-!
# Finite prefixes do not identify limiting behaviour

Two impossibility results about deciding from finite observations.  First, a
general lemma: if two worlds expose the same observation but require opposite
answers, no deterministic decision rule on that observation is correct in
both.  Second, its yield-curve instance: every finite observed yield prefix
has both an eventually-zero continuation and a continuation with positive
yield forever, so no classifier of the prefix decides eventual vanishing.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace AdaptivePortfolio

/-! ## An observation-only impossibility theorem -/

/-- If two worlds expose the same observation but require opposite answers,
no deterministic decision rule on that observation can be correct in both. -/
theorem no_observationOnly_rule_correct_on_opposite_worlds
    {World Observation : Type*}
    (observe : World → Observation) (correctAnswer : World → Prop)
    {positiveWorld negativeWorld : World}
    (sameObservation :
      observe positiveWorld = observe negativeWorld)
    (positiveAnswer : correctAnswer positiveWorld)
    (negativeAnswer : ¬ correctAnswer negativeWorld)
    (decision : Observation → Bool) :
    ¬ ((decision (observe positiveWorld) = true ↔
          correctAnswer positiveWorld) ∧
        (decision (observe negativeWorld) = true ↔
          correctAnswer negativeWorld)) := by
  rintro ⟨correctPositive, correctNegative⟩
  have chosePositive :
      decision (observe positiveWorld) = true :=
    correctPositive.mpr positiveAnswer
  have choseNegative :
      decision (observe negativeWorld) = true := by
    rwa [← sameObservation]
  exact negativeAnswer (correctNegative.mp choseNegative)


/-! ## A finite horizon cannot identify saturation -/

/-- The values visible through a finite generation horizon. -/
def yieldPrefix (horizon : ℕ) (yield : ℕ → ℕ) :
    Fin (horizon + 1) → ℕ :=
  fun generation ↦ yield generation

/-- Continue an observed yield curve by reporting no discoveries after the
declared horizon. -/
def zeroTail (observed : ℕ → ℕ) (horizon : ℕ) : ℕ → ℕ :=
  fun generation ↦ if generation ≤ horizon then observed generation else 0

/-- Continue the same observed yield curve by reporting one discovery in every
later generation. -/
def oneTail (observed : ℕ → ℕ) (horizon : ℕ) : ℕ → ℕ :=
  fun generation ↦ if generation ≤ horizon then observed generation else 1

/-- A yield curve saturates in the narrow count sense when all sufficiently
late generation increments are zero. -/
def EventuallyZeroYield (yield : ℕ → ℕ) : Prop :=
  ∃ threshold, ∀ generation, threshold ≤ generation → yield generation = 0

/-- The two continuations are observationally identical at every generation
inside the declared horizon. -/
theorem zeroTail_oneTail_samePrefix
    (observed : ℕ → ℕ) (horizon : ℕ) :
    yieldPrefix horizon (zeroTail observed horizon) =
      yieldPrefix horizon (oneTail observed horizon) := by
  funext generation
  have visible : generation.val ≤ horizon := by omega
  simp [yieldPrefix, zeroTail, oneTail, visible]

/-- The zero continuation really is eventually zero. -/
theorem zeroTail_eventuallyZero
    (observed : ℕ → ℕ) (horizon : ℕ) :
    EventuallyZeroYield (zeroTail observed horizon) := by
  refine ⟨horizon + 1, ?_⟩
  intro generation late
  have outside : ¬ generation ≤ horizon := by omega
  simp [zeroTail, outside]

/-- The positive continuation never becomes eventually zero. -/
theorem oneTail_not_eventuallyZero
    (observed : ℕ → ℕ) (horizon : ℕ) :
    ¬ EventuallyZeroYield (oneTail observed horizon) := by
  rintro ⟨threshold, lateZero⟩
  let generation := max threshold (horizon + 1)
  have threshold_le : threshold ≤ generation := Nat.le_max_left _ _
  have outside : ¬ generation ≤ horizon := by
    dsimp [generation]
    omega
  have claimedZero := lateZero generation threshold_le
  simp [oneTail, outside] at claimedZero

/-- No deterministic classifier seeing only a finite yield prefix can be
correct on both the zero-tail and positive-tail continuations.  Consequently,
observed decline through a finite terminal generation is not by itself a
saturation proof. -/
theorem not_correct_on_zeroTail_and_oneTail
    (observed : ℕ → ℕ) (horizon : ℕ)
    (decision : (Fin (horizon + 1) → ℕ) → Bool) :
    ¬ ((decision (yieldPrefix horizon (zeroTail observed horizon)) = true ↔
          EventuallyZeroYield (zeroTail observed horizon)) ∧
        (decision (yieldPrefix horizon (oneTail observed horizon)) = true ↔
          EventuallyZeroYield (oneTail observed horizon))) := by
  rintro ⟨correctZero, correctOne⟩
  have choosesZero :
      decision (yieldPrefix horizon (zeroTail observed horizon)) = true :=
    correctZero.mpr (zeroTail_eventuallyZero observed horizon)
  have choosesOne :
      decision (yieldPrefix horizon (oneTail observed horizon)) = true := by
    rw [← zeroTail_oneTail_samePrefix observed horizon]
    exact choosesZero
  exact oneTail_not_eventuallyZero observed horizon (correctOne.mp choosesOne)

section Examples

/-- A concrete declining observed prefix. -/
def observed : ℕ → ℕ
  | 0 => 5
  | 1 => 3
  | _ => 2

/-- Both continuations reproduce the concrete observations through generation
two, although exactly one saturates afterwards. -/
theorem decliningPrefix_opposite_tails :
    yieldPrefix 2 (zeroTail observed 2) =
        yieldPrefix 2 (oneTail observed 2) ∧
      EventuallyZeroYield (zeroTail observed 2) ∧
      ¬ EventuallyZeroYield (oneTail observed 2) := by
  exact ⟨zeroTail_oneTail_samePrefix observed 2,
    zeroTail_eventuallyZero observed 2,
    oneTail_not_eventuallyZero observed 2⟩

end Examples


#print axioms no_observationOnly_rule_correct_on_opposite_worlds
#print axioms zeroTail_oneTail_samePrefix
#print axioms zeroTail_eventuallyZero
#print axioms oneTail_not_eventuallyZero
#print axioms not_correct_on_zeroTail_and_oneTail
#print axioms decliningPrefix_opposite_tails

end AdaptivePortfolio

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
