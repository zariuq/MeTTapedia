import Mettapedia.Hyperseed.Ultrainfinitism

/-!
# Hyperseed Ultrainfinitism Regression

Positive examples:

- `city` is observable through an admitted signal,
- `city` lies in the near eurycosm at budget `1`,
- expanding the signal class preserves observability.

Negative examples:

- `hidden` is not observable from the grounded perspective,
- `forest` is outside the near eurycosm at budget `1`.
-/

namespace Mettapedia.Hyperseed.UltrainfinitismRegression

open Mettapedia.Hyperseed

inductive ToyWorld where
  | city
  | forest
  | hidden
  deriving DecidableEq

inductive ToySignal where
  | sight
  | radio
  | mythic
  deriving DecidableEq

inductive ToyEvent where
  | surprise
  deriving DecidableEq

inductive ToyAction where
  | probe
  deriving DecidableEq

/-- Grounded perspective: ordinary signals, finite budget, and no access to the
hidden world. -/
def groundedPerspective : Perspective ToyWorld ToySignal ℕ where
  signalClass := {ToySignal.sight, ToySignal.radio}
  reaches s x :=
    match s, x with
    | .sight, .city => True
    | .radio, .city => True
    | .radio, .forest => True
    | _, _ => False
  effort x :=
    match x with
    | .city => 1
    | .forest => 2
    | .hidden => 5

/-- Expanded perspective: same reachability, but with an additional signal class
that reaches the hidden world. -/
def expandedPerspective : Perspective ToyWorld ToySignal ℕ where
  signalClass := {ToySignal.sight, ToySignal.radio, ToySignal.mythic}
  reaches s x :=
    match s, x with
    | .sight, .city => True
    | .radio, .city => True
    | .radio, .forest => True
    | .mythic, .hidden => True
    | _, _ => False
  effort := groundedPerspective.effort

/-- A narrow credibility/guard region for the grounded perspective. -/
def groundedGuard : Set ToyWorld := {ToyWorld.city}

theorem city_mem_observableUniverse_grounded :
    ToyWorld.city ∈ observableUniverse groundedPerspective := by
  exact ⟨ToySignal.sight, by simp [groundedPerspective], by simp [groundedPerspective]⟩

theorem hidden_not_mem_observableUniverse_grounded :
    ToyWorld.hidden ∉ observableUniverse groundedPerspective := by
  intro h
  rcases h with ⟨s, hs, hreach⟩
  cases s <;> simp [groundedPerspective] at hs hreach

theorem city_mem_nearEurycosm_grounded_budget1 :
    ToyWorld.city ∈ nearEurycosm groundedPerspective 1 := by
  show groundedPerspective.effort ToyWorld.city ≤ 1
  simp [groundedPerspective]

theorem forest_not_mem_nearEurycosm_grounded_budget1 :
    ToyWorld.forest ∉ nearEurycosm groundedPerspective 1 := by
  intro h
  simp [nearEurycosm, sublevelRegion, groundedPerspective] at h

theorem city_mem_nearEurycosm_grounded_budget5 :
    ToyWorld.city ∈ nearEurycosm groundedPerspective 5 := by
  show groundedPerspective.effort ToyWorld.city ≤ 5
  simp [groundedPerspective]

theorem hidden_mem_observableUniverse_expanded :
    ToyWorld.hidden ∈ observableUniverse expandedPerspective := by
  exact ⟨ToySignal.mythic, by simp [expandedPerspective], by simp [expandedPerspective]⟩

theorem city_mem_availableRegion_grounded :
    ToyWorld.city ∈ availableRegion groundedPerspective 1 groundedGuard := by
  simp [availableRegion, groundedGuard, city_mem_observableUniverse_grounded,
    city_mem_nearEurycosm_grounded_budget1]

theorem forest_not_mem_availableRegion_grounded :
    ToyWorld.forest ∉ availableRegion groundedPerspective 1 groundedGuard := by
  simp [availableRegion, groundedGuard, forest_not_mem_nearEurycosm_grounded_budget1]

theorem observableUniverse_grounded_subset_expanded :
    observableUniverse groundedPerspective ⊆ observableUniverse expandedPerspective := by
  refine observableUniverse_mono_of_signalClass_subset ?_ ?_
  · intro s hs
    cases s <;> simp [groundedPerspective, expandedPerspective] at hs ⊢
  · intro s x h
    cases s <;> cases x <;> simp [groundedPerspective, expandedPerspective] at h ⊢

theorem nearEurycosm_grounded_budget1_subset_budget2 :
    nearEurycosm groundedPerspective 1 ⊆ nearEurycosm groundedPerspective 2 := by
  exact nearEurycosm_mono groundedPerspective (show 1 ≤ 2 by decide)

/-- A stage filtration of the same infinite-style world space: stage `n` contains
exactly the worlds whose effort is at most `n + 1`. -/
def toyStageView : StagedView (World := ToyWorld) ℕ where
  region n := { x | groundedPerspective.effort x ≤ n + 1 }
  mono := by
    intro i j hij x hx
    exact le_trans hx (Nat.add_le_add_right hij 1)

theorem city_mem_toyStageView_0 :
    ToyWorld.city ∈ toyStageView.region 0 := by
  simp [toyStageView, groundedPerspective]

theorem hidden_not_mem_toyStageView_1 :
    ToyWorld.hidden ∉ toyStageView.region 1 := by
  simp [toyStageView, groundedPerspective]

theorem hidden_mem_toyStageView_4 :
    ToyWorld.hidden ∈ toyStageView.region 4 := by
  simp [toyStageView, groundedPerspective]

/-- A minimal closure-approximant family: each stage keeps the seed and adds the
current stage view. -/
def toyClosureApprox : ClosureApproximation (World := ToyWorld) ℕ (Set ToyWorld) where
  approx n seed := seed ∪ toyStageView.region n
  mono := by
    intro i j seed hij x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((StagedView.region_mono toyStageView hij) hx)

theorem city_mem_toyClosureApprox_empty_0 :
    ToyWorld.city ∈ toyClosureApprox.approx 0 (∅ : Set ToyWorld) := by
  simp [toyClosureApprox, toyStageView, groundedPerspective]

theorem hidden_not_mem_toyClosureApprox_empty_1 :
    ToyWorld.hidden ∉ toyClosureApprox.approx 1 (∅ : Set ToyWorld) := by
  simp [toyClosureApprox, toyStageView, groundedPerspective]

theorem hidden_mem_toyClosureApprox_empty_4 :
    ToyWorld.hidden ∈ toyClosureApprox.approx 4 (∅ : Set ToyWorld) := by
  simp [toyClosureApprox, toyStageView, groundedPerspective]

/-- One concrete example where a specific bound and an intersection coexist: the
available region can be further cut by a stage view. -/
def stagedAvailableGrounded (n : ℕ) : Set ToyWorld :=
  availableRegion groundedPerspective 5 Set.univ ∩ toyStageView.region n

theorem city_mem_stagedAvailableGrounded_0 :
    ToyWorld.city ∈ stagedAvailableGrounded 0 := by
  refine ⟨?_, city_mem_toyStageView_0⟩
  exact ⟨city_mem_observableUniverse_grounded, city_mem_nearEurycosm_grounded_budget5, by simp⟩

theorem hidden_not_mem_stagedAvailableGrounded_4 :
    ToyWorld.hidden ∉ stagedAvailableGrounded 4 := by
  intro h
  have hObs : ToyWorld.hidden ∈ observableUniverse groundedPerspective := by
    exact availableRegion_subset_observableUniverse groundedPerspective 5 Set.univ h.1
  exact hidden_not_mem_observableUniverse_grounded hObs

/-- Positive multiverse shell example: a surprise can move the observer from the
city hypothesis to the forest hypothesis. -/
def toyMultiverse : Multiverse (World := ToyWorld) ToyEvent where
  candidateWorlds := {ToyWorld.city, ToyWorld.forest}
  step w e :=
    match w, e with
    | .city, .surprise => {ToyWorld.forest}
    | .forest, .surprise => {ToyWorld.city}
    | .hidden, .surprise => ∅

theorem forest_mem_oneStepReachable_toyMultiverse :
    ToyWorld.forest ∈ oneStepReachable toyMultiverse := by
  exact ⟨ToyWorld.city, ToyEvent.surprise, by simp [toyMultiverse], by simp [toyMultiverse]⟩

end Mettapedia.Hyperseed.UltrainfinitismRegression
