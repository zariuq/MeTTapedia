import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.ProbabilityTheory.MarkovCategory

/-!
# WM Experiment Layer (Stochastic Channels)

Finite stochastic extension of the experiment WM layer:

- channels as `Θ → PMF Ω`
- Blackwell-style garbling factorization as channel composition
- explicit utility/decision layer with finite priors
- value monotonicity (`optimalValue weak ≤ optimalValue strong`) under Blackwell factorization
- bridge to existing `MarkovCategoryCore` abstraction
-/

namespace Mettapedia.Logic.PLNWorldModelExperimentStochastic

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v w

abbrev StochasticChannel (Θ : Type u) (Ω : Type v) := Θ → PMF Ω
abbrev StochasticState (Θ : Type u) := Θ → ℝ≥0∞

instance {Θ : Type u} : EvidenceType (StochasticState Θ) where

/-- Kleisli composition for PMF channels (`first f, then g`). -/
noncomputable def stochasticComp {Θ : Type u} {Ω : Type v} {Υ : Type w}
    (f : StochasticChannel Θ Ω) (g : StochasticChannel Ω Υ) :
    StochasticChannel Θ Υ :=
  fun θ => (f θ).bind g

/-- Deterministic channel embedded into PMF channels. -/
noncomputable def stochasticId (Θ : Type u) : StochasticChannel Θ Θ :=
  fun θ => PMF.pure θ

/-- Shared-abstraction bridge:
PMF channels instantiate the existing `MarkovCategoryCore` interface. -/
noncomputable def stochasticMarkovCategoryCore : Mettapedia.ProbabilityTheory.MarkovCategoryCore where
  Obj := Type u
  Hom := fun X Y => StochasticChannel X Y
  id := stochasticId
  comp := fun {X Y Z} f g => stochasticComp f g
  prod := fun X Y => X × Y
  unit := PUnit
  copy := fun X x => PMF.pure (x, x)
  discard := fun X _ => PMF.pure PUnit.unit
  id_comp := by
    intro X Y f
    funext x
    simp [stochasticComp, stochasticId]
  comp_id := by
    intro X Y f
    funext x
    change (f x).bind (fun y => PMF.pure y) = f x
    simp
  comp_assoc := by
    intro W X Y Z f g h
    funext x
    unfold stochasticComp
    exact (PMF.bind_bind (f x) g h).symm

/-- Explicit compatibility theorem with `MarkovCategoryCore.comp`. -/
theorem stochasticComp_eq_markovCoreComp
    {Θ : Type u} {Ω : Type u} {Υ : Type u}
    (f : StochasticChannel Θ Ω) (g : StochasticChannel Ω Υ) :
    stochasticComp f g =
      Mettapedia.ProbabilityTheory.MarkovCategoryCore.comp
        stochasticMarkovCategoryCore f g := by
  rfl

/-- Query for stochastic channels: event predicate on observations. -/
@[ext] structure StochasticExperimentQuery (Θ : Type u) (Ω : Type v) where
  channel : StochasticChannel Θ Ω
  outcome : Ω → Prop

/-- Event probability at one hypothesis under a stochastic query. -/
noncomputable def eventProb
    {Θ : Type u} {Ω : Type v} [Fintype Ω]
    (q : StochasticExperimentQuery Θ Ω) (θ : Θ) : ℝ≥0∞ := by
  classical
  exact ∑ o, if q.outcome o then q.channel θ o else 0

/-- Complement event probability at one hypothesis under a stochastic query. -/
noncomputable def eventProbCompl
    {Θ : Type u} {Ω : Type v} [Fintype Ω]
    (q : StochasticExperimentQuery Θ Ω) (θ : Θ) : ℝ≥0∞ := by
  classical
  exact ∑ o, if q.outcome o then 0 else q.channel θ o

/-- Finite weighted-state evidence for stochastic event queries. -/
noncomputable def stochasticEvidence
    {Θ : Type u} {Ω : Type v}
    [Fintype Θ] [Fintype Ω]
    (W : StochasticState Θ) (q : StochasticExperimentQuery Θ Ω) : BinaryEvidence := by
  classical
  exact
    ⟨∑ θ, W θ * eventProb q θ,
     ∑ θ, W θ * eventProbCompl q θ⟩

theorem stochasticEvidence_add
    {Θ : Type u} {Ω : Type v}
    [Fintype Θ] [Fintype Ω]
    (W₁ W₂ : StochasticState Θ) (q : StochasticExperimentQuery Θ Ω) :
    stochasticEvidence (W₁ + W₂) q =
      stochasticEvidence W₁ q + stochasticEvidence W₂ q := by
  classical
  apply BinaryEvidence.ext'
  ·
    simp [stochasticEvidence, eventProb, BinaryEvidence.hplus_def, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  ·
    simp [stochasticEvidence, eventProbCompl, BinaryEvidence.hplus_def, add_mul, Finset.sum_add_distrib, Pi.add_apply]

/-- WM instance for finite weighted states with stochastic experiment queries. -/
noncomputable instance
    {Θ : Type u} {Ω : Type v}
    [Fintype Θ] [Fintype Ω] :
    BinaryWorldModel (StochasticState Θ) (StochasticExperimentQuery Θ Ω) where
  evidence := stochasticEvidence
  evidence_add := stochasticEvidence_add
  evidence_zero q := by
    classical
    simp only [stochasticEvidence, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; rfl

abbrev Prior (Θ : Type u) := PMF Θ
abbrev DecisionRule (Ω : Type v) (A : Type w) := Ω → PMF A

/-- Blackwell-style factorization for stochastic channels:
`weak = strong ≫ κ` (Kleisli composition). -/
def BlackwellFactorsThrough
    {Θ : Type u} {Ω : Type v}
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω) : Prop :=
  weak = stochasticComp strong κ

/-- Equivalent restatement in terms of Markov-core composition. -/
theorem blackwellFactorsThrough_iff_markovCoreComp
    {Θ : Type u} {Ω : Type u}
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω) :
    BlackwellFactorsThrough strong weak κ ↔
      weak =
        Mettapedia.ProbabilityTheory.MarkovCategoryCore.comp
          stochasticMarkovCategoryCore strong κ := by
  constructor
  · intro h
    simpa [BlackwellFactorsThrough, stochasticComp_eq_markovCoreComp] using h
  · intro h
    simpa [BlackwellFactorsThrough, stochasticComp_eq_markovCoreComp] using h

/-- Channel-induced action distribution after applying a decision rule. -/
noncomputable def inducedActionDist
    {Θ : Type u} {Ω : Type v} {A : Type w}
    (ch : StochasticChannel Θ Ω)
    (δ : DecisionRule Ω A) (θ : Θ) : PMF A :=
  (ch θ).bind δ

/-- Lift a weak-side decision rule to the strong channel via garbling `κ`. -/
noncomputable def liftDecision
    {Ω : Type v} {A : Type w}
    (κ : StochasticChannel Ω Ω)
    (δ : DecisionRule Ω A) : DecisionRule Ω A :=
  fun o => (κ o).bind δ

/-- Expected utility under a finite prior, stochastic channel, and decision rule. -/
noncomputable def expectedUtility
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (π : Prior Θ)
    (ch : StochasticChannel Θ Ω)
    (δ : DecisionRule Ω A)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∑ θ, π θ * ∑ a, (inducedActionDist ch δ θ) a * u θ a

/-- If `weak = strong ≫ κ`, then every weak policy has an equivalent lifted
strong policy with identical expected utility. -/
theorem expectedUtility_eq_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (π : Prior Θ)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (δ : DecisionRule Ω A)
    (u : Θ → A → ℝ≥0∞) :
    expectedUtility π weak δ u =
      expectedUtility π strong (liftDecision κ δ) u := by
  classical
  unfold expectedUtility
  refine Finset.sum_congr rfl ?_
  intro θ hθ
  have hdist :
      inducedActionDist weak δ θ =
        inducedActionDist strong (liftDecision κ δ) θ := by
    rcases hfactor with rfl
    unfold inducedActionDist stochasticComp liftDecision
    rw [PMF.bind_bind]
  simp [hdist]

/-- Optimal expected utility over all decision rules. -/
noncomputable def optimalValue
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (π : Prior Θ)
    (ch : StochasticChannel Θ Ω)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ δ : DecisionRule Ω A, expectedUtility π ch δ u

/-- Decision/utility consequence theorem:
Blackwell factorization implies value monotonicity under explicit finite priors. -/
theorem optimalValue_mono_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (π : Prior Θ)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (u : Θ → A → ℝ≥0∞) :
    optimalValue π weak u ≤ optimalValue π strong u := by
  classical
  refine iSup_le ?_
  intro δw
  calc
    expectedUtility π weak δw u =
        expectedUtility π strong (liftDecision κ δw) u := by
          exact expectedUtility_eq_of_blackwellFactor π strong weak κ hfactor δw u
    _ ≤ optimalValue π strong u := by
      exact le_iSup (fun δ => expectedUtility π strong δ u) (liftDecision κ δw)

abbrev SourceWeight (Θ : Type u) := Θ → ℝ≥0∞

/-- Weighted/trusted-source experiment policy:
base source weights with a trust gate selecting admitted sources. -/
@[ext] structure WeightedSourcePolicy (Θ : Type u) where
  baseWeight : SourceWeight Θ
  trusted : Θ → Bool

/-- Effective source weights after applying the trust gate. -/
def WeightedSourcePolicy.effectiveWeight
    {Θ : Type u} (π : WeightedSourcePolicy Θ) : SourceWeight Θ :=
  fun θ => if π.trusted θ then π.baseWeight θ else 0

/-- Expected utility with general source weights (no normalization requirement). -/
noncomputable def expectedUtilityWeighted
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (ω : SourceWeight Θ)
    (ch : StochasticChannel Θ Ω)
    (δ : DecisionRule Ω A)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∑ θ, ω θ * ∑ a, (inducedActionDist ch δ θ) a * u θ a

/-- Weighted expected utility transport under Blackwell factorization. -/
theorem expectedUtilityWeighted_eq_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (ω : SourceWeight Θ)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (δ : DecisionRule Ω A)
    (u : Θ → A → ℝ≥0∞) :
    expectedUtilityWeighted ω weak δ u =
      expectedUtilityWeighted ω strong (liftDecision κ δ) u := by
  classical
  unfold expectedUtilityWeighted
  refine Finset.sum_congr rfl ?_
  intro θ hθ
  have hdist :
      inducedActionDist weak δ θ =
        inducedActionDist strong (liftDecision κ δ) θ := by
    rcases hfactor with rfl
    unfold inducedActionDist stochasticComp liftDecision
    rw [PMF.bind_bind]
  simp [hdist]

/-- Optimal weighted expected utility over all decision rules. -/
noncomputable def optimalValueWeighted
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (ω : SourceWeight Θ)
    (ch : StochasticChannel Θ Ω)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ δ : DecisionRule Ω A, expectedUtilityWeighted ω ch δ u

/-- Weighted/source-aware transfer theorem:
Blackwell factorization preserves utility monotonicity under arbitrary
source weights. -/
theorem optimalValueWeighted_mono_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (ω : SourceWeight Θ)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (u : Θ → A → ℝ≥0∞) :
    optimalValueWeighted ω weak u ≤ optimalValueWeighted ω strong u := by
  classical
  refine iSup_le ?_
  intro δw
  calc
    expectedUtilityWeighted ω weak δw u =
        expectedUtilityWeighted ω strong (liftDecision κ δw) u := by
          exact
            expectedUtilityWeighted_eq_of_blackwellFactor
              ω strong weak κ hfactor δw u
    _ ≤ optimalValueWeighted ω strong u := by
      exact le_iSup (fun δ => expectedUtilityWeighted ω strong δ u) (liftDecision κ δw)

/-- Policy-view expected utility: weighted utility under trusted-source gating. -/
noncomputable def expectedUtilityPolicy
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (policy : WeightedSourcePolicy Θ)
    (ch : StochasticChannel Θ Ω)
    (δ : DecisionRule Ω A)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ :=
  expectedUtilityWeighted policy.effectiveWeight ch δ u

/-- Policy-view optimal utility. -/
noncomputable def optimalValuePolicy
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (policy : WeightedSourcePolicy Θ)
    (ch : StochasticChannel Θ Ω)
    (u : Θ → A → ℝ≥0∞) : ℝ≥0∞ :=
  optimalValueWeighted policy.effectiveWeight ch u

/-- Trusted-source gate transfer theorem:
for any policy, Blackwell factorization implies policy-level utility
monotonicity. -/
theorem optimalValuePolicy_mono_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (policy : WeightedSourcePolicy Θ)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (u : Θ → A → ℝ≥0∞) :
    optimalValuePolicy policy weak u ≤ optimalValuePolicy policy strong u := by
  exact
    optimalValueWeighted_mono_of_blackwellFactor
      policy.effectiveWeight strong weak κ hfactor u

/-- Convenience wrapper with explicit base weights and trust gate. -/
theorem optimalValue_trustedGate_mono_of_blackwellFactor
    {Θ : Type u} {Ω : Type v} {A : Type w}
    [Fintype Θ] [Fintype A]
    (baseWeight : SourceWeight Θ)
    (trusted : Θ → Bool)
    (strong weak : StochasticChannel Θ Ω)
    (κ : StochasticChannel Ω Ω)
    (hfactor : BlackwellFactorsThrough strong weak κ)
    (u : Θ → A → ℝ≥0∞) :
    optimalValuePolicy
        (WeightedSourcePolicy.mk baseWeight trusted)
        weak u ≤
      optimalValuePolicy
        (WeightedSourcePolicy.mk baseWeight trusted)
        strong u := by
  exact
    optimalValuePolicy_mono_of_blackwellFactor
      (policy := WeightedSourcePolicy.mk baseWeight trusted)
      strong weak κ hfactor u

end Mettapedia.Logic.PLNWorldModelExperimentStochastic
