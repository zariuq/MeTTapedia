import Mettapedia.Logic.PLNRegimeMixtureTheorems

/-!
# No-Go: Variance Accumulation in Regime-Mixture Chains

This module formalizes the **variance accumulation** no-go theorem:

When a chain of inference steps each involves an unresolved regime mixture with
positive variance, the accumulated uncertainty (sum of per-step variances) grows
at least linearly with chain length. There is no mechanism by which later steps
can "undo" earlier variance contributions.

**Design implication**: long chains over unresolved regime mixtures accumulate
irreducible uncertainty. Truncation or revelation of the mixture at each step
is necessary to avoid linear variance growth.

## Mathematical content

1. `mixtureVariance_pos_of_nondegen`: for a non-degenerate mixture (two regimes
   with different query values each having positive weight), the mixture variance is
   strictly positive.

2. `variance_accumulation`: for a chain of n non-degenerate steps each with variance
   ≥ δ, the total accumulated variance is ≥ n · δ.

Both results build directly on the `expectedSquaredLoss_decomposition` theorem from
`PLNRegimeMixtureTheorems.lean`.
-/

namespace Mettapedia.Logic.PLNVarianceChainNoGo

open scoped BigOperators
open Mettapedia.Logic.PLNRegimeMixtureTheorems

/-! ## Step 1: Positive variance for non-degenerate mixtures -/

/-- A mixture with two regimes having distinct query values and positive weights
has strictly positive variance.

The key argument: if `q r1 ≠ q r2`, they cannot both equal the mixture mean `m`.
The regime with `q r ≠ m` contributes `w r * (q r - m)^2 > 0` to the variance sum. -/
theorem mixtureVariance_pos_of_nondegen {R : Type*} [Fintype R] [DecidableEq R]
    (w q : R → ℝ) (hw : ValidRegimeWeights w)
    (r1 r2 : R) (_hr : r1 ≠ r2) (hw1 : 0 < w r1) (hw2 : 0 < w r2)
    (hq : q r1 ≠ q r2) :
    0 < mixtureVariance w q := by
  -- Unfold variance to the weighted sum of squared deviations
  have hvar_eq : mixtureVariance w q =
      ∑ r : R, w r * (q r - mixtureValue w q)^2 := by
    unfold mixtureVariance expectedSquaredLoss
    congr 1; ext r; ring
  rw [hvar_eq]
  -- Show all terms are nonneg
  have hnn : ∀ r ∈ Finset.univ, 0 ≤ w r * (q r - mixtureValue w q)^2 := by
    intro r _
    apply mul_nonneg
    · exact (hw.1 r)
    · positivity
  -- Find at least one positive term
  set m := mixtureValue w q
  -- q r1 ≠ q r2 implies at least one differs from m
  have hne : q r1 ≠ m ∨ q r2 ≠ m := by
    rcases (ne_or_eq (q r1) m) with h | h
    · exact Or.inl h
    · exact Or.inr (fun h2 => hq (h.trans h2.symm))
  -- In either case, obtain the positive-contribution regime
  rcases hne with hne1 | hne2
  · -- r1 contributes positively
    apply lt_of_lt_of_le _ (Finset.single_le_sum hnn (Finset.mem_univ r1))
    exact mul_pos hw1 (sq_pos_of_ne_zero (sub_ne_zero.mpr hne1))
  · -- r2 contributes positively
    apply lt_of_lt_of_le _ (Finset.single_le_sum hnn (Finset.mem_univ r2))
    exact mul_pos hw2 (sq_pos_of_ne_zero (sub_ne_zero.mpr hne2))

/-! ## Step 2: Linear variance accumulation over n chain steps -/

/-- **Variance accumulation**: for a chain of n steps each with mixture variance ≥ δ,
the total variance over all steps is at least n · δ.

This holds regardless of the specific query values at each step—even if the regime
structure changes between steps, uncertainty cannot decrease below δ per step. -/
theorem variance_accumulation {R : Type*} [Fintype R]
    (n : ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (ws qs : Fin n → R → ℝ)
    (_hws : ∀ i, ValidRegimeWeights (ws i))
    (hfloor : ∀ i, δ ≤ mixtureVariance (ws i) (qs i)) :
    n * δ ≤ ∑ i : Fin n, mixtureVariance (ws i) (qs i) := by
  calc (n : ℝ) * δ
      = ∑ _i : Fin n, δ := by simp [Finset.sum_const]
    _ ≤ ∑ i : Fin n, mixtureVariance (ws i) (qs i) :=
        Finset.sum_le_sum (fun i _ => hfloor i)

/-! ## Step 3: Explicit chain-with-resets accumulation -/

/-- Actions relevant for variance accumulation along a higher-order chain. -/
inductive VarianceChainAction where
  | continue
  | reveal
  | fallback
  deriving DecidableEq, Repr

/-- One step of a variance-tracked higher-order chain. -/
structure VarianceChainStep where
  action : VarianceChainAction
  varianceFloor : ℝ
  varianceFloor_nonneg : 0 ≤ varianceFloor

/-- Accumulate unresolved variance along a chain, resetting after `reveal` or
`fallback`. -/
def unresolvedVarianceAfterAux (acc : ℝ) : List VarianceChainStep → ℝ
  | [] => acc
  | step :: rest =>
      match step.action with
      | .continue => unresolvedVarianceAfterAux (acc + step.varianceFloor) rest
      | .reveal => unresolvedVarianceAfterAux 0 rest
      | .fallback => unresolvedVarianceAfterAux 0 rest

/-- Unresolved variance after executing a chain from a fresh start. -/
def unresolvedVarianceAfter (steps : List VarianceChainStep) : ℝ :=
  unresolvedVarianceAfterAux 0 steps

/-- Total variance mass contributed by unresolved `continue` steps, ignoring
reset actions. -/
def continueVarianceMass : List VarianceChainStep → ℝ
  | [] => 0
  | step :: rest =>
      match step.action with
      | .continue => step.varianceFloor + continueVarianceMass rest
      | .reveal => continueVarianceMass rest
      | .fallback => continueVarianceMass rest

theorem unresolvedVarianceAfterAux_append
    (acc : ℝ)
    (seg : List VarianceChainStep)
    (suffix : List VarianceChainStep) :
    unresolvedVarianceAfterAux acc (seg ++ suffix) =
      unresolvedVarianceAfterAux (unresolvedVarianceAfterAux acc seg) suffix := by
  induction seg generalizing acc with
  | nil =>
      simp [unresolvedVarianceAfterAux]
  | cons step seg ih =>
      cases hact : step.action <;>
        simp [unresolvedVarianceAfterAux, hact, ih]

theorem unresolvedVarianceAfterAux_eq_acc_add_continueVarianceMass_of_all_continue
    (acc : ℝ) (steps : List VarianceChainStep)
    (hcont : ∀ s ∈ steps, s.action = .continue) :
    unresolvedVarianceAfterAux acc steps = acc + continueVarianceMass steps := by
  induction steps generalizing acc with
  | nil =>
      simp [unresolvedVarianceAfterAux, continueVarianceMass]
  | cons step rest ih =>
      have hstep : step.action = .continue := hcont step (by simp)
      have hrest : ∀ s ∈ rest, s.action = .continue := by
        intro s hs
        exact hcont s (by simp [hs])
      have ih' :=
        ih (acc := acc + step.varianceFloor) hrest
      simp [unresolvedVarianceAfterAux, continueVarianceMass, hstep, ih', add_assoc]

theorem unresolvedVarianceAfter_eq_continueVarianceMass_of_all_continue
    (steps : List VarianceChainStep)
    (hcont : ∀ s ∈ steps, s.action = .continue) :
    unresolvedVarianceAfter steps = continueVarianceMass steps := by
  have h :=
    unresolvedVarianceAfterAux_eq_acc_add_continueVarianceMass_of_all_continue
      (acc := 0) steps hcont
  simpa [unresolvedVarianceAfter] using h

theorem continueVarianceMass_ge_length_mul_of_all_continue
    (δ : ℝ) :
    ∀ steps : List VarianceChainStep,
      (∀ s ∈ steps, s.action = .continue) →
      (∀ s ∈ steps, δ ≤ s.varianceFloor) →
      (steps.length : ℝ) * δ ≤ continueVarianceMass steps
  | [], _, _ => by simp [continueVarianceMass]
  | step :: rest, hcont, hfloor => by
      have hstep : step.action = .continue := hcont step (by simp)
      have hstepFloor : δ ≤ step.varianceFloor := hfloor step (by simp)
      have hrestCont : ∀ s ∈ rest, s.action = .continue := by
        intro s hs
        exact hcont s (by simp [hs])
      have hrestFloor : ∀ s ∈ rest, δ ≤ s.varianceFloor := by
        intro s hs
        exact hfloor s (by simp [hs])
      have ih :=
        continueVarianceMass_ge_length_mul_of_all_continue
          (δ := δ) rest hrestCont hrestFloor
      simp [continueVarianceMass, hstep]
      nlinarith

/-- Along a continue-only chain, any certified per-step variance floor `δ`
accumulates linearly in the unresolved variance. -/
theorem variance_accumulation_along_unrevealed_chain
    (δ : ℝ) (steps : List VarianceChainStep)
    (hcont : ∀ s ∈ steps, s.action = .continue)
    (hfloor : ∀ s ∈ steps, δ ≤ s.varianceFloor) :
    (steps.length : ℝ) * δ ≤ unresolvedVarianceAfter steps := by
  rw [unresolvedVarianceAfter_eq_continueVarianceMass_of_all_continue steps hcont]
  exact continueVarianceMass_ge_length_mul_of_all_continue δ steps hcont hfloor

theorem reveal_resets_variance_accumulation_aux
    (acc : ℝ) (step : VarianceChainStep) (rest : List VarianceChainStep)
    (hact : step.action = .reveal) :
    unresolvedVarianceAfterAux acc (step :: rest) = unresolvedVarianceAfter rest := by
  simp [unresolvedVarianceAfterAux, unresolvedVarianceAfter, hact]

theorem fallback_resets_variance_accumulation_aux
    (acc : ℝ) (step : VarianceChainStep) (rest : List VarianceChainStep)
    (hact : step.action = .fallback) :
    unresolvedVarianceAfterAux acc (step :: rest) = unresolvedVarianceAfter rest := by
  simp [unresolvedVarianceAfterAux, unresolvedVarianceAfter, hact]

/-- A reveal step resets unresolved variance regardless of the preceding
accumulator. -/
theorem reveal_resets_variance_accumulation
    (step : VarianceChainStep) (rest : List VarianceChainStep)
    (hact : step.action = .reveal) :
    unresolvedVarianceAfter (step :: rest) = unresolvedVarianceAfter rest :=
  reveal_resets_variance_accumulation_aux 0 step rest hact

/-- A fallback step also resets unresolved variance regardless of the preceding
accumulator. -/
theorem fallback_resets_variance_accumulation
    (step : VarianceChainStep) (rest : List VarianceChainStep)
    (hact : step.action = .fallback) :
    unresolvedVarianceAfter (step :: rest) = unresolvedVarianceAfter rest :=
  fallback_resets_variance_accumulation_aux 0 step rest hact

/-- Between resets, variance accumulates linearly; after a reveal/fallback
reset, the unresolved variance depends only on the suffix. -/
theorem variance_accumulation_between_resets
    (δ : ℝ)
    (seg : List VarianceChainStep)
    (suffix : List VarianceChainStep)
    (reset : VarianceChainStep)
    (hseg : ∀ s ∈ seg, s.action = .continue)
    (hfloor : ∀ s ∈ seg, δ ≤ s.varianceFloor)
    (hreset : reset.action = .reveal ∨ reset.action = .fallback) :
    (seg.length : ℝ) * δ ≤ unresolvedVarianceAfter seg ∧
      unresolvedVarianceAfter (seg ++ reset :: suffix) = unresolvedVarianceAfter suffix := by
  constructor
  · exact variance_accumulation_along_unrevealed_chain δ seg hseg hfloor
  · rw [unresolvedVarianceAfter,
      unresolvedVarianceAfterAux_append (acc := 0) (seg := seg) (suffix := reset :: suffix)]
    rcases hreset with hreveal | hfallback
    · exact reveal_resets_variance_accumulation_aux
        (unresolvedVarianceAfterAux 0 seg) reset suffix hreveal
    · exact fallback_resets_variance_accumulation_aux
        (unresolvedVarianceAfterAux 0 seg) reset suffix hfallback

end Mettapedia.Logic.PLNVarianceChainNoGo
