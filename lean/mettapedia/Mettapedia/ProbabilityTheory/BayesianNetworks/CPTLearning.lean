/-
# CPT Learning: Bridging PLN BinaryEvidence to Bayesian Network Parameters

This file connects PLN BinaryEvidence (from EvidenceBeta.lean) to CPT parameter estimation
for Boolean Bayesian network nodes. When all state spaces are Bool, each CPT entry
is a Bernoulli parameter, and PLN evidence provides a principled way to estimate it
via Beta posterior means.

## Main Definitions

- `IsBooleanBN`: All state spaces are Bool
- `BooleanCPTEntry`: A single CPT entry with evidence counts
- `evidenceToBernoulliParam`: Convert evidence to CPT probability via Beta posterior mean

## Main Results

- `evidenceToBernoulliParam_in_unit`: The estimated parameter is in [0, 1]
- `evidence_aggregation_preserves_cpt`: Aggregating evidence corresponds to Bayesian updating
- `cpt_param_converges`: CPT parameters converge as evidence grows

## References

- Goertzel, Ikle, Potapov, "Probabilistic Logic Networks" (2009)
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 17
-/

import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.Evidence.SourcePacketStore

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning

/-! ## Boolean Bayesian Networks -/

/-- A Bayesian network is Boolean if every node's state space is `Bool`. -/
def IsBooleanBN {V : Type*} [Fintype V] (bn : BayesianNetwork V) : Prop :=
  ∀ v : V, bn.stateSpace v = Bool

/-! ## CPT Learning from BinaryEvidence -/

/-- A single CPT entry for a Boolean node: evidence counts for a specific parent configuration. -/
structure BooleanCPTEntry where
  /-- Number of positive (True) observations -/
  n_pos : ℕ
  /-- Number of negative (False) observations -/
  n_neg : ℕ
  deriving Repr, DecidableEq

/-- Convert a BooleanCPTEntry to EvidenceBetaParams using a uniform (Laplace) prior. -/
noncomputable def BooleanCPTEntry.toLaplaceBeta (e : BooleanCPTEntry) :
    EvidenceBetaParams :=
  withUniformPrior e.n_pos e.n_neg

/-- Convert a BooleanCPTEntry to EvidenceBetaParams using a Jeffreys prior. -/
noncomputable def BooleanCPTEntry.toJeffreysBeta (e : BooleanCPTEntry) :
    EvidenceBetaParams :=
  withJeffreysPrior e.n_pos e.n_neg

/-- The Bernoulli parameter estimated from evidence via Beta posterior mean (Laplace prior). -/
noncomputable def evidenceToBernoulliParam (e : BooleanCPTEntry) : ℝ :=
  e.toLaplaceBeta.posteriorMean

/-! ## Properties -/

/-- The estimated Bernoulli parameter is in [0, 1]. -/
theorem evidenceToBernoulliParam_in_unit (e : BooleanCPTEntry) :
    0 ≤ evidenceToBernoulliParam e ∧ evidenceToBernoulliParam e ≤ 1 :=
  e.toLaplaceBeta.posteriorMean_mem_unit

/-- Aggregating evidence corresponds to conjugate Bayesian updating.

If we observe additional positive and negative counts, the resulting Beta parameters
are exactly the original parameters updated with the new evidence. -/
theorem evidence_aggregation_preserves_cpt (e : BooleanCPTEntry) (n₂_pos n₂_neg : ℕ) :
    let e_combined : BooleanCPTEntry := ⟨e.n_pos + n₂_pos, e.n_neg + n₂_neg⟩
    e_combined.toLaplaceBeta.alpha = e.toLaplaceBeta.alpha + n₂_pos ∧
    e_combined.toLaplaceBeta.beta = e.toLaplaceBeta.beta + n₂_neg := by
  simp only [BooleanCPTEntry.toLaplaceBeta, withUniformPrior,
             EvidenceBetaParams.alpha, EvidenceBetaParams.beta, Nat.cast_add]
  constructor <;> ring

/-- CPT posterior mean converges to PLN strength as evidence grows.

For any ε > 0, there exists N such that for n_pos + n_neg ≥ N, the
difference between PLN strength (n⁺/n) and Beta posterior mean (n⁺+α)/(n+2α)
is less than ε. With Laplace prior (α = 1), this shows the CPT parameter
converges to the empirical frequency.

This wraps `strength_converges_to_mean` from EvidenceBeta. -/
theorem cpt_param_converges_to_strength :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n_pos n_neg : ℕ, N ≤ n_pos + n_neg → n_pos + n_neg ≠ 0 →
    let strength := plnStrength n_pos n_neg
    let mean := ((n_pos : ℝ) + 1) / ((n_pos : ℝ) + (n_neg : ℝ) + 2)
    |strength - mean| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := strength_converges_to_mean ε hε 1 one_pos
  refine ⟨N, fun n_pos n_neg hle hne => ?_⟩
  have h := hN n_pos n_neg hle hne
  -- h has mean = (n_pos + 1)/(n_pos + n_neg + 2*1) which equals our goal
  simp only [mul_one] at h
  exact h

/-! ## Source-retaining exact parameter observations -/

open Mettapedia.Evidence.SourcePacketStore

def sourcedEntry {Source : Type*} (store : Store Source (ℕ × ℕ)) : BooleanCPTEntry :=
  ⟨(counts store).1, (counts store).2⟩

theorem sourcedEntry_insert {Source : Type*} [DecidableEq Source]
    (store : Store Source (ℕ × ℕ)) (source : Source) (positives negatives : ℕ) :
    sourcedEntry (store.insert source (positives, negatives)) =
      ⟨positives + (sourcedEntry (store.erase source)).n_pos,
       negatives + (sourcedEntry (store.erase source)).n_neg⟩ := by
  simp [sourcedEntry, counts_insert]

theorem sourcedEntry_repeat {Source : Type*} [DecidableEq Source]
    (store : Store Source (ℕ × ℕ)) (packet : Packet Source (ℕ × ℕ))
    (present : store.lookup packet.source = some packet.payload) :
    (deliver store packet).map sourcedEntry = some (sourcedEntry store) := by
  rw [deliver_existing store packet present]
  rfl

theorem sourcedEntry_retract_replacement {Source : Type*} [DecidableEq Source]
    (store : Store Source (ℕ × ℕ)) (source : Source) (payload : ℕ × ℕ) :
    sourcedEntry ((store.insert source payload).erase source) = sourcedEntry (store.erase source) := by
  rw [retract_replacement]

def exactPosteriorMean (alpha beta : ℚ) (entry : BooleanCPTEntry) : ℚ :=
  (alpha + entry.n_pos) / (alpha + entry.n_pos + (beta + entry.n_neg))

def posteriorPrior (alpha beta : ℚ) (positiveAlpha : 0 < alpha) (positiveBeta : 0 < beta)
    (entry : BooleanCPTEntry) : Mettapedia.ProbabilityTheory.BetaBernoulliPrior where
  α := (alpha : ℝ) + entry.n_pos
  β := (beta : ℝ) + entry.n_neg
  α_pos := by
    have positive : (0 : ℝ) < alpha := by exact_mod_cast positiveAlpha
    have nonnegative : (0 : ℝ) ≤ entry.n_pos := Nat.cast_nonneg _
    linarith
  β_pos := by
    have positive : (0 : ℝ) < beta := by exact_mod_cast positiveBeta
    have nonnegative : (0 : ℝ) ≤ entry.n_neg := Nat.cast_nonneg _
    linarith

theorem exactPosteriorMean_refines (alpha beta : ℚ) (positiveAlpha : 0 < alpha)
    (positiveBeta : 0 < beta) (entry : BooleanCPTEntry) :
    (exactPosteriorMean alpha beta entry : ℝ) =
      (posteriorPrior alpha beta positiveAlpha positiveBeta entry).mean := by
  simp [exactPosteriorMean, posteriorPrior, Mettapedia.ProbabilityTheory.BetaBernoulliPrior.mean]

theorem exactPosteriorMean_mem_unit (alpha beta : ℚ) (positiveAlpha : 0 < alpha)
    (positiveBeta : 0 < beta) (entry : BooleanCPTEntry) :
    0 ≤ exactPosteriorMean alpha beta entry ∧ exactPosteriorMean alpha beta entry ≤ 1 := by
  have den : 0 < alpha + entry.n_pos + (beta + entry.n_neg) := by positivity
  constructor
  · unfold exactPosteriorMean
    apply div_nonneg <;> positivity
  · rw [exactPosteriorMean, div_le_one den]
    have nonnegative : (0 : ℚ) ≤ entry.n_neg := Nat.cast_nonneg _
    linarith

theorem exactPosteriorMean_laplace (entry : BooleanCPTEntry) :
    (exactPosteriorMean 1 1 entry : ℝ) = evidenceToBernoulliParam entry := by
  simp [exactPosteriorMean, evidenceToBernoulliParam, BooleanCPTEntry.toLaplaceBeta,
    withUniformPrior, EvidenceBetaParams.posteriorMean, EvidenceBetaParams.alpha, EvidenceBetaParams.beta]

theorem beta_batch_parameters (prior : Mettapedia.ProbabilityTheory.BetaBernoulliPrior)
    (outcomes : List Bool) :
    (outcomes.foldl Mettapedia.ProbabilityTheory.BetaBernoulliPrior.posterior prior).α =
      prior.α + outcomes.count true ∧
    (outcomes.foldl Mettapedia.ProbabilityTheory.BetaBernoulliPrior.posterior prior).β =
      prior.β + outcomes.count false := by
  induction outcomes generalizing prior with
  | nil => simp
  | cons outcome outcomes ih =>
      have tail := ih (prior.posterior outcome)
      cases outcome <;>
        simp [List.foldl_cons, Mettapedia.ProbabilityTheory.BetaBernoulliPrior.posterior] at tail ⊢ <;>
        constructor <;> linarith [tail.1, tail.2]

end Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning
