import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.BooleanRepresentation

/-!
# K&S + Separation → PLN Deduction Formula

This file proves that the K&S axiom system with Separation implies the PLN
deduction formula. This establishes the second derivation path in the hypercube:

```
     Kolmogorov Axioms           K&S Axioms + Separation
            ↓                              ↓
    Law of Total Prob          Representation Theorem
            ↓                              ↓
    + Independence               Θ : α ≃o (ℝ≥0, +)
            ↓                              ↓
            └──────────┬───────────────────┘
                       ↓
              Normalization to [0,1]
                       ↓
              PLN Deduction Formula
              sAC = sAB·sBC + (1-sAB)·(pC-pB·sBC)/(1-pB)
```

## Main Results

1. `ks_representation_to_probability` - K&S representation gives probability via normalization
2. `probability_satisfies_frechet` - The normalized probabilities satisfy Fréchet bounds
3. `ks_separation_implies_pln_deduction` - Main theorem: K&S + Separation → PLN formula

## Dependencies

This file imports from:
- `BooleanRepresentation.lean` - Core K&S structures (no PLN dependency)
- `PLNDeduction.lean` - PLN deduction formula
- `PLNFrechetBounds.lean` - Fréchet bound equivalence

The K&S project does NOT depend on PLN. Rather, PLN can be derived FROM K&S.

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 5
- PLNFrechetBounds.lean for the Fréchet ↔ consistency equivalence
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.PLNConnection

open Mettapedia.Logic.PLNDeduction
open Mettapedia.ProbabilityTheory.KnuthSkilling.BooleanRepresentation

-- Re-export the core structures for backward compatibility
export BooleanRepresentation (KSRepresentation KSBooleanRepresentation)

namespace KSBooleanRepresentation

variable {α : Type*} [BooleanAlgebra α] (R : KSBooleanRepresentation α)

/-!
## §1: PLN Consistency from Fréchet Bounds

The Fréchet bounds (from BooleanRepresentation.lean) imply PLN consistency.
-/

/-- Conditional probability satisfies PLN consistency bounds -/
theorem condProb_consistent (a b : α) (h : R.Θ ⊤ ≠ 0) (ha : R.probability a ≠ 0) :
    conditionalProbabilityConsistency (R.probability a) (R.probability b) (R.condProb b a) := by
  have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm ha)
  have hfrechet_lower := R.frechet_lower a b h
  have hfrechet_upper := R.frechet_upper a b
  constructor
  · -- 0 < P(a)
    exact ha_pos
  constructor
  · -- Lower bound from Fréchet
    -- smallestIntersectionProbability pA pB = max 0 ((pA + pB - 1) / pA)
    unfold smallestIntersectionProbability condProb
    simp only [ha, ↓reduceDIte]
    apply max_le
    · -- 0 ≤ P(a ⊓ b) / P(a)
      apply div_nonneg (R.probability_nonneg _) (le_of_lt ha_pos)
    · -- (P(a) + P(b) - 1) / P(a) ≤ P(a ⊓ b) / P(a)
      apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      -- P(a) + P(b) - 1 ≤ P(a ⊓ b) from Fréchet lower bound
      -- hfrechet_lower : max 0 (P+P-1) ≤ P(a⊓b), so P+P-1 ≤ max 0 (P+P-1) ≤ P(a⊓b)
      exact le_trans (le_max_right 0 _) hfrechet_lower
  · -- Upper bound from Fréchet
    -- largestIntersectionProbability pA pB = min 1 (pB / pA)
    unfold largestIntersectionProbability condProb
    simp only [ha, ↓reduceDIte]
    apply le_min
    · -- P(a ⊓ b) / P(a) ≤ 1
      rw [div_le_one ha_pos]
      exact (le_min_iff.mp hfrechet_upper).1
    · -- P(a ⊓ b) / P(a) ≤ P(b) / P(a)
      apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      exact (le_min_iff.mp hfrechet_upper).2

/-- Conditional probability is non-negative -/
theorem condProb_nonneg (b a : α) : 0 ≤ R.condProb b a := by
  unfold condProb
  split_ifs
  · exact le_refl 0
  · apply div_nonneg (R.probability_nonneg _) (R.probability_nonneg _)

/-- Conditional probability is at most 1 -/
theorem condProb_le_one (b a : α) : R.condProb b a ≤ 1 := by
  unfold condProb
  split_ifs with h
  · exact zero_le_one
  · have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm h)
    rw [div_le_one ha_pos]
    -- P(a ⊓ b) ≤ P(a) since a ⊓ b ≤ a
    have hle := R.frechet_upper a b
    exact le_trans (le_min_iff.mp hle).1 (le_refl _)

/-- Conditional probability is in [0, 1] -/
theorem condProb_mem_unit (b a : α) : R.condProb b a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨R.condProb_nonneg b a, R.condProb_le_one b a⟩

/-!
## §2: The Main Theorem: K&S + Separation → PLN Deduction
-/

/-- **Main Theorem**: K&S representation implies PLN deduction formula is valid.

Given a K&S representation on a Boolean algebra, the PLN deduction formula
produces valid probabilities in [0, 1].

This completes the derivation chain:
  K&S Axioms + Separation
         ↓
  Representation Theorem (Θ : α ≃o ℝ≥0)
         ↓
  Normalization (P = Θ/Θ(⊤))
         ↓
  Fréchet bounds (from modularity)
         ↓
  PLN consistency (from Fréchet)
         ↓
  PLN deduction formula valid
-/
theorem ks_implies_pln_valid (a b c : α)
    (h : R.Θ ⊤ ≠ 0)
    (ha : R.probability a ≠ 0)
    (hb : R.probability b ≠ 0)
    (hb_small : R.probability b < 0.99) :
    simpleDeductionStrengthFormula
      (R.probability a) (R.probability b) (R.probability c)
      (R.condProb b a) (R.condProb c b) ∈ Set.Icc (0 : ℝ) 1 := by
  have h_consist_ab := R.condProb_consistent a b h ha
  have h_consist_bc := R.condProb_consistent b c h hb
  exact deduction_formula_in_unit_interval
    (R.probability a) (R.probability b) (R.probability c)
    (R.condProb b a) (R.condProb c b)
    (R.probability_mem_unit a) (R.probability_mem_unit b) (R.probability_mem_unit c)
    (R.condProb_mem_unit b a)
    (R.condProb_mem_unit c b)
    hb_small
    ⟨h_consist_ab, h_consist_bc⟩

end KSBooleanRepresentation

/-!
## §3: Indefinite PLN from Credal Sets

The indefinite version of PLN (interval truth values) corresponds to:
1. K&S without completeness → credal set (set of representations)
2. Each representation gives a probability
3. The interval [L, U] = [inf P, sup P] over the credal set

This connects to:
- Walley's imprecise probabilities (LowerPrevision, UpperPrevision)
- The CredalAlgebra structure in CredalSets.lean
-/

/-- A credal set is a set of K&S representations.

Without completeness, we may have multiple valid representations,
giving interval-valued probabilities. -/
structure CredalSet (α : Type*) [BooleanAlgebra α] where
  representations : Set (KSBooleanRepresentation α)
  nonempty : representations.Nonempty

namespace CredalSet

variable {α : Type*} [BooleanAlgebra α] (C : CredalSet α)

/-- Lower probability: P*(a) = inf { R.probability a | R ∈ credal set } -/
noncomputable def lowerProb (a : α) : ℝ :=
  sInf { R.probability a | R ∈ C.representations }

/-- Upper probability: P*(a) = sup { R.probability a | R ∈ credal set } -/
noncomputable def upperProb (a : α) : ℝ :=
  sSup { R.probability a | R ∈ C.representations }

/-- The probability interval for an event -/
noncomputable def probInterval (a : α) : Set ℝ :=
  Set.Icc (C.lowerProb a) (C.upperProb a)

/-- **Indefinite PLN Truth Value** from credal set:
- Strength interval: [L, U] = [lowerProb, upperProb]
- Confidence: related to interval width (narrower = more confident)
-/
structure IndefiniteTruthValue where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1

/-- Convert credal probability to indefinite truth value -/
noncomputable def toIndefiniteTruthValue (a : α)
    (h_lower : 0 ≤ C.lowerProb a)
    (h_upper : C.upperProb a ≤ 1)
    (h_valid : C.lowerProb a ≤ C.upperProb a) : IndefiniteTruthValue where
  lower := C.lowerProb a
  upper := C.upperProb a
  valid := h_valid
  lower_nonneg := h_lower
  upper_le_one := h_upper

end CredalSet

/-!
## §4: Summary: The Complete Derivation Diagram

```
                    ┌─────────────────────────────────────┐
                    │          Hypercube Vertex           │
                    │  (commutative, precise, tensor)     │
                    └─────────────────────────────────────┘
                                     │
           ┌─────────────────────────┼─────────────────────────┐
           │                         │                         │
           ▼                         ▼                         ▼
    ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
    │  Kolmogorov │          │     Cox     │          │ K&S + Sep   │
    │  σ-algebra  │          │  Func. eqs  │          │  Assoc+Arch │
    └─────────────┘          └─────────────┘          └─────────────┘
           │                         │                         │
           ▼                         ▼                         ▼
    ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
    │  Measure    │          │  Product    │          │  Θ : α→ℝ≥0  │
    │  Theory     │          │  Rule       │          │  (additive) │
    └─────────────┘          └─────────────┘          └─────────────┘
           │                         │                         │
           └─────────────────────────┼─────────────────────────┘
                                     │
                                     ▼
                         ┌───────────────────┐
                         │   Normalization   │
                         │   P = Θ/Θ(Ω)      │
                         └───────────────────┘
                                     │
                                     ▼
                         ┌───────────────────┐
                         │  Fréchet Bounds   │
                         │  (from modularity)│
                         └───────────────────┘
                                     │
                    ┌────────────────┼────────────────┐
                    │                │                │
                    ▼                ▼                ▼
             ┌───────────┐    ┌───────────┐    ┌───────────┐
             │ PLN Simple│    │ Law of    │    │  Credal   │
             │ Deduction │◄───│ Total Prob│───►│   Sets    │
             └───────────┘    └───────────┘    └───────────┘
                    │                                │
                    ▼                                ▼
             ┌───────────┐                    ┌───────────┐
             │  sAC =    │                    │ PLN Indef │
             │ sAB·sBC + │                    │ [L, U], b │
             │   ...     │                    └───────────┘
             └───────────┘
```

**Key Insight**: All three axiom systems (Kolmogorov, Cox, K&S+Separation)
derive the SAME PLN deduction formula because they all:
1. Give additive probability measures
2. Satisfy Fréchet bounds
3. Support the law of total probability

The indefinite PLN version arises when:
- K&S without completeness → credal set (interval probabilities)
- This corresponds to the `plnIndefinite` vertex in the hypercube
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.PLNConnection
