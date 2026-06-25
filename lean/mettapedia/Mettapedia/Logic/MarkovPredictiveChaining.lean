import Mettapedia.Logic.WMMarkovCanonical
import Mettapedia.Logic.WMMarkov
import Mathlib.Data.Fintype.BigOperators

/-!
# Markov Predictive Chaining via WM Dirichlet Posteriors

This file formalizes the honest multi-step Markov chaining story on the
predictive side:

* one-step transition prediction comes from the active row posterior;
* hypothetical transitions update the Markov summary via `TransCounts.bump`;
* multi-step chaining is sequential predictive composition, not additive pooling.
-/

noncomputable section

namespace Mettapedia.Logic.MarkovPredictiveChaining

open Mettapedia.Logic
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.Logic.WMMarkovCanonical
open Mettapedia.UniversalAI.UniversalPrediction

open scoped BigOperators ENNReal

variable {k : ℕ}

/-- WM-side sequential predictive chain from a current state `prev` and
transition-count summary `c`. Each hypothetical next state updates the summary
before the rest of the future path is predicted. -/
noncomputable def markovWMPosteriorChain
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) :
    List (Fin k) → ENNReal
  | [] => 1
  | next :: ys =>
      ENNReal.ofReal
        ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) *
        markovWMPosteriorChain hk prior next (TransCounts.bump c prev next) ys

@[simp] theorem markovWMPosteriorChain_nil
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) :
    markovWMPosteriorChain hk prior prev c [] = 1 :=
  rfl

@[simp] theorem markovWMPosteriorChain_cons
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev next : Fin k) (c : TransCounts k) (ys : List (Fin k)) :
    markovWMPosteriorChain hk prior prev c (next :: ys) =
      ENNReal.ofReal
        ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) *
        markovWMPosteriorChain hk prior next (TransCounts.bump c prev next) ys :=
  rfl

/-- The WM-side sequential chain agrees exactly with the Markov-Dirichlet
predictive recursion already formalized as `prefixAux`. -/
theorem markovWMPosteriorChain_eq_prefixAux
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) :
    ∀ ys : List (Fin k),
      markovWMPosteriorChain hk prior prev c ys =
        Mettapedia.UniversalAI.UniversalPrediction.MarkovDirichlet.prefixAux
          (k := k) prior prev c ys := by
  intro ys
  induction ys generalizing prev c with
  | nil =>
      rfl
  | cons next ys ih =>
      simp [markovWMPosteriorChain, Mettapedia.UniversalAI.UniversalPrediction.MarkovDirichlet.prefixAux,
        rowEvidence_posteriorMean_eq_stepProb, ih]

/-- Every predictive chain weight is a subprobability mass. This is the key
bound needed when packaging predictive chains as query-mass semantics. -/
theorem markovWMPosteriorChain_le_one
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) :
    ∀ ys : List (Fin k), markovWMPosteriorChain hk prior prev c ys ≤ 1 := by
  intro ys
  induction ys generalizing prev c with
  | nil =>
      simp [markovWMPosteriorChain]
  | cons next ys ih =>
      have hstep_unit :
          ENNReal.ofReal
              ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) ≤ 1 := by
        have hmean_unit :
            (⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next ≤ 1 :=
          (EvidenceDirichletParams.posteriorMean_mem_unit
            (p := ⟨prior prev, rowEvidence c prev⟩) hk next).2
        simpa using ENNReal.ofReal_le_ofReal hmean_unit
      have htail :
          markovWMPosteriorChain hk prior next (TransCounts.bump c prev next) ys ≤ 1 :=
        ih (prev := next) (c := TransCounts.bump c prev next)
      calc
        markovWMPosteriorChain hk prior prev c (next :: ys)
            = ENNReal.ofReal
                ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) *
              markovWMPosteriorChain hk prior next (TransCounts.bump c prev next) ys := by
                simp [markovWMPosteriorChain]
        _ ≤ ENNReal.ofReal
              ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) * 1 := by
                exact mul_le_mul_right htail _
        _ = ENNReal.ofReal
              ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next) := by
                simp
        _ ≤ 1 := hstep_unit

/-- Two-step WM chain expands into the expected product of the first-step row
posterior and the second-step posterior after updating with the intermediate
transition. -/
theorem markovWMPosteriorChain_twoStep
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev mid dst : Fin k) (c : TransCounts k) :
    markovWMPosteriorChain hk prior prev c [mid, dst] =
      ENNReal.ofReal
        ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk mid) *
      ENNReal.ofReal
        ((⟨prior mid, rowEvidence (TransCounts.bump c prev mid) mid⟩ :
            EvidenceDirichletParams k).posteriorMean hk dst) := by
  simp [markovWMPosteriorChain]

/-- Total predictive mass of arriving at `dst` in exactly two future steps,
starting from the current state `prev` and summary `c`. -/
noncomputable def markovTwoStepArrivalMass
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) (dst : Fin k) : ENNReal :=
  ∑ mid : Fin k, markovWMPosteriorChain hk prior prev c [mid, dst]

/-- The two-step arrival mass is the sum of the underlying Markov-Dirichlet
predictive chain weights. -/
theorem markovTwoStepArrivalMass_eq_prefixAux_sum
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) (dst : Fin k) :
    markovTwoStepArrivalMass hk prior prev c dst =
      ∑ mid : Fin k,
        Mettapedia.UniversalAI.UniversalPrediction.MarkovDirichlet.prefixAux
          (k := k) prior prev c [mid, dst] := by
  simp [markovTwoStepArrivalMass, markovWMPosteriorChain_eq_prefixAux]

/-- The two-step arrival mass can be read as a sum of posterior-mean products:
first-step prediction from the current row, then second-step prediction from the
updated row indexed by the realized intermediate state. -/
theorem markovTwoStepArrivalMass_eq_posteriorMean_sum
    (hk : 0 < k) (prior : Fin k → DirichletParams k)
    (prev : Fin k) (c : TransCounts k) (dst : Fin k) :
    markovTwoStepArrivalMass hk prior prev c dst =
      ∑ mid : Fin k,
        ENNReal.ofReal
          ((⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk mid) *
        ENNReal.ofReal
          ((⟨prior mid, rowEvidence (TransCounts.bump c prev mid) mid⟩ :
              EvidenceDirichletParams k).posteriorMean hk dst) := by
  simp [markovTwoStepArrivalMass]

abbrev bit0 : Fin 2 := ⟨0, by decide⟩
abbrev bit1 : Fin 2 := ⟨1, by decide⟩

/-- Binary example: in the `k = 2` case, two-step arrival mass expands into the
two concrete intermediate-state branches. -/
theorem binary_markovTwoStepArrivalMass_expand
    (hk : 0 < 2) (prior : Fin 2 → DirichletParams 2)
    (prev dst : Fin 2) (c : TransCounts 2) :
    markovTwoStepArrivalMass (k := 2) hk prior prev c dst =
      markovWMPosteriorChain (k := 2) hk prior prev c [bit0, dst] +
      markovWMPosteriorChain (k := 2) hk prior prev c [bit1, dst] := by
  simp [markovTwoStepArrivalMass, bit0, bit1, Fin.sum_univ_two]

/-- Binary example: the `k = 2` two-step arrival mass is the sum of exactly two
Markov-Dirichlet path weights. -/
theorem binary_markovTwoStepArrivalMass_eq_prefixAux_expand
    (hk : 0 < 2) (prior : Fin 2 → DirichletParams 2)
    (prev dst : Fin 2) (c : TransCounts 2) :
    markovTwoStepArrivalMass (k := 2) hk prior prev c dst =
      Mettapedia.UniversalAI.UniversalPrediction.MarkovDirichlet.prefixAux
        (k := 2) prior prev c [bit0, dst] +
      Mettapedia.UniversalAI.UniversalPrediction.MarkovDirichlet.prefixAux
        (k := 2) prior prev c [bit1, dst] := by
  rw [binary_markovTwoStepArrivalMass_expand (hk := hk) (prior := prior) (prev := prev)
    (dst := dst) (c := c)]
  rw [markovWMPosteriorChain_eq_prefixAux (k := 2) hk prior prev c [bit0, dst]]
  rw [markovWMPosteriorChain_eq_prefixAux (k := 2) hk prior prev c [bit1, dst]]

end Mettapedia.Logic.MarkovPredictiveChaining
