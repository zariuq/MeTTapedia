import Mettapedia.InformationTheory.FiniteProbability
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite statistical Markov blankets

External and internal observations are conditionally independent given the
blanket. The conditional distribution of the external variables therefore
depends only on the blanket, not on internal observations. This is statistical
sufficiency at one time; temporal or interventional sufficiency requires a
separate dynamics contract.

References: Da Costa et al., *Bayesian mechanics for stationary processes*
(2021). The finite conditional-independence and information definitions are
shared with the information-theory development.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

variable {Ω E B I : Type*} [Fintype Ω] [Fintype E] [Fintype B] [Fintype I]
  [DecidableEq E] [DecidableEq B] [DecidableEq I]

/-- Statistical blanket sufficiency is exactly vanishing conditional information. -/
theorem conditionalInformation_eq_zero_iff (p : Prob Ω) (external : Ω → E)
    (blanket : Ω → B) (internal : Ω → I) :
    condMutualInfo p.1 external blanket internal = 0 ↔
      CondIndep p.1 external blanket internal :=
  condMutualInfo_eq_zero_iff p.1 p.2.1 external blanket internal

omit [Fintype I] [DecidableEq I] in
/-- Conditional distribution of the external observation given a possible blanket value. -/
noncomputable def externalGivenBlanket (p : Prob Ω) (external : Ω → E) (blanket : Ω → B)
    (b : B) (possible : 0 < pushforward p.1 blanket b) : Prob E :=
  ⟨fun e => law2 p.1 external blanket (e, b) / pushforward p.1 blanket b,
    (fun e => div_nonneg (pushforward_nonneg p.1 p.2.1 _ _) possible.le), by
      rw [← Finset.sum_div, sum_law2_left, div_self possible.ne']⟩

/-- Conditional external distribution given possible blanket and internal observations. -/
noncomputable def externalGivenBlanketInternal (p : Prob Ω) (external : Ω → E)
    (blanket : Ω → B) (internal : Ω → I) (b : B) (i : I)
    (possible : 0 < law2 p.1 blanket internal (b, i)) : Prob E :=
  ⟨fun e => law3 p.1 external blanket internal (e, b, i) / law2 p.1 blanket internal (b, i),
    (fun e => div_nonneg (pushforward_nonneg p.1 p.2.1 _ _) possible.le), by
      rw [← Finset.sum_div, sum_law3_left, div_self possible.ne']⟩

omit [Fintype B] in
/-- The conditional external posterior factors through the blanket observation. -/
theorem externalGivenBlanketInternal_eq (p : Prob Ω) (external : Ω → E)
    (blanket : Ω → B) (internal : Ω → I)
    (independent : CondIndep p.1 external blanket internal) (b : B) (i : I)
    (possible : 0 < law2 p.1 blanket internal (b, i)) :
    externalGivenBlanketInternal p external blanket internal b i possible =
      externalGivenBlanket p external blanket b
        (lt_of_lt_of_le possible (law2_le_pushforward_fst p.1 p.2.1 blanket internal (b, i))) := by
  apply Subtype.ext
  funext e
  change law3 p.1 external blanket internal (e, b, i) / law2 p.1 blanket internal (b, i) =
    law2 p.1 external blanket (e, b) / pushforward p.1 blanket b
  have hblanket : 0 < pushforward p.1 blanket b :=
    lt_of_lt_of_le possible (law2_le_pushforward_fst p.1 p.2.1 blanket internal (b, i))
  have h := independent (e, b, i)
  field_simp [possible.ne', hblanket.ne']
  simpa only [mul_comm] using h

omit [Fintype B] in
/-- Any expectation over external outcomes survives forgetting the internal observation. -/
theorem external_consumer_preserved (p : Prob Ω) (external : Ω → E)
    (blanket : Ω → B) (internal : Ω → I)
    (independent : CondIndep p.1 external blanket internal) (b : B) (i : I)
    (possible : 0 < law2 p.1 blanket internal (b, i)) (consumer : E → ℝ) :
    (∑ e, (externalGivenBlanketInternal p external blanket internal b i possible).1 e * consumer e) =
      ∑ e, (externalGivenBlanket p external blanket b
        (lt_of_lt_of_le possible (law2_le_pushforward_fst p.1 p.2.1 blanket internal (b, i)))).1 e * consumer e := by
  rw [externalGivenBlanketInternal_eq p external blanket internal independent]

end Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket
