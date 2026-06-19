import Mettapedia.Logic.PLNDerivation

/-!
# PLN Bayes / Inversion Bridge

PLN's book-level "Inversion" surface has two nearby readings:

* the historical compiled-rule catalog keeps the implication strength unchanged;
* the probabilistic WM-calc reading is Bayes inversion, using the base rates.

This file exposes the WM-facing Bayes version as a small guarded bridge.  It is
the same `bayesInversion` already used by induction and abduction; no new
inference semantics are introduced here.
-/

namespace Mettapedia.Logic.PLN

/-- Bayes inversion of an `A → B` strength into a `B → A` strength:

`P(A|B) = P(B|A) * P(A) / P(B)`.
-/
noncomputable def plnInversionBayesStrength
    (sAB pA pB : ℝ) : ℝ :=
  bayesInversion sAB pB pA

/-- The admissibility guard for using Bayes inversion as a probability-valued
PLN rule.  The final inequality is exactly the joint-probability constraint
`P(A ∩ B) = P(B|A) P(A) ≤ P(B)`. -/
def BayesInversionAdmissible
    (sAB pA pB : ℝ) : Prop :=
  0 ≤ sAB ∧ sAB ≤ 1 ∧
    0 ≤ pA ∧ pA ≤ 1 ∧
    0 < pB ∧ pB ≤ 1 ∧
    sAB * pA ≤ pB

@[simp] theorem plnInversionBayesStrength_eq
    (sAB pA pB : ℝ) :
    plnInversionBayesStrength sAB pA pB =
      sAB * pA / pB := rfl

/-- Bayes inversion reconstructs the same joint probability after multiplying
back by the target base rate. -/
theorem plnInversionBayesStrength_joint_eq
    (sAB pA pB : ℝ) (hpB : pB ≠ 0) :
    plnInversionBayesStrength sAB pA pB * pB = sAB * pA := by
  unfold plnInversionBayesStrength bayesInversion
  field_simp [hpB]

/-- The guarded Bayes inversion output is a probability. -/
theorem plnInversionBayesStrength_mem_Icc
    (sAB pA pB : ℝ)
    (h : BayesInversionAdmissible sAB pA pB) :
    plnInversionBayesStrength sAB pA pB ∈ Set.Icc (0 : ℝ) 1 := by
  rcases h with ⟨hsAB0, hsAB1, hpA0, hpA1, hpB0, hpB1, hjoint⟩
  constructor
  · unfold plnInversionBayesStrength bayesInversion
    exact div_nonneg (mul_nonneg hsAB0 hpA0) (le_of_lt hpB0)
  · exact bayesInversion_bounded sAB pB pA
      ⟨hsAB0, hsAB1⟩ hpB0 ⟨hpA0, hpA1⟩ hjoint

/-- Equal base rates are the special case where the catalog same-strength
inversion agrees with the Bayes inversion. -/
theorem plnInversionBayesStrength_eq_catalog_of_equal_base_rate
    (sAB p : ℝ) (hp : p ≠ 0) :
    plnInversionBayesStrength sAB p p = sAB := by
  unfold plnInversionBayesStrength bayesInversion
  field_simp [hp]

/-- Positive canary: a feasible inversion with unequal base rates.  The raw
strength `4/5` inverts to `2/5`, remains in `[0,1]`, and reconstructs the same
joint mass. -/
theorem plnInversionBayesStrength_feasible_canary :
    BayesInversionAdmissible (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) ∧
      plnInversionBayesStrength (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) =
        (2 / 5 : ℝ) ∧
      plnInversionBayesStrength (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) ∈
        Set.Icc (0 : ℝ) 1 ∧
      plnInversionBayesStrength (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) *
          (1 / 2 : ℝ) =
        (4 / 5 : ℝ) * (1 / 4 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [BayesInversionAdmissible]
  · norm_num [plnInversionBayesStrength, bayesInversion]
  · exact plnInversionBayesStrength_mem_Icc
      (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) (by
        norm_num [BayesInversionAdmissible])
  · norm_num [plnInversionBayesStrength, bayesInversion]

/-- Negative canary: catalog inversion is not Bayes inversion in general.  It
agrees only under extra base-rate conditions, not as a theorem of inversion
itself. -/
theorem plnInversion_catalog_ne_bayes_canary :
    (4 / 5 : ℝ) ≠
      plnInversionBayesStrength (4 / 5 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  norm_num [plnInversionBayesStrength, bayesInversion]

/-- Guardrail canary: without the joint-probability constraint, Bayes inversion
can leave the unit interval.  This is why the rule is explicitly guarded. -/
theorem plnInversionBayesStrength_invalid_constraint_canary :
    ¬ BayesInversionAdmissible (4 / 5 : ℝ) (3 / 4 : ℝ) (1 / 4 : ℝ) ∧
      plnInversionBayesStrength (4 / 5 : ℝ) (3 / 4 : ℝ) (1 / 4 : ℝ) =
        (12 / 5 : ℝ) ∧
      (1 : ℝ) <
        plnInversionBayesStrength (4 / 5 : ℝ) (3 / 4 : ℝ) (1 / 4 : ℝ) := by
  norm_num [BayesInversionAdmissible, plnInversionBayesStrength, bayesInversion]

end Mettapedia.Logic.PLN
