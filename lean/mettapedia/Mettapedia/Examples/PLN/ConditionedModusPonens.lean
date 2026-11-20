import Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
import Mettapedia.ProbabilityTheory.BayesianNetworks.ConditionedKernel
import Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorQueries

/-!
# Two-sided modus ponens after downstream evidence

A binary chain supplies an executable comparison with the calculus of
scored edge kernels. A separate shared-effect observation tests whether
independent source facts remain independent in the posterior.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.ConditionedModusPonens

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceRules
open Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions
open Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.BayesianNetworks
open ConditionedKernel ExecutableFactorTable ScopedFactorReadout
open FiniteFunctionalExtension FiniteWeightedExtension
open scoped NNReal ENNReal BigOperators

/-- Changing only the background branch isolates its effect on strength. -/
theorem background_branch_change (source implication : TV) (q : ℝ) :
    modusPonens implication.s source.s q - (truthModusPonens source implication).s =
      (q - 1 / 50) * (1 - source.s) := by
  norm_num [truthModusPonens, modusPonens]
  ring

def domains (_ : Fin 3) : Nat := 2

theorem positive (v : Fin 3) : 0 < domains v := by simp [domains]

def present (v : Fin 3) : Constraint domains := ⟨v, ⟨1, by simp [domains]⟩⟩

def fairBit (v : Fin 3) : Table domains :=
  tabulate domains positive [v] (by simp) fun _ => 1 / 2

/-- One complete conditional probability table for a binary edge. -/
def edge (parent child : Fin 3) (distinct : parent ≠ child) (p q : ℚ) : Table domains :=
  tabulate domains positive [parent, child] (by simp [distinct]) fun cfg =>
    let rate := if (cfg parent).val = 1 then p else q
    if (cfg child).val = 1 then rate else 1 - rate

def read (tables : List (Table domains)) (observed query : List (Constraint domains)) : Option ℚ :=
  (conditionalMasses? positive tables observed query [0, 1, 2]).bind Masses.posterior?

def chain : List (Table domains) :=
  [fairBit 0, edge 0 1 (by decide) (4 / 5) (1 / 10),
    edge 1 2 (by decide) (9 / 10) (1 / 10)]

theorem prediction : read chain [] [present 1] = some (9 / 20) := by decide +kernel

theorem parent_given_effect :
    read chain [present 2] [present 0] = some (37 / 46) := by decide +kernel

theorem child_given_effect :
    read chain [present 2] [present 1] = some (81 / 92) := by decide +kernel

theorem reuse_original_rows :
    modusPonens (4 / 5) (37 / 46) (1 / 10) = 61 / 92 := by
  norm_num [modusPonens]

noncomputable def originalRates (a : Bool) : ℝ≥0 :=
  if a then 4 / 5 else 1 / 10

noncomputable def effectLikelihood (b : Bool) : ℝ≥0 :=
  if b then 9 / 10 else 1 / 10

theorem updated_rows :
    normalizeRows (score (bernoulli originalRates) effectLikelihood) true true = 36 / 37 ∧
    normalizeRows (score (bernoulli originalRates) effectLikelihood) false true = 1 / 2 := by
  have hp : (4 / 5 : ℝ≥0) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num [NNReal.coe_div]
  have hq : (1 / 10 : ℝ≥0) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num [NNReal.coe_div]
  constructor <;> apply NNReal.coe_injective <;>
    norm_num [normalizeRows, rowMass, score, bernoulli, originalRates, effectLikelihood,
      Fintype.sum_bool, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_sub hp, NNReal.coe_sub hq]

theorem corrected_modus_ponens :
    modusPonens (36 / 37) (37 / 46) (1 / 2) = 81 / 92 := by
  norm_num [modusPonens]

/-- Conditioning can couple two initially independent sources. -/
def eitherSource : Table domains :=
  tabulate domains positive [0, 1] (by decide) fun cfg =>
    if (cfg 0).val = 1 ∨ (cfg 1).val = 1 then 1 else 0

theorem shared_effect_couples_source_facts :
    read [fairBit 0, fairBit 1] [] [present 0, present 1] = some (1 / 4) ∧
    read [fairBit 0, fairBit 1, eitherSource] [] [present 0] = some (2 / 3) ∧
    read [fairBit 0, fairBit 1, eitherSource] [] [present 1] = some (2 / 3) ∧
    read [fairBit 0, fairBit 1, eitherSource] [] [present 0, present 1] = some (1 / 3) ∧
    (2 / 3 : ℚ) * (2 / 3) ≠ 1 / 3 := by decide +kernel

/-- A zero parent branch can coexist with a supported child posterior. -/
theorem impossible_branch :
    read [fairBit 0, edge 0 1 (by decide) (1 / 2) 0] [present 1] [present 0] = some 1 ∧
    read [fairBit 0, edge 0 1 (by decide) 0 0] [present 1] [present 0] = none := by
  decide +kernel

end Mettapedia.Examples.PLN.ConditionedModusPonens
