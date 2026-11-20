import Mettapedia.ProbabilityTheory.StochasticInference.Finite

/-!
# Binary probability models

Bernoulli priors and two-sided conditional tables use the same factor
interface as arbitrary finite likelihoods. A transition contributes both
rows of its conditional table.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable

abbrev BinaryDomains (n : Nat) : Fin n → Nat := fun _ => 2

theorem binaryPositive (n : Nat) (v : Fin n) : 0 < BinaryDomains n v := Nat.zero_lt_succ 1

def bitValue (value : Bool) : Fin 2 := if value then 1 else 0

def bits {n : Nat} (x : Config (BinaryDomains n)) (v : Fin n) : Bool :=
  decide ((x v).val = 1)

structure UnitProbability where
  val : ℚ
  nonneg : 0 ≤ val
  le_one : val ≤ 1
  deriving DecidableEq

def UnitProbability.checked (value : ℚ) : Option UnitProbability :=
  if valid : 0 ≤ value ∧ value ≤ 1 then some ⟨value, valid.1, valid.2⟩ else none

def UnitProbability.atOutcome (p : UnitProbability) (outcome : Bool) : ℚ :=
  if outcome then p.val else 1 - p.val

theorem UnitProbability.atOutcome_nonneg (p : UnitProbability) (outcome : Bool) :
    0 ≤ p.atOutcome outcome := by
  cases outcome
  · exact sub_nonneg.mpr p.le_one
  · exact p.nonneg

@[simp] theorem UnitProbability.outcomes_sum (p : UnitProbability) :
    p.atOutcome false + p.atOutcome true = 1 := by
  simp [atOutcome]

def binaryEvent {n : Nat} (v : Fin n) (value : Bool) : Event (BinaryDomains n) :=
  Event.equalTo (binaryPositive n) v (bitValue value)

def bernoulli {n : Nat} (v : Fin n) (p : UnitProbability) : Potential (BinaryDomains n) :=
  Potential.onScope (binaryPositive n) [v] (by simp)
    (fun x => p.atOutcome (decide ((x v (by simp)).val = 1)))
    (fun _ => p.atOutcome_nonneg _)

theorem bernoulli_value {n : Nat} (v : Fin n) (p : UnitProbability)
    (x : Config (BinaryDomains n)) :
    (bernoulli v p).table.value _ (binaryPositive n) x = p.atOutcome (bits x v) :=
  tableOnScope_value _ _ _ _ _

/-- The child has success probability `p` with a true parent and `q` with
a false parent. The roles occupy distinct coordinates. -/
def binaryTransition {n : Nat} (parent child : Fin n) (distinct : parent ≠ child)
    (p q : UnitProbability) : Potential (BinaryDomains n) :=
  Potential.onScope (binaryPositive n) [parent, child] (by simp [distinct])
    (fun x => (if (x parent (by simp)).val = 1 then p else q).atOutcome
      (decide ((x child (by simp)).val = 1))) (fun _ => UnitProbability.atOutcome_nonneg _ _)

theorem binaryTransition_value {n : Nat} (parent child : Fin n) (distinct : parent ≠ child)
    (p q : UnitProbability) (x : Config (BinaryDomains n)) :
    (binaryTransition parent child distinct p q).table.value _ (binaryPositive n) x =
      (if bits x parent then p else q).atOutcome (bits x child) := by
  rw [binaryTransition, Potential.onScope, tableOnScope_value]
  simp [bits]

end Mettapedia.ProbabilityTheory.StochasticInference
