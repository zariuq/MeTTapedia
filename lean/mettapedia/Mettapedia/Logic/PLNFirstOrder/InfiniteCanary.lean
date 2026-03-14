import Mettapedia.Logic.PLNFirstOrder.InfiniteSoundness

/-!
# Arbitrary-Domain PLN Quantifier Canary Suite

Regression-style canaries for the infinitary PLN quantifier layer.

The fixtures here use `Nat` as a genuinely infinite domain. The main mixed fixture
splits the domain into even and odd numbers, so it does not collapse to a finite-support
encoding while still remaining easy to reason about.
-/

namespace Mettapedia.Logic.PLNFirstOrder.Infinite

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

section ConcreteFixtures

/-- Infinite-domain mixed fixture: even numbers are classically true, odd numbers contradictory. -/
def natFixtureParity : SatisfyingSetInf Nat :=
  ⟨fun n => if n % 2 = 0 then (⟨1, 0⟩ : Evidence) else (⟨0, 1⟩ : Evidence)⟩

/-- Infinite-domain constant fixture for extensional canaries. -/
def natFixtureConst : SatisfyingSetInf Nat :=
  ⟨fun _ => (⟨2, 0⟩ : Evidence)⟩

/-- Uniform weight fixture over the infinite domain. -/
def natWeightUnit : WeightFunctionInf Nat Evidence :=
  ⟨fun _ => (⟨1, 0⟩ : Evidence)⟩

/-- Even numbers receive boosted positive evidence while odd numbers keep unit weight. -/
def natWeightBoostEven : WeightFunctionInf Nat Evidence :=
  ⟨fun n => if n % 2 = 0 then (⟨2, 0⟩ : Evidence) else (⟨1, 0⟩ : Evidence)⟩

/-- De Morgan canary on a genuinely infinite domain. -/
theorem canary_inf_nat_exists_deMorgan :
    thereExistsEvalInf natFixtureParity natWeightUnit =
      Evidence.compl (forAllEvalInf (SatisfyingSetInf.neg natFixtureParity) natWeightUnit) :=
  main_theorem_3_de_morgan_inf natFixtureParity natWeightUnit

/-- Pointwise comparison needed for the monotonicity canary. -/
theorem natWeightUnit_le_natWeightBoostEven (n : Nat) :
    natWeightUnit.μ n ≤ natWeightBoostEven.μ n := by
  by_cases h : n % 2 = 0 <;>
    simp [natWeightUnit, natWeightBoostEven, h, Evidence.le_def]

/-- Monotonicity canary using two honest weights over the infinite domain. -/
theorem canary_inf_nat_weight_monotonicity :
    forAllEvalInf SatisfyingSetInf.constantTrue natWeightUnit ≤
      forAllEvalInf SatisfyingSetInf.constantTrue natWeightBoostEven :=
  main_theorem_2_monotonicity_inf
    SatisfyingSetInf.constantTrue
    natWeightUnit
    natWeightBoostEven
    natWeightUnit_le_natWeightBoostEven

/-- Constant-predicate extensional canary over the infinite domain. -/
theorem canary_inf_nat_constant_extensional :
    forAllEvalExtInf natFixtureConst = (⟨2, 0⟩ : Evidence) ∧
      thereExistsEvalExtInf natFixtureConst = (⟨2, 0⟩ : Evidence) := by
  have hset :
      ({ e : Evidence | ∃ n : Nat, e = natFixtureConst.pred n } : Set Evidence) =
        ({ (⟨2, 0⟩ : Evidence) } : Set Evidence) := by
    ext e
    constructor
    · intro he
      rcases he with ⟨n, rfl⟩
      simp [natFixtureConst]
    · intro he
      simp only [Set.mem_singleton_iff] at he
      exact ⟨0, by simpa [natFixtureConst] using he⟩
  constructor
  · unfold forAllEvalExtInf
    rw [hset, sInf_singleton]
  · unfold thereExistsEvalExtInf
    rw [hset, sSup_singleton]

/-- The parity fixture only takes two values, but does so on infinitely many even and odd numbers. -/
theorem natFixtureParity_range :
    ({ e : Evidence | ∃ n : Nat, e = natFixtureParity.pred n } : Set Evidence) =
      ({ (⟨1, 0⟩ : Evidence), (⟨0, 1⟩ : Evidence) } : Set Evidence) := by
  ext e
  constructor
  · intro he
    rcases he with ⟨n, rfl⟩
    by_cases h : n % 2 = 0 <;> simp [natFixtureParity, h]
  · intro he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with h | h
    · exact ⟨0, by simpa [natFixtureParity] using h⟩
    · exact ⟨1, by simpa [natFixtureParity] using h⟩

/-- Extensional `∀` canary for the infinite parity fixture. -/
theorem canary_inf_nat_parity_forall_ext :
    forAllEvalExtInf natFixtureParity = (⟨0, 0⟩ : Evidence) := by
  unfold forAllEvalExtInf
  rw [natFixtureParity_range, sInf_pair]
  show Evidence.inf (⟨1, 0⟩ : Evidence) (⟨0, 1⟩ : Evidence) = (⟨0, 0⟩ : Evidence)
  unfold Evidence.inf
  apply Evidence.ext'
  · simp
  · simp

/-- Extensional `∃` canary for the infinite parity fixture. -/
theorem canary_inf_nat_parity_exists_ext :
    thereExistsEvalExtInf natFixtureParity = (⟨1, 1⟩ : Evidence) := by
  unfold thereExistsEvalExtInf
  rw [natFixtureParity_range, sSup_pair]
  show Evidence.sup (⟨1, 0⟩ : Evidence) (⟨0, 1⟩ : Evidence) = (⟨1, 1⟩ : Evidence)
  unfold Evidence.sup
  apply Evidence.ext'
  · simp
  · simp

/-- Extensional quantifiers remain ordered on the infinite parity fixture. -/
theorem canary_inf_nat_parity_forall_le_exists_ext :
    forAllEvalExtInf natFixtureParity ≤ thereExistsEvalExtInf natFixtureParity :=
  forAllEvalExtInf_le_thereExistsEvalExtInf natFixtureParity

/-- Negative canary: the extensional infinitary quantifiers are not equal on the parity fixture. -/
theorem canary_inf_nat_parity_non_equivalence_extensional :
    forAllEvalExtInf natFixtureParity ≠ thereExistsEvalExtInf natFixtureParity := by
  intro hEq
  have h0 : (⟨0, 0⟩ : Evidence) = (⟨1, 1⟩ : Evidence) := by
    rw [← canary_inf_nat_parity_forall_ext, ← canary_inf_nat_parity_exists_ext]
    exact hEq
  have hpos : (0 : ENNReal) = 1 := by
    simpa using congrArg Evidence.pos h0
  exact zero_ne_one hpos

end ConcreteFixtures

end Mettapedia.Logic.PLNFirstOrder.Infinite
