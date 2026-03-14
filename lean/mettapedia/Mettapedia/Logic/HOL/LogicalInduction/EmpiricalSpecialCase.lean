import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.HOL.LogicalInduction.WorldModelBridge
import Mettapedia.Logic.HOL.WorldModel

/-!
# Empirical Special Case of the HOL Logical-Induction Day Interface

This module relates the new logical-induction-ready day interface back to the
existing static HOL world-model semantics.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), a belief process should remain
separate from semantic truth.  Nevertheless, the current multiset-counting HOL
world-model semantics is an important empirical special case.

This file packages that special case by:

- turning a multiset of Henkin models into a single empirical belief day,
- showing singleton satisfying/non-satisfying models induce day prices `1/0`,
- and proving that the induced day-strength agrees with the existing static HOL
  query strength.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

private theorem countP_le_card
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (p : HenkinModel.{u, v, w} Base Const → Prop)
    [DecidablePred p] :
    Multiset.countP p W ≤ W.card := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      by_cases hp : p a
      · simpa [Multiset.countP_cons_of_pos, hp] using Nat.succ_le_succ ih
      · have hle : Multiset.countP p W ≤ W.card + 1 := Nat.le_succ_of_le ih
        simpa [Multiset.countP_cons_of_neg, hp] using hle

/-- Rational empirical price of a coded HOL formula under multiset-counting HOL semantics. -/
noncomputable def empiricalPrice
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormulaCode Const) : Price01 := by
  classical
  let p : HenkinModel.{u, v, w} Base Const → Prop :=
    fun M => holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)
  by_cases hcard : W.card = 0
  · exact Price01.zero
  · refine
      ⟨(Multiset.countP p W : Rat) / (W.card : Rat), ?_, ?_⟩
    · have hcard_pos : (0 : Rat) < W.card := by
        exact_mod_cast Nat.pos_of_ne_zero hcard
      positivity
    · have hp_le : Multiset.countP p W ≤ W.card := countP_le_card (Base := Base) (Const := Const) W p
      have hp_le_rat : (Multiset.countP p W : Rat) ≤ (W.card : Rat) := by
        exact_mod_cast hp_le
      have hcard_pos : (0 : Rat) < W.card := by
        exact_mod_cast Nat.pos_of_ne_zero hcard
      exact (div_le_one hcard_pos).2 hp_le_rat

/-- Empirical belief day induced by multiset-counting HOL semantics. -/
noncomputable def empiricalBeliefDay
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) : BeliefDay Const :=
  empiricalPrice (Base := Base) (Const := Const) W

@[simp] theorem empiricalBeliefDay_empty
    (φ : ClosedFormulaCode Const) :
    empiricalBeliefDay (Base := Base) (Const := Const)
      (0 : Multiset (HenkinModel.{u, v, w} Base Const)) φ = Price01.zero := by
  classical
  simp [empiricalBeliefDay, empiricalPrice]

private theorem holEvidence_total_eq_card
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormulaCode Const) :
    (holEvidence (Base := Base) (Const := Const) W (decodeClosedFormula φ)).total =
      (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const =>
              holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) W +
          Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const =>
              ¬ holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP
        (p := fun M : HenkinModel.{u, v, w} Base Const =>
          holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const =>
              holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) W : ℝ≥0∞) +
          (Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const =>
              ¬ holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold holEvidence Evidence.total
  simpa using hcard.symm

theorem staticQueryStrength_toReal_eq_empiricalPrice
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormulaCode Const) :
    (WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W (decodeClosedFormula φ)).toReal =
      (((empiricalBeliefDay (Base := Base) (Const := Const) W φ : Price01) : Rat) : Real) := by
  classical
  change
    (Evidence.toStrength
      (holEvidence (Base := Base) (Const := Const) W (decodeClosedFormula φ))).toReal =
      (((empiricalBeliefDay (Base := Base) (Const := Const) W φ : Price01) : Rat) : Real)
  by_cases hcard : W.card = 0
  · have hstrength :
        Evidence.toStrength
          (holEvidence (Base := Base) (Const := Const) W (decodeClosedFormula φ)) = 0 := by
      rw [Evidence.toStrength, holEvidence_total_eq_card (Base := Base) (Const := Const) W φ]
      simp [hcard]
    rw [hstrength]
    simp [empiricalBeliefDay, empiricalPrice, hcard]
  ·
    rw [Evidence.toStrength, holEvidence_total_eq_card (Base := Base) (Const := Const) W φ]
    have hcardENN : (W.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hcard
    rw [if_neg hcardENN, ENNReal.toReal_div]
    simp [holEvidence, empiricalBeliefDay, empiricalPrice, hcard]

theorem empiricalDayStrength_eq_staticQueryStrength
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormulaCode Const) :
    dayQueryStrength (Const := Const)
      (empiricalBeliefDay (Base := Base) (Const := Const) W) φ =
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W (decodeClosedFormula φ) := by
  have hleft :
      dayQueryStrength (Const := Const)
        (empiricalBeliefDay (Base := Base) (Const := Const) W) φ ≠ ⊤ := by
    simp [dayQueryStrength_eq_price]
  have hright_le :
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W (decodeClosedFormula φ) ≤ 1 := by
    change
      Evidence.toStrength
        (holEvidence (Base := Base) (Const := Const) W (decodeClosedFormula φ)) ≤ 1
    exact Evidence.toStrength_le_one _
  have hright :
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W (decodeClosedFormula φ) ≠ ⊤ := by
    intro htop
    have htop_le : (⊤ : ℝ≥0∞) ≤ 1 := by
      rw [htop] at hright_le
      exact hright_le
    have hnot : ¬ ((⊤ : ℝ≥0∞) ≤ 1) := by simp
    exact hnot htop_le
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  have hprice :
      (dayQueryStrength (Const := Const)
        (empiricalBeliefDay (Base := Base) (Const := Const) W) φ).toReal =
        (((empiricalBeliefDay (Base := Base) (Const := Const) W φ : Price01) : Rat) : Real) := by
    rw [dayQueryStrength_eq_price]
    exact ENNReal.toReal_ofReal (by
      exact_mod_cast
        (empiricalBeliefDay (Base := Base) (Const := Const) W φ).zero_le)
  rw [hprice]
  exact (staticQueryStrength_toReal_eq_empiricalPrice
    (Base := Base) (Const := Const) W φ).symm

theorem empiricalBeliefDay_singleton_of_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormulaCode Const)
    (hφ : holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) :
    empiricalBeliefDay (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = Price01.one := by
  have hstrength :
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
          (decodeClosedFormula φ) = 1 :=
    queryStrength_singleton_of_satisfies
      (Base := Base) (Const := Const) M (decodeClosedFormula φ) hφ
  have hday :
      dayQueryStrength (Const := Const)
          (empiricalBeliefDay
            (Base := Base) (Const := Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const))) φ = 1 := by
    rw [empiricalDayStrength_eq_staticQueryStrength
      (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ]
    exact hstrength
  have hnonneg :
      0 ≤
        (((empiricalBeliefDay
            (Base := Base) (Const := Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ : Price01) : Rat) : Real) := by
    exact_mod_cast
      (empiricalBeliefDay
        (Base := Base) (Const := Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ).zero_le
  have hreal :
      (((empiricalBeliefDay
          (Base := Base) (Const := Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ : Price01) : Rat) : Real) = 1 := by
    have htoReal := congrArg ENNReal.toReal hday
    rw [dayQueryStrength_eq_price, ENNReal.toReal_ofReal hnonneg] at htoReal
    simpa using htoReal
  apply Price01.ext
  exact_mod_cast hreal

theorem empiricalBeliefDay_singleton_of_not_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormulaCode Const)
    (hφ : ¬ holSatisfies (Base := Base) (Const := Const) M (decodeClosedFormula φ)) :
    empiricalBeliefDay (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = Price01.zero := by
  have hstrength :
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
          (decodeClosedFormula φ) = 0 :=
    queryStrength_singleton_of_not_satisfies
      (Base := Base) (Const := Const) M (decodeClosedFormula φ) hφ
  have hday :
      dayQueryStrength (Const := Const)
          (empiricalBeliefDay
            (Base := Base) (Const := Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const))) φ = 0 := by
    rw [empiricalDayStrength_eq_staticQueryStrength
      (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ]
    exact hstrength
  have hnonneg :
      0 ≤
        (((empiricalBeliefDay
            (Base := Base) (Const := Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ : Price01) : Rat) : Real) := by
    exact_mod_cast
      (empiricalBeliefDay
        (Base := Base) (Const := Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ).zero_le
  have hreal :
      (((empiricalBeliefDay
          (Base := Base) (Const := Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ : Price01) : Rat) : Real) = 0 := by
    have htoReal := congrArg ENNReal.toReal hday
    rw [dayQueryStrength_eq_price, ENNReal.toReal_ofReal hnonneg] at htoReal
    simpa using htoReal
  apply Price01.ext
  exact_mod_cast hreal

end Mettapedia.Logic.HOL.LogicalInduction
