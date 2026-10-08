import Mettapedia.SetTheory.CarveOuts.HeytingValued.Gunky
import Mathlib.Data.ENNReal.Inv

/-!
# A free point does not collapse to the ground

The frame `[0, ∞]` (a complete chain) has the point "positive" (`positivePoint`): it affirms
exactly the values above `0`. The point is not principal (`positivePoint_not_principal`): no
least positive value exists. It passes through double negation
(`positivePoint_holds_compl_compl`), so it is a point of the double-negation part.

At this point the two-valued reading and the truth values part ways on a bounded universal.
Let `x` be the name whose members are `{∅ ↦ 1/n}` for every `n`. The sentence
`∀ z ∈ x, ∅ ∈ z` has value `⨅ n, 1/n = 0` (`eval_allContainEmpty`), which the point does not
affirm; but in the two-valued reading at the point every member of `x` contains `∅`
(`positivePoint_reads`). So positive truth transfers to every point
(`Point.holds_eval_iff_of_positive`), all bounded truth transfers at an atom
(`Name.le_eval_iff_zfHolds`), and here a free point fails the bounded universal
(`free_point_ball_gap`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.HeytingValued

open scoped ENNReal

/-- The point of `[0, ∞]` affirming exactly the positive values. -/
def positivePoint : Point ℝ≥0∞ where
  holds h := 0 < h
  holds_top := ENNReal.zero_lt_top
  holds_inf _ _ := lt_inf_iff
  holds_sSup _ := lt_sSup_iff

/-- **The positive point is free: it has no least positive value.** -/
theorem positivePoint_not_principal : ¬ positivePoint.IsPrincipal := by
  rintro ⟨a, ha⟩
  have hpos : 0 < a := (ha a).mpr le_rfl
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
  have : a ≤ (n : ℝ≥0∞)⁻¹ := (ha _).mp (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n))
  exact absurd hn (not_lt.mpr this)

/-- Negation in `[0, ∞]`: `⊤` at `0`, and `0` elsewhere. -/
theorem ennreal_compl (h : ℝ≥0∞) : hᶜ = if h = 0 then ⊤ else 0 := by
  rw [← himp_bot]
  show (if h ≤ ⊥ then ⊤ else ⊥) = _
  simp only [bot_eq_zero, nonpos_iff_eq_zero]
  rfl

theorem ennreal_compl_compl (h : ℝ≥0∞) : hᶜᶜ = if h = 0 then 0 else ⊤ := by
  rw [ennreal_compl h]
  by_cases h0 : h = 0
  · rw [if_pos h0, if_pos h0, ennreal_compl, if_neg ENNReal.top_ne_zero]
  · rw [if_neg h0, if_neg h0, ennreal_compl, if_pos rfl]

/-- The positive point passes through double negation. -/
theorem positivePoint_holds_compl_compl (h : ℝ≥0∞) :
    positivePoint.holds hᶜᶜ ↔ positivePoint.holds h := by
  show 0 < hᶜᶜ ↔ 0 < h
  rw [ennreal_compl_compl]
  by_cases h0 : h = 0
  · rw [if_pos h0, h0]
  · rw [if_neg h0]
    exact ⟨fun _ => pos_iff_ne_zero.mpr h0, fun _ => ENNReal.zero_lt_top⟩

theorem iInf_inv_nat : (⨅ n : ℕ, (n : ℝ≥0∞)⁻¹) = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
  exact absurd (iInf_le _ n) (not_le.mpr hn)

/-- The name whose members are `{∅ ↦ 1/n}`, each with full weight. -/
noncomputable def descending : Name ℝ≥0∞ :=
  Name.mk ℕ (fun n => Name.truthName ((n : ℝ≥0∞)⁻¹)) (fun _ => ⊤)

/-- `∀ z ∈ x₀, ∅ ∈ z`, where `x₁` is `∅`. -/
def allContainEmpty : BFormula 2 :=
  .ball 0 (.mem 2 0)

/-- `x₀ = descending`, `x₁ = ∅`. -/
noncomputable def descendingAssign : Fin 2 → Name ℝ≥0∞ :=
  ![descending, Name.empty]

theorem eval_allContainEmpty :
    Name.eval allContainEmpty descendingAssign = ⨅ n : ℕ, (n : ℝ≥0∞)⁻¹ := by
  show (⨅ n : ℕ, (⊤ : ℝ≥0∞) ⇨ Name.mem Name.empty (Name.truthName ((n : ℝ≥0∞)⁻¹))) = _
  simp only [top_himp, Name.mem_empty_truthName]

theorem positivePoint_reads : positivePoint.reads allContainEmpty descendingAssign := by
  intro z hz
  change 0 < Name.mem z descending at hz
  change 0 < Name.mem Name.empty z
  rw [descending, Name.mem_mk] at hz
  obtain ⟨n, hn⟩ := (positivePoint.holds_iSup _).mp hz
  have heq : positivePoint.holds (Name.eq (Name.truthName ((n : ℝ≥0∞)⁻¹)) z) := by
    rw [Name.eq_comm]
    exact ((positivePoint.holds_inf _ _).mp hn).2
  have hmem : positivePoint.holds (Name.mem Name.empty (Name.truthName ((n : ℝ≥0∞)⁻¹))) := by
    rw [Name.mem_empty_truthName]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  exact positivePoint.holds_mono (Name.eq_inf_mem_le_right _ _ _)
    ((positivePoint.holds_inf _ _).mpr ⟨heq, hmem⟩)

/-- **A free point fails a bounded universal.** The two-valued reading at the positive point
satisfies `∀ z ∈ x, ∅ ∈ z`, and the point does not affirm the sentence's truth value. -/
theorem free_point_ball_gap :
    positivePoint.reads allContainEmpty descendingAssign ∧
      ¬ positivePoint.holds (Name.eval allContainEmpty descendingAssign) := by
  refine ⟨positivePoint_reads, ?_⟩
  rw [eval_allContainEmpty, iInf_inv_nat]
  exact lt_irrefl 0

end Mettapedia.SetTheory.CarveOuts.HeytingValued
