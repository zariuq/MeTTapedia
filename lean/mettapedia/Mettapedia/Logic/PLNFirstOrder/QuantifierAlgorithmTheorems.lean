import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemantics

/-!
# Chapter-11 Quantifier Algorithm Theorem Pack

Theorems about the algorithmic quantifier layer itself:

1. Parameter monotonicity (`ε`, `PCL`, `LPC`, `UPC`).
2. Crisp-as-fuzzy endpoint characterizations.
3. Rule-4 discrepancy bounds for conjunction-vs-quantification interaction.
-/

namespace Mettapedia.Logic.PLNFirstOrder

section ParameterMonotonicity

variable {U : Type*} [Fintype U]

/-- Increasing `ε` weakens `nearOne` strictness (membership monotonicity). -/
theorem nearOne_mono_of_epsilon_le
    (p₁ p₂ : FuzzyQuantifierParams) (x : ℝ)
    (hε : p₁.ε ≤ p₂.ε)
    (hx : nearOne p₁ x) :
    nearOne p₂ x := by
  unfold nearOne at *
  constructor
  · linarith [hx.1, hε]
  · exact hx.2

/-- Increasing `ε` weakens `nearZero` strictness (membership monotonicity). -/
theorem nearZero_mono_of_epsilon_le
    (p₁ p₂ : FuzzyQuantifierParams) (x : ℝ)
    (hε : p₁.ε ≤ p₂.ε)
    (hx : nearZero p₁ x) :
    nearZero p₂ x := by
  unfold nearZero at *
  constructor
  · exact hx.1
  · exact le_trans hx.2 hε

/-- Increasing `ε` can only increase the `nearOne` witness mass. -/
theorem nearOneFraction_mono_of_epsilon_le
    (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε : p₁.ε ≤ p₂.ε) :
    nearOneFraction p₁ profile ≤ nearOneFraction p₂ profile := by
  classical
  unfold nearOneFraction
  exact witnessFraction_mono
    (pred₁ := fun u => nearOne p₁ (profile u))
    (pred₂ := fun u => nearOne p₂ (profile u))
    (hImpl := by
      intro u hu
      exact nearOne_mono_of_epsilon_le p₁ p₂ (profile u) hε hu)

/-- Increasing `ε` can only increase fuzzy existential score. -/
theorem fuzzyExistsScore_mono_of_epsilon_le
    (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε : p₁.ε ≤ p₂.ε) :
    fuzzyExistsScore p₁ profile ≤ fuzzyExistsScore p₂ profile := by
  unfold fuzzyExistsScore
  exact nearOneFraction_mono_of_epsilon_le p₁ p₂ profile hε

/-- Increasing `ε` and relaxing `PCL` preserves fuzzy-`ForAll` truth. -/
theorem fuzzyForAllHolds_of_epsilon_and_PCL_relax
    (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε : p₁.ε ≤ p₂.ε)
    (hPCL : p₂.PCL ≤ p₁.PCL)
    (hForAll : fuzzyForAllHolds p₁ profile) :
    fuzzyForAllHolds p₂ profile := by
  unfold fuzzyForAllHolds at *
  exact le_trans hPCL (le_trans hForAll (nearOneFraction_mono_of_epsilon_le p₁ p₂ profile hε))

/-- Equal `ε` gives identical `nearOne` witness mass. -/
  theorem nearOneFraction_eq_of_epsilon_eq
      (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
      (hε : p₁.ε = p₂.ε) :
      nearOneFraction p₁ profile = nearOneFraction p₂ profile := by
  have h12 : nearOneFraction p₁ profile ≤ nearOneFraction p₂ profile := by
    exact nearOneFraction_mono_of_epsilon_le p₁ p₂ profile (by simp [hε])
  have h21 : nearOneFraction p₂ profile ≤ nearOneFraction p₁ profile := by
    exact nearOneFraction_mono_of_epsilon_le p₂ p₁ profile (by simp [hε])
  exact le_antisymm h12 h21

/-- Widening `[LPC, UPC]` preserves interval acceptance (with same `ε`). -/
theorem fuzzyIntervalHolds_of_wider_bounds
    (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε : p₁.ε = p₂.ε)
    (hL : p₂.LPC ≤ p₁.LPC)
    (hU : p₁.UPC ≤ p₂.UPC)
    (hInt : fuzzyIntervalHolds p₁ profile) :
    fuzzyIntervalHolds p₂ profile := by
  have hFrac : nearOneFraction p₁ profile = nearOneFraction p₂ profile :=
    nearOneFraction_eq_of_epsilon_eq p₁ p₂ profile hε
  unfold fuzzyIntervalHolds at *
  constructor
  · have hLeft : p₂.LPC ≤ nearOneFraction p₁ profile := le_trans hL hInt.1
    simpa [hFrac] using hLeft
  · have hRight : nearOneFraction p₁ profile ≤ p₂.UPC := le_trans hInt.2 hU
    simpa [hFrac] using hRight

/-- Lowering `PCL` preserves fuzzy-`ForAll` acceptance (with same `ε`). -/
theorem fuzzyForAllHolds_of_lowerPCL_sameEpsilon
    (p₁ p₂ : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε : p₁.ε = p₂.ε)
    (hPCL : p₂.PCL ≤ p₁.PCL)
    (hForAll : fuzzyForAllHolds p₁ profile) :
    fuzzyForAllHolds p₂ profile := by
  have hFrac : nearOneFraction p₁ profile = nearOneFraction p₂ profile :=
    nearOneFraction_eq_of_epsilon_eq p₁ p₂ profile hε
  unfold fuzzyForAllHolds at *
  have hMain : p₂.PCL ≤ nearOneFraction p₁ profile := le_trans hPCL hForAll
  simpa [hFrac] using hMain

end ParameterMonotonicity

section CrispEndpoints

variable {U : Type*} [Fintype U]

theorem witnessFraction_false :
    witnessFraction (U := U) (fun _ : U => False) = 0 := by
  unfold witnessFraction witnessCount
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0]

theorem witnessFraction_true [Nonempty U] :
    witnessFraction (U := U) (fun _ : U => True) = 1 := by
  unfold witnessFraction witnessCount
  have h0 : Fintype.card U ≠ 0 := by
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty U›)
  simp [h0]

/-- Crisp endpoint: `PCL = 1` turns fuzzy `ForAll` into exact full witness mass. -/
theorem fuzzyForAllHolds_iff_fraction_eq_one_of_PCL_eq_one
    (p : FuzzyQuantifierParams) (profile : U → ℝ)
    (hPCL : p.PCL = 1) :
    fuzzyForAllHolds p profile ↔ nearOneFraction p profile = 1 := by
  constructor
  · intro hForAll
    unfold fuzzyForAllHolds at hForAll
    have hge : (1 : ℝ) ≤ nearOneFraction p profile := by simpa [hPCL] using hForAll
    have hle : nearOneFraction p profile ≤ 1 := (nearOneFraction_in_unit p profile).2
    exact le_antisymm hle hge
  · intro hEq
    unfold fuzzyForAllHolds
    rw [hPCL, hEq]

/-- Crisp endpoint: `PCL = 1` turns fuzzy `ThereExists` into zero near-zero mass. -/
theorem fuzzyThereExistsHolds_iff_nearZeroFraction_eq_zero_of_PCL_eq_one
    (p : FuzzyQuantifierParams) (profile : U → ℝ)
    (hPCL : p.PCL = 1) :
    fuzzyThereExistsHolds p profile ↔ nearZeroFraction p profile = 0 := by
  constructor
  · intro hEx
    unfold fuzzyThereExistsHolds at hEx
    have hge : (1 : ℝ) ≤ 1 - nearZeroFraction p profile := by simpa [hPCL] using hEx
    have hle0 : nearZeroFraction p profile ≤ 0 := by linarith
    have hge0 : 0 ≤ nearZeroFraction p profile := (nearZeroFraction_in_unit p profile).1
    exact le_antisymm hle0 hge0
  · intro hZero
    unfold fuzzyThereExistsHolds
    rw [hPCL, hZero]
    norm_num

/-- Crisp endpoint theorem:
at `ε = 0` and `PCL = 1`, fuzzy `ForAll` is equivalent to pointwise value `= 1`. -/
theorem crispForAll_endpoint_iff_allEqOne
    [Nonempty U]
    (p : FuzzyQuantifierParams) (profile : U → ℝ)
    (hε0 : p.ε = 0)
    (hPCL1 : p.PCL = 1) :
    fuzzyForAllHolds p profile ↔ ∀ u : U, profile u = 1 := by
  constructor
  · intro hForAll u
    have hNear : nearOne p (profile u) :=
      nearOne_of_fuzzyForAll_eq_one p profile u hForAll hPCL1
    unfold nearOne at hNear
    rw [hε0] at hNear
    linarith [hNear.1, hNear.2]
  · intro hAll
    have hNearAll : ∀ u : U, nearOne p (profile u) := by
      intro u
      have hu : profile u = 1 := hAll u
      unfold nearOne
      rw [hu, hε0]
      constructor <;> norm_num
    have hLeTrue :
        nearOneFraction p profile ≤ witnessFraction (U := U) (fun _ : U => True) := by
      classical
      unfold nearOneFraction
      exact witnessFraction_mono
        (pred₁ := fun u => nearOne p (profile u))
        (pred₂ := fun _ : U => True)
        (hImpl := by intro _ _; trivial)
    have hTrueLe :
        witnessFraction (U := U) (fun _ : U => True) ≤ nearOneFraction p profile := by
      classical
      unfold nearOneFraction
      exact witnessFraction_mono
        (pred₁ := fun _ : U => True)
        (pred₂ := fun u => nearOne p (profile u))
        (hImpl := by intro u _; exact hNearAll u)
    have hFrac1 : nearOneFraction p profile = 1 := by
      have hEq :
          nearOneFraction p profile = witnessFraction (U := U) (fun _ : U => True) :=
        le_antisymm hLeTrue hTrueLe
      simpa [witnessFraction_true (U := U)] using hEq
    exact (fuzzyForAllHolds_iff_fraction_eq_one_of_PCL_eq_one p profile hPCL1).2 hFrac1

end CrispEndpoints

section Rule4Discrepancy

variable {U : Type*} [Fintype U]

/-- Quantitative discrepancy for Chapter-11 rule-4 style comparison:
`∃x(G ∧ F(x))` vs `G ∧ ∃x F(x)` (fuzzy existential score path). -/
noncomputable def rule4Discrepancy
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ) : ℝ :=
  |fuzzyExistsScore p (conjoinProfile g profile) - min g (fuzzyExistsScore p profile)|

theorem rule4Discrepancy_nonneg
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ) :
    0 ≤ rule4Discrepancy p g profile := by
  unfold rule4Discrepancy
  exact abs_nonneg _

/-- If gate `g` stays above the near-one threshold (`1-ε`), conjunction does not
change near-one witness mass. -/
theorem nearOneFraction_conjoin_eq_of_gate_high
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgate : 1 - p.ε ≤ g)
    (hg1 : g ≤ 1)
    (hub : ∀ u : U, profile u ≤ 1) :
    nearOneFraction p (conjoinProfile g profile) = nearOneFraction p profile := by
  apply nearOneFraction_eq_of_signatureEq
  intro u
  unfold conjoinProfile
  constructor
  · intro hNear
    unfold nearOne at hNear
    unfold nearOne
    constructor
    · exact le_trans hNear.1 (min_le_right g (profile u))
    · exact hub u
  · intro hNear
    unfold nearOne at hNear
    unfold nearOne
    constructor
    · exact le_min hgate hNear.1
    · exact le_trans (min_le_left g (profile u)) hg1

/-- High-gate identity at score level. -/
theorem fuzzyExistsScore_conjoin_eq_of_gate_high
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgate : 1 - p.ε ≤ g)
    (hg1 : g ≤ 1)
    (hub : ∀ u : U, profile u ≤ 1) :
    fuzzyExistsScore p (conjoinProfile g profile) = fuzzyExistsScore p profile := by
  unfold fuzzyExistsScore
  exact nearOneFraction_conjoin_eq_of_gate_high p g profile hgate hg1 hub

theorem abs_sub_min_le_one_sub_left
    (s g : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    |s - min g s| ≤ 1 - g := by
  by_cases hsg : s ≤ g
  · have hrhs_nonneg : 0 ≤ 1 - g := by linarith [hg.2]
    simp [min_eq_right hsg, hrhs_nonneg]
  · have hgs : g ≤ s := le_of_lt (lt_of_not_ge hsg)
    have habs : |s - g| = s - g := abs_of_nonneg (sub_nonneg.mpr hgs)
    have hle : s - g ≤ 1 - g := sub_le_sub_right hs.2 g
    have hmin : min g s = g := min_eq_left hgs
    rw [hmin]
    simpa [habs] using hle

/-- Rule-4 discrepancy bound (high-gate regime): discrepancy is at most `1 - g`.
So when `g` is close to `1`, noncommutativity is forced small. -/
theorem rule4Discrepancy_bound_of_gate_high
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgate : 1 - p.ε ≤ g)
    (hg : g ∈ Set.Icc (0 : ℝ) 1)
    (hub : ∀ u : U, profile u ≤ 1) :
    rule4Discrepancy p g profile ≤ 1 - g := by
  unfold rule4Discrepancy
  rw [fuzzyExistsScore_conjoin_eq_of_gate_high p g profile hgate hg.2 hub]
  have hs : fuzzyExistsScore p profile ∈ Set.Icc (0 : ℝ) 1 := by
    unfold fuzzyExistsScore
    exact nearOneFraction_in_unit p profile
  exact abs_sub_min_le_one_sub_left (fuzzyExistsScore p profile) g hs hg

/-- Exact commuting condition (high-gate + gate covers score): discrepancy vanishes. -/
theorem rule4Discrepancy_eq_zero_of_gate_high_and_cover
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgate : 1 - p.ε ≤ g)
    (hg1 : g ≤ 1)
    (hub : ∀ u : U, profile u ≤ 1)
    (hcover : fuzzyExistsScore p profile ≤ g) :
    rule4Discrepancy p g profile = 0 := by
  unfold rule4Discrepancy
  rw [fuzzyExistsScore_conjoin_eq_of_gate_high p g profile hgate hg1 hub]
  rw [min_eq_right hcover, sub_self, abs_zero]

/-- If gate `g` is below near-one threshold (`g < 1-ε`), conjunction kills all
near-one witnesses. -/
theorem nearOneFraction_conjoin_eq_zero_of_gate_low
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgateLow : g < 1 - p.ε) :
    nearOneFraction p (conjoinProfile g profile) = 0 := by
  have hNone : ∀ u : U, ¬ nearOne p ((conjoinProfile g profile) u) := by
    intro u hNear
    unfold nearOne conjoinProfile at hNear
    have hle : min g (profile u) ≤ g := min_le_left _ _
    linarith [hNear.1, hle, hgateLow]
  have hLeFalse :
      nearOneFraction p (conjoinProfile g profile) ≤
        witnessFraction (U := U) (fun _ : U => False) := by
    classical
    unfold nearOneFraction
    exact witnessFraction_mono
      (pred₁ := fun u => nearOne p ((conjoinProfile g profile) u))
      (pred₂ := fun _ : U => False)
      (hImpl := by
        intro u hu
        exact (hNone u hu).elim)
  have hGe0 : 0 ≤ nearOneFraction p (conjoinProfile g profile) :=
    (nearOneFraction_in_unit p (conjoinProfile g profile)).1
  rw [witnessFraction_false (U := U)] at hLeFalse
  exact le_antisymm hLeFalse hGe0

/-- Rule-4 discrepancy exact form in low-gate regime (with `0 ≤ g`). -/
theorem rule4Discrepancy_eq_minScore_of_gate_low
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgateLow : g < 1 - p.ε)
    (hg0 : 0 ≤ g) :
    rule4Discrepancy p g profile = min g (fuzzyExistsScore p profile) := by
  unfold rule4Discrepancy
  have hZero : fuzzyExistsScore p (conjoinProfile g profile) = 0 := by
    unfold fuzzyExistsScore
    exact nearOneFraction_conjoin_eq_zero_of_gate_low p g profile hgateLow
  rw [hZero]
  have hs0 : 0 ≤ fuzzyExistsScore p profile := by
    unfold fuzzyExistsScore
    exact (nearOneFraction_in_unit p profile).1
  have hmin0 : 0 ≤ min g (fuzzyExistsScore p profile) := by
    exact le_min hg0 hs0
  simp [hmin0]

/-- Low-gate discrepancy bound: discrepancy is at most `g` when `g ≥ 0`. -/
theorem rule4Discrepancy_le_g_of_gate_low
    (p : FuzzyQuantifierParams) (g : ℝ) (profile : U → ℝ)
    (hgateLow : g < 1 - p.ε)
    (hg0 : 0 ≤ g) :
    rule4Discrepancy p g profile ≤ g := by
  rw [rule4Discrepancy_eq_minScore_of_gate_low p g profile hgateLow hg0]
  exact min_le_left _ _

end Rule4Discrepancy

end Mettapedia.Logic.PLNFirstOrder
