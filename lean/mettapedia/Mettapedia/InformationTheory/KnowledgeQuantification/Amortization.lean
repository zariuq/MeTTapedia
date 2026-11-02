import Mettapedia.InformationTheory.KnowledgeQuantification.Basic
import Mettapedia.InformationTheory.RelationStoreRentOrBuy

/-!
# Knowledge over many uses: amortization and unknown use counts

A theory is described once and used `n` times, so its description length is amortized
(D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6:
181055, 2019, §§2.2.3, 2.3.1, 3.1, 3.3).

* `tendsto_knowledge_ofUses`: with input proportional to the uses, `K` tends to
  `(e − r) / (e + i)` per use; `tendsto_knowledge_ofUsesFixedInput`: with a fixed input,
  `K` tends to the effect `k`.
* `tendsto_knowledge_direct_description` (eq. 2.17), `tendsto_knowledge_pattern`
  (eq. 2.21) and `tendsto_knowledge_unbounded_memory` (eq. 2.19): the paper's three limits
  of a measuring device (its pressure-demon example), `1/2`, `1` and `0`.
* `knowledge_ofUses_lt_of_lt`: consilience, `K` grows with the number of uses.
* `eventually_knowledge_lt`: whatever the theory lengths, rankings by `K` settle on the
  ranking of the limits as uses grow.

How many uses will come is usually unknown when a theory is adopted.  For a lossless
theory without input, describing every use directly is renting and describing the theory
once is buying, so the rent-or-buy bounds of `RelationStoreRentOrBuy` apply:

* `rentOrBuyOpt_eq_min`: the hindsight optimum is the shorter of the direct description and
  the two-part code;
* `rentOrBuyOpt_eq_iff_half_le`: buying is optimal in hindsight exactly when `K ≥ 1/2`;
* `adoption_at_half_le_two_mul_opt`: adopting the theory at the first use at which its `K`
  would reach one half costs at most twice the hindsight optimum, however many uses come.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Filter Topology

namespace Budget

/-! ## Limits as uses grow -/

/-- With input proportional to the uses, knowledge tends to `(e − r) / (e + i)`. -/
theorem tendsto_knowledge_ofUses {e r i L : ℝ} (hpos : 0 < e + i) :
    Tendsto (fun n : ℕ => (ofUses n e r i L).knowledge) atTop (𝓝 ((e - r) / (e + i))) := by
  have hev : (fun n : ℕ => (e - r) / (e + i + L / n)) =ᶠ[atTop]
      fun n : ℕ => (ofUses n e r i L).knowledge := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [knowledge_ofUses (Nat.cast_pos.2 hn)]
  refine Tendsto.congr' hev ?_
  have hL : Tendsto (fun n : ℕ => L / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => e + i + L / (n : ℝ)) atTop (𝓝 (e + i)) := by
    have := (tendsto_const_nhds (x := e + i)).add hL
    rwa [add_zero] at this
  exact tendsto_const_nhds.div hden hpos.ne'

/-- A system used `n` times with a fixed total input `I`, as when one measurement fixes a
pattern for every later use. -/
def ofUsesFixedInput (n e r I L : ℝ) : Budget := ⟨n * e, n * r, I, L⟩

theorem knowledge_ofUsesFixedInput {n : ℝ} (hn : 0 < n) (e r I L : ℝ) :
    (ofUsesFixedInput n e r I L).knowledge = (e - r) / (e + (I + L) / n) := by
  unfold knowledge explained total ofUsesFixedInput
  dsimp only
  rw [show n * e - n * r = n * (e - r) by ring,
    show n * e + I + L = n * (e + (I + L) / n) by field_simp; ring]
  exact mul_div_mul_left _ _ hn.ne'

/-- With a fixed input, knowledge tends to the effect `(e − r) / e`. -/
theorem tendsto_knowledge_ofUsesFixedInput {e r I L : ℝ} (he : 0 < e) :
    Tendsto (fun n : ℕ => (ofUsesFixedInput n e r I L).knowledge) atTop
      (𝓝 ((e - r) / e)) := by
  have hev : (fun n : ℕ => (e - r) / (e + (I + L) / n)) =ᶠ[atTop]
      fun n : ℕ => (ofUsesFixedInput n e r I L).knowledge := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [knowledge_ofUsesFixedInput (Nat.cast_pos.2 hn)]
  refine Tendsto.congr' hev ?_
  have hc : Tendsto (fun n : ℕ => (I + L) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => e + (I + L) / (n : ℝ)) atTop (𝓝 e) := by
    have := (tendsto_const_nhds (x := e)).add hc
    rwa [add_zero] at this
  exact tendsto_const_nhds.div hden he.ne'

/-- **Direct description** (eq. 2.17).  When every use needs its own measurement, as large as
the explanandum, a lossless theory tends to `1/2`. -/
theorem tendsto_knowledge_direct_description {e L : ℝ} (he : 0 < e) :
    Tendsto (fun n : ℕ => (ofUses n e 0 e L).knowledge) atTop (𝓝 (1 / 2)) := by
  have hlim := tendsto_knowledge_ofUses (e := e) (r := 0) (i := e) (L := L) (by linarith)
  have hval : (e - 0) / (e + e) = 1 / 2 := by
    field_simp
    ring
  rwa [hval] at hlim

/-- **A pattern** (eq. 2.21).  When one measurement fixes every later use, a lossless theory
tends to `1`. -/
theorem tendsto_knowledge_pattern {e I L : ℝ} (he : 0 < e) :
    Tendsto (fun n : ℕ => (ofUsesFixedInput n e 0 I L).knowledge) atTop (𝓝 1) := by
  have hlim := tendsto_knowledge_ofUsesFixedInput (e := e) (r := 0) (I := I) (L := L) he
  rwa [sub_zero, div_self he.ne'] at hlim

/-- **Unbounded memory** (eq. 2.19).  When the stored input grows with the square of the
number of uses, knowledge tends to `0`, whatever the theory. -/
theorem tendsto_knowledge_unbounded_memory {e L : ℝ} (he : 0 < e) (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => (⟨n * e, 0, n * n * e, L⟩ : Budget).knowledge) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with n
    unfold knowledge explained total
    dsimp only
    apply div_nonneg (by rw [sub_zero]; positivity) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    unfold knowledge explained total
    dsimp only
    rw [sub_zero, div_le_div_iff₀ (by positivity) hn']
    nlinarith [mul_pos hn' he, mul_pos (mul_pos hn' hn') he]

/-- **Consilience** (§3.3).  A theory of positive length with a positive effect holds more
knowledge the more often it is used. -/
theorem knowledge_ofUses_lt_of_lt {n n' e r i L : ℝ} (hn : 0 < n) (hnn' : n < n') (hr : r < e)
    (hL : 0 < L) (hpos : 0 < e + i) :
    (ofUses n e r i L).knowledge < (ofUses n' e r i L).knowledge := by
  have h1 : 0 < e + i + L / n := by have := div_pos hL hn; linarith
  have h2 : 0 < e + i + L / n' := by have := div_pos hL (hn.trans hnn'); linarith
  rw [ockham_relative hn (hn.trans hnn') hr h1 h2]
  exact div_lt_div_of_pos_left hL hn hnn'

/-- Whatever the theory lengths, the theory with the higher limit eventually holds more
knowledge: description length matters less and less as uses grow. -/
theorem eventually_knowledge_lt {e r i L e' r' i' L' : ℝ} (hpos : 0 < e + i)
    (hpos' : 0 < e' + i') (hlim : (e - r) / (e + i) < (e' - r') / (e' + i')) :
    ∀ᶠ n : ℕ in atTop, (ofUses n e r i L).knowledge < (ofUses n e' r' i' L').knowledge :=
  (tendsto_knowledge_ofUses hpos).eventually_lt (tendsto_knowledge_ofUses hpos') hlim

/-! ## Unknown use counts: rent or buy -/

open Mettapedia.InformationTheory.RelationStoreFloors

/-- A lossless theory of length `B` without input, used `q` times, each use worth `r`. -/
def losslessUses (r B q : ℕ) : Budget := ⟨(q : ℝ) * r, 0, 0, B⟩

theorem losslessUses_twoPartLength (r B q : ℕ) : (losslessUses r B q).twoPartLength = B := by
  simp [losslessUses, twoPartLength]

theorem losslessUses_knowledge (r B q : ℕ) :
    (losslessUses r B q).knowledge = (q : ℝ) * r / ((q : ℝ) * r + B) := by
  simp [losslessUses, knowledge, explained, total]

/-- The hindsight optimum of rent-or-buy is the shorter of the direct description and the
two-part code of the theory. -/
theorem rentOrBuyOpt_eq_min (r B q : ℕ) :
    ((rentOrBuyOpt r B q : ℕ) : ℝ) =
      min (losslessUses r B q).explanandum (losslessUses r B q).twoPartLength := by
  rw [losslessUses_twoPartLength]
  simp [rentOrBuyOpt, losslessUses]

private theorem half_le_losslessUses_iff {r B q : ℕ} (hpos : 0 < q * r + B) :
    1 / 2 ≤ (losslessUses r B q).knowledge ↔ B ≤ q * r := by
  have hpos' : (0 : ℝ) < (q : ℝ) * r + B := by exact_mod_cast hpos
  rw [losslessUses_knowledge, le_div_iff₀ hpos']
  constructor
  · intro h
    have : (B : ℝ) ≤ (q : ℝ) * r := by linarith
    exact_mod_cast this
  · intro h
    have : (B : ℝ) ≤ (q : ℝ) * r := by exact_mod_cast h
    linarith

private theorem losslessUses_le_half_iff {r B q : ℕ} (hpos : 0 < q * r + B) :
    (losslessUses r B q).knowledge ≤ 1 / 2 ↔ q * r ≤ B := by
  have hpos' : (0 : ℝ) < (q : ℝ) * r + B := by exact_mod_cast hpos
  rw [losslessUses_knowledge, div_le_iff₀ hpos']
  constructor
  · intro h
    have : (q : ℝ) * r ≤ B := by linarith
    exact_mod_cast this
  · intro h
    have : (q : ℝ) * r ≤ B := by exact_mod_cast h
    linarith

/-- Buying the theory is optimal in hindsight exactly when its knowledge has reached one
half. -/
theorem rentOrBuyOpt_eq_iff_half_le {r B q : ℕ} (hpos : 0 < q * r + B) :
    rentOrBuyOpt r B q = B ↔ 1 / 2 ≤ (losslessUses r B q).knowledge := by
  rw [half_le_losslessUses_iff hpos, rentOrBuyOpt, min_eq_right_iff]

/-- The adoption allowance `k r ≤ B ≤ (k + 1) r` of the 2-competitive policy is the point
at which knowledge crosses one half. -/
theorem knowledge_half_at_adoption {r B k : ℕ} (hr : 0 < r) (hlow : k * r ≤ B)
    (hhigh : B ≤ (k + 1) * r) :
    (losslessUses r B k).knowledge ≤ 1 / 2 ∧ 1 / 2 ≤ (losslessUses r B (k + 1)).knowledge := by
  have hpos1 : 0 < (k + 1) * r + B := by positivity
  constructor
  · rcases Nat.eq_zero_or_pos (k * r + B) with hz | hpos
    · have hkr : k * r = 0 := by omega
      have hB : B = 0 := by omega
      rw [losslessUses_knowledge]
      have hcast : (k : ℝ) * r = 0 := by exact_mod_cast hkr
      rw [hcast, hB]
      norm_num
    · exact (losslessUses_le_half_iff hpos).2 hlow
  · exact (half_le_losslessUses_iff hpos1).2 hhigh

/-- **Unknown use counts.**  Adopt the theory at the first use at which its knowledge reaches
one half.  Whatever the number of uses, the description length paid is at most twice the
hindsight optimum.  This is `rentOrBuy_le_two_mul_opt`, with its allowance read as a
threshold on `K`. -/
theorem adoption_at_half_le_two_mul_opt {r B k : ℕ} (hr : 0 < r)
    (hbefore : (losslessUses r B k).knowledge ≤ 1 / 2)
    (hafter : 1 / 2 ≤ (losslessUses r B (k + 1)).knowledge) (q : ℕ) :
    rentOrBuy r B k q ≤ 2 * rentOrBuyOpt r B q := by
  have hlow : k * r ≤ B := by
    rcases Nat.eq_zero_or_pos (k * r + B) with hz | hpos
    · omega
    · exact (losslessUses_le_half_iff hpos).1 hbefore
  have hhigh : B ≤ (k + 1) * r :=
    (half_le_losslessUses_iff (by positivity)).1 hafter
  exact rentOrBuy_le_two_mul_opt hlow hhigh q

end Budget

end Mettapedia.InformationTheory.KnowledgeQuantification
