import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Tiering an invocation of unknown length

Interpreter work costs one per unit. Native work costs `q` per unit,
`0 < q < 1`, and compilation costs `C > 0`. At a threshold `t`, the
switch costs `C + handoff + lost * t + q * work`. Replay discards the
entire prefix (`lost = 1`); resuming at the same point retains it
(`lost = 1 - q`). Intermediate values model partial reuse. `handoff`
is any additional cost that the offline native-from-entry run avoids.

The comparison is for one invocation, with no profile information other
than survival to the threshold. Cached compilation across calls, variable
native speed, semantic permission to replay, and translation of live state
are separate questions. A threshold ties with completion in favor of
switching, so its worst case is attained at the threshold itself.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TierUpReplayCost

noncomputable section

structure Prices where
  compile : ℝ
  q : ℝ
  compile_pos : 0 < compile
  q_pos : 0 < q
  q_lt_one : q < 1

def gap (p : Prices) : ℝ := 1 - p.q

theorem gap_pos (p : Prices) : 0 < gap p := sub_pos.mpr p.q_lt_one

def breakEven (p : Prices) : ℝ := p.compile / gap p

theorem breakEven_pos (p : Prices) : 0 < breakEven p :=
  div_pos p.compile_pos (gap_pos p)

theorem compile_eq (p : Prices) : p.compile = gap p * breakEven p := by
  unfold breakEven
  field_simp [(gap_pos p).ne']

structure Transfer (p : Prices) where
  lost : ℝ
  handoff : ℝ
  lost_ge_gap : gap p ≤ lost
  handoff_nonneg : 0 ≤ handoff

def replay (p : Prices) : Transfer p := ⟨1, 0, by unfold gap; linarith [p.q_pos], le_rfl⟩

def resume (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff) : Transfer p :=
  ⟨gap p, handoff, le_rfl, nonneg⟩

def native (p : Prices) (work : ℝ) : ℝ := p.compile + p.q * work

def offline (p : Prices) (work : ℝ) : ℝ := min work (native p work)

def switched (p : Prices) (path : Transfer p) (threshold work : ℝ) : ℝ :=
  native p work + path.handoff + path.lost * threshold

def tier (p : Prices) (path : Transfer p) (threshold work : ℝ) : ℝ :=
  if work < threshold then work else switched p path threshold work

def Competitive (p : Prices) (run : ℝ → ℝ) (ratio : ℝ) : Prop :=
  ∀ work : ℝ, 0 < work → run work ≤ ratio * offline p work

def atSwitch (p : Prices) (path : Transfer p) (threshold : ℝ) : ℝ :=
  switched p path threshold threshold / offline p threshold

theorem native_pos (p : Prices) {work : ℝ} (pos : 0 ≤ work) : 0 < native p work :=
  add_pos_of_pos_of_nonneg p.compile_pos (mul_nonneg p.q_pos.le pos)

theorem offline_pos (p : Prices) {work : ℝ} (pos : 0 < work) : 0 < offline p work :=
  lt_min pos (native_pos p pos.le)

theorem breakEven_criterion (p : Prices) (work : ℝ) :
    native p work ≤ work ↔ breakEven p ≤ work := by
  rw [breakEven, div_le_iff₀ (gap_pos p)]
  unfold native gap
  constructor <;> intro h <;> linarith

theorem native_at_breakEven (p : Prices) : native p (breakEven p) = breakEven p := by
  have eq := compile_eq p
  unfold native gap at *
  linarith

private theorem offline_before (p : Prices) {work : ℝ} (earlier : work ≤ breakEven p) :
    offline p work = work := by
  have enough := mul_le_mul_of_nonneg_left earlier (gap_pos p).le
  have base := compile_eq p
  unfold offline native gap at *
  exact min_eq_left (by linarith)

private theorem offline_after (p : Prices) {work : ℝ} (later : breakEven p ≤ work) :
    offline p work = native p work :=
  min_eq_right ((breakEven_criterion p work).mpr later)

private theorem branch_bounds (p : Prices) (r cost work : ℝ) (hr : 0 ≤ r) :
    cost ≤ r * offline p work ↔ cost ≤ r * work ∧ cost ≤ r * native p work := by
  unfold offline
  by_cases order : work ≤ native p work
  · rw [min_eq_left order]
    exact ⟨fun h => ⟨h, h.trans (mul_le_mul_of_nonneg_left order hr)⟩, And.left⟩
  · have rev := le_of_not_ge order
    rw [min_eq_right rev]
    exact ⟨fun h => ⟨h.trans (mul_le_mul_of_nonneg_left rev hr), h⟩, And.right⟩

private theorem switched_ge_work (p : Prices) (path : Transfer p) {threshold : ℝ}
    (ht : 0 ≤ threshold) : threshold ≤ switched p path threshold threshold := by
  have past := mul_le_mul_of_nonneg_right path.lost_ge_gap ht
  unfold switched native gap at *
  linarith [p.compile_pos, path.handoff_nonneg]

/-- A run that has just reached the switching point is a worst case.
The two later cost lines have slopes no larger than the same ratio times
the two offline slopes. Earlier no-switch runs are bounded as well. -/
theorem threshold_competitive_iff (p : Prices) (path : Transfer p) (threshold r : ℝ)
    (ht : 0 < threshold) :
    Competitive p (tier p path threshold) r ↔ atSwitch p path threshold ≤ r := by
  have optPos := offline_pos p ht
  constructor
  · intro holds
    have exactAt := holds threshold ht
    rw [tier, if_neg (lt_irrefl _)] at exactAt
    exact (div_le_iff₀ optPos).mpr exactAt
  · intro bound
    have exactAt : switched p path threshold threshold ≤ r * offline p threshold :=
      (div_le_iff₀ optPos).mp bound
    have base := switched_ge_work p path ht.le
    have one : 1 ≤ r := by
      apply (le_mul_iff_one_le_left optPos).mp
      exact (min_le_left _ _).trans (base.trans exactAt)
    have nonneg : 0 ≤ r := zero_le_one.trans one
    obtain ⟨interpreted, compiled⟩ := (branch_bounds p r _ _ nonneg).mp exactAt
    intro work hw
    apply (branch_bounds p r _ _ nonneg).mpr
    by_cases early : work < threshold
    · rw [tier, if_pos early]
      refine ⟨by simpa using mul_le_mul_of_nonneg_right one hw.le, ?_⟩
      have relation : work * native p threshold ≤ threshold * native p work := by
        unfold native
        nlinarith only [mul_le_mul_of_nonneg_left early.le p.compile_pos.le]
      have dominated : work * native p threshold ≤ (r * native p work) * native p threshold := by
        calc
          _ ≤ threshold * native p work := relation
          _ ≤ (r * native p threshold) * native p work :=
            mul_le_mul_of_nonneg_right (base.trans compiled) (native_pos p hw.le).le
          _ = _ := by ring
      exact le_of_mul_le_mul_right dominated (native_pos p ht.le)
    · rw [tier, if_neg early]
      have distance : 0 ≤ work - threshold := sub_nonneg.mpr (le_of_not_gt early)
      have slow : p.q * (work - threshold) ≤ r * (work - threshold) :=
        mul_le_mul_of_nonneg_right (p.q_lt_one.le.trans one) distance
      have fast : p.q * (work - threshold) ≤ r * (p.q * (work - threshold)) := by
        simpa using mul_le_mul_of_nonneg_right one (mul_nonneg p.q_pos.le distance)
      unfold switched native at *
      constructor
      · nlinarith only [interpreted, slow]
      · nlinarith only [compiled, fast]

theorem atSwitch_before (p : Prices) (path : Transfer p) (t : ℝ)
    (ht : 0 < t) (early : t ≤ breakEven p) :
    atSwitch p path t = path.lost + p.q + (p.compile + path.handoff) / t := by
  rw [atSwitch, offline_before p early]
  unfold switched native
  field_simp [ht.ne']
  ring

theorem atSwitch_after (p : Prices) (path : Transfer p) (t : ℝ) (ht : 0 < t)
    (late : breakEven p ≤ t) :
    atSwitch p path t = 1 + (path.handoff + path.lost * t) / native p t := by
  rw [atSwitch, offline_after p late, switched]
  field_simp [(native_pos p ht.le).ne']
  ring

def breakRatio (p : Prices) (path : Transfer p) : ℝ :=
  1 + path.lost + path.handoff / breakEven p

theorem at_breakEven (p : Prices) (path : Transfer p) :
    atSwitch p path (breakEven p) = breakRatio p path := by
  rw [atSwitch_after p path _ (breakEven_pos p) le_rfl, native_at_breakEven]
  unfold breakRatio
  field_simp [(breakEven_pos p).ne']
  ring

/-- Without a handoff surcharge, the unique best finite threshold is the
offline break-even point, independently of how much prefix work is lost. -/
theorem no_handoff_unique_threshold (p : Prices) (path : Transfer p) (t : ℝ) (ht : 0 < t)
    (free : path.handoff = 0) :
    1 + path.lost ≤ atSwitch p path t ∧
      (atSwitch p path t = 1 + path.lost ↔ t = breakEven p) := by
  have hd := gap_pos p
  have hp : 0 < path.lost := hd.trans_le path.lost_ge_gap
  by_cases same : t = breakEven p
  · simp [same, at_breakEven, breakRatio, free]
  · have strict : 1 + path.lost < atSwitch p path t := by
      rcases lt_or_gt_of_ne same with early | late
      · rw [atSwitch_before p path t ht early.le, free, add_zero]
        have bigger : gap p < p.compile / t := (lt_div_iff₀ ht).mpr
          (by rw [compile_eq p]; exact mul_lt_mul_of_pos_left early hd)
        unfold gap at bigger
        linarith
      · rw [atSwitch_after p path t ht late.le, free, zero_add]
        have profitable : native p t < t := by
          have lower := mul_lt_mul_of_pos_left late hd
          have before := compile_eq p
          unfold gap native at *
          nlinarith only [before, lower]
        have larger : path.lost < path.lost * t / native p t :=
          (lt_div_iff₀ (native_pos p ht.le)).mpr (mul_lt_mul_of_pos_left profitable hp)
        linarith
    exact ⟨strict.le, ⟨fun equal => (strict.ne equal.symm).elim, fun h => (same h).elim⟩⟩

def neverRatio (p : Prices) : ℝ := 1 / p.q

/-- The interpreter-only ratio is a supremum, approached on arbitrarily
long work. The constructed witness rules out any smaller alleged bound. -/
theorem never_competitive_iff (p : Prices) (r : ℝ) :
    Competitive p id r ↔ neverRatio p ≤ r := by
  constructor
  · intro all
    by_contra smaller
    have scaling : 0 < 1 - r * p.q := sub_pos.mpr
      ((lt_div_iff₀ p.q_pos).mp (lt_of_not_ge smaller))
    let work : ℝ := (|r| * p.compile + 1) / (1 - r * p.q)
    have hw : 0 < work := div_pos
      (add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg _) p.compile_pos.le) zero_lt_one) scaling
    have rr : 0 ≤ r := by
      have good := all work hw
      change work ≤ r * offline p work at good
      by_contra h
      exact (not_le_of_gt (mul_neg_of_neg_of_pos (lt_of_not_ge h) (offline_pos p hw))).elim
        (hw.le.trans good)
    have allowed := ((branch_bounds p r work work rr).mp (all work hw)).2
    have defWork : work * (1 - r * p.q) = |r| * p.compile + 1 :=
      div_mul_cancel₀ _ scaling.ne'
    have abs := mul_le_mul_of_nonneg_right (le_abs_self r) p.compile_pos.le
    unfold native at allowed
    nlinarith only [allowed, defWork, abs]
  · intro bound work hw
    change work ≤ r * offline p work
    have one : 1 ≤ r := (by
      unfold neverRatio
      exact (le_div_iff₀ p.q_pos).mpr (by simpa using p.q_lt_one.le) : 1 ≤ neverRatio p).trans bound
    have scale : 1 ≤ r * p.q := (div_le_iff₀ p.q_pos).mp bound
    apply (branch_bounds p r _ _ (zero_le_one.trans one)).mpr
    refine ⟨by simpa using mul_le_mul_of_nonneg_right one hw.le, ?_⟩
    unfold native
    nlinarith only [mul_le_mul_of_nonneg_right scale hw.le,
      mul_nonneg (zero_le_one.trans one) p.compile_pos.le]

def bestRatio (p : Prices) (path : Transfer p) : ℝ :=
  min (breakRatio p path) (neverRatio p)

private theorem best_le_atSwitch (p : Prices) (path : Transfer p) {t : ℝ} (ht : 0 < t) :
    bestRatio p path ≤ atSwitch p path t := by
  have bPos := breakEven_pos p
  by_cases early : t ≤ breakEven p
  · have ratio : atSwitch p path (breakEven p) ≤ atSwitch p path t := by
      rw [atSwitch_before p path _ bPos le_rfl, atSwitch_before p path _ ht early]
      exact add_le_add (le_refl _)
        (div_le_div_of_nonneg_left (add_nonneg p.compile_pos.le path.handoff_nonneg) ht early)
    rw [at_breakEven] at ratio
    exact (min_le_left _ _).trans ratio
  · let r := bestRatio p path
    have late := le_of_not_ge early
    have atBreak : r - 1 ≤ (path.handoff + path.lost * breakEven p) / native p (breakEven p) := by
      have low : r ≤ atSwitch p path (breakEven p) := by
        rw [at_breakEven]
        exact min_le_left _ _
      rw [atSwitch_after p path _ bPos le_rfl] at low
      linarith
    have base := (le_div_iff₀ (native_pos p bPos.le)).mp atBreak
    have speed : r * p.q ≤ 1 := (le_div_iff₀ p.q_pos).mp (min_le_right _ _)
    have slope : (r - 1) * p.q ≤ path.lost := by
      have h := path.lost_ge_gap
      unfold gap at h
      linarith
    have extra := mul_le_mul_of_nonneg_right slope (sub_nonneg.mpr late)
    have continued : (r - 1) * native p t ≤ path.handoff + path.lost * t := by
      unfold native at *
      nlinarith only [base, extra]
    rw [atSwitch_after p path t ht late]
    have bound := (le_div_iff₀ (native_pos p ht.le)).mpr continued
    change r ≤ _
    linarith

/-- Any positive finite threshold competes with the option of never
switching. The break-even threshold or the interpreter attains the minimum,
even if translation imposes an extra fixed handoff surcharge. -/
theorem achievable_iff (p : Prices) (path : Transfer p) (r : ℝ) :
    (Competitive p id r ∨ ∃ t : ℝ, 0 < t ∧ Competitive p (tier p path t) r) ↔
      bestRatio p path ≤ r := by
  constructor
  · rintro (never | ⟨t, ht, switches⟩)
    · exact (min_le_right _ _).trans ((never_competitive_iff p r).mp never)
    · exact (best_le_atSwitch p path ht).trans ((threshold_competitive_iff p path t r ht).mp switches)
  · intro best
    rcases min_le_iff.mp best with breaks | never
    · exact Or.inr ⟨breakEven p, breakEven_pos p,
        (threshold_competitive_iff p path _ r (breakEven_pos p)).mpr ((at_breakEven p path).trans_le breaks)⟩
    · exact Or.inl ((never_competitive_iff p r).mpr never)

theorem replay_ratio (p : Prices) : bestRatio p (replay p) = min 2 (1 / p.q) := by
  norm_num [bestRatio, breakRatio, replay, neverRatio]

theorem resume_ratio (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff) :
    bestRatio p (resume p handoff nonneg) = min (2 - p.q + handoff / breakEven p) (1 / p.q) := by
  unfold bestRatio breakRatio resume gap neverRatio
  congr 1
  ring

/-- Exact engineering margin in this cost model. To improve on replay,
the handoff cost must fit below both the replay gap and the interpreter
option. A small native speedup makes the second margin particularly tight. -/
theorem resume_strictly_beats_replay_iff (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff) :
    bestRatio p (resume p handoff nonneg) < bestRatio p (replay p) ↔
      handoff / breakEven p < min p.q ((1 - p.q) ^ 2 / p.q) := by
  rw [resume_ratio, replay_ratio]
  have diff : 1 / p.q - (2 - p.q) = (1 - p.q) ^ 2 / p.q := by
    field_simp [p.q_pos.ne']
    ring
  constructor
  · intro better
    rcases min_lt_iff.mp better with yes | no
    · rw [lt_min_iff] at yes ⊢
      exact ⟨by linarith [yes.1], by linarith [yes.2]⟩
    · exact ((min_le_right _ _).not_gt no).elim
  · rw [lt_min_iff]
    intro room
    exact (min_le_left _ _).trans_lt (lt_min (by linarith [room.1]) (by linarith [room.2]))

theorem replay_never_optimal_iff (p : Prices) :
    Competitive p id (bestRatio p (replay p)) ↔ 1 / 2 ≤ p.q := by
  rw [never_competitive_iff, replay_ratio, neverRatio, le_min_iff]
  simp only [le_refl, and_true, div_le_iff₀ p.q_pos]
  constructor <;> intro inequality <;> linarith

theorem free_resume_beats_replay (p : Prices) :
    bestRatio p (resume p 0 le_rfl) < bestRatio p (replay p) := by
  rw [resume_strictly_beats_replay_iff, zero_div]
  exact lt_min p.q_pos (div_pos (sq_pos_of_pos (sub_pos.mpr p.q_lt_one)) p.q_pos)

/-- With a fixed translation cost, the native-rate band in which OSR is a
strict minimax improvement narrows symmetrically around q = 1/2. -/
theorem resume_speed_band (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff) :
    bestRatio p (resume p handoff nonneg) < bestRatio p (replay p) ↔
      handoff / (p.compile + handoff) < p.q ∧ p.q < p.compile / (p.compile + handoff) := by
  have sumPos := add_pos_of_pos_of_nonneg p.compile_pos nonneg
  rw [resume_strictly_beats_replay_iff, lt_min_iff, div_lt_iff₀ sumPos, lt_div_iff₀ sumPos]
  have first : handoff / breakEven p < p.q ↔ handoff * gap p < p.q * p.compile := by
    rw [div_lt_iff₀ (breakEven_pos p), breakEven, ← mul_div_assoc, lt_div_iff₀ (gap_pos p)]
  have second : handoff / breakEven p < (1 - p.q) ^ 2 / p.q ↔
      handoff * p.q < p.compile * gap p := by
    have rearrange : (1 - p.q) ^ 2 / p.q * breakEven p = p.compile * gap p / p.q := by
      calc
        _ = (gap p * breakEven p) * gap p / p.q := by unfold gap; ring
        _ = _ := by rw [← compile_eq p]
    rw [div_lt_iff₀ (breakEven_pos p), rearrange, lt_div_iff₀ p.q_pos]
  rw [first, second]
  unfold gap
  constructor <;> rintro ⟨left, right⟩ <;> constructor <;> nlinarith only [left, right]

theorem handoff_at_least_compile_cannot_improve (p : Prices) (handoff : ℝ)
    (nonneg : 0 ≤ handoff) (large : p.compile ≤ handoff) :
    ¬ bestRatio p (resume p handoff nonneg) < bestRatio p (replay p) := by
  rw [resume_speed_band]
  intro band
  have tooSmall := band.1.trans band.2
  have enough := (div_lt_div_iff_of_pos_right (add_pos_of_pos_of_nonneg p.compile_pos nonneg)).mp tooSmall
  exact (not_lt_of_ge large) enough

theorem twofold_speed_margin (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff)
    (twice : p.q = 1 / 2) :
    bestRatio p (resume p handoff nonneg) < bestRatio p (replay p) ↔ handoff < p.compile := by
  have sumPos := add_pos_of_pos_of_nonneg p.compile_pos nonneg
  rw [resume_speed_band, twice, div_lt_iff₀ sumPos, lt_div_iff₀ sumPos]
  constructor
  · rintro ⟨left, _⟩
    linarith only [left]
  · intro smaller
    constructor <;> linarith only [smaller]

/-- On a single run that actually switches, resumption saves the native
cost of redoing the prefix. This is a different question from which policy
wins minimax across short and long invocations. -/
theorem same_switch_pointwise_margin (p : Prices) (handoff : ℝ) (nonneg : 0 ≤ handoff)
    {threshold work : ℝ} (hit : threshold ≤ work) :
    tier p (resume p handoff nonneg) threshold work < tier p (replay p) threshold work ↔
      handoff < p.q * threshold := by
  simp only [tier, if_neg (not_lt.mpr hit), switched, resume, replay, gap]
  constructor <;> intro h <;> linarith

/-- Compiling at zero has no finite multiplicative guarantee: an adversary
can always choose a short enough invocation. -/
theorem eager_not_competitive (p : Prices) (path : Transfer p) (r : ℝ) :
    ¬ Competitive p (tier p path 0) r := by
  intro all
  have scale : 0 < |r| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  let work := p.compile / (|r| + 1)
  have hw : 0 < work := div_pos p.compile_pos scale
  have multiplication : work * (|r| + 1) = p.compile := div_mul_cancel₀ _ scale.ne'
  have paid := all work hw
  rw [tier, if_neg (not_lt.mpr hw.le)] at paid
  have compileCost : p.compile ≤ switched p path 0 work := by
    unfold switched native
    simp only [mul_zero, add_zero]
    linarith only [path.handoff_nonneg, mul_nonneg p.q_pos.le hw.le]
  have small : |r| * work < p.compile := by nlinarith only [multiplication, hw]
  exact (not_lt_of_ge (compileCost.trans (paid.trans
    ((mul_le_mul_of_nonneg_right (le_abs_self r) (offline_pos p hw).le).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg r)))))) small

namespace Controls

def mild : Prices := ⟨1, 3 / 4, by norm_num, by norm_num, by norm_num⟩

/-- A 4/3 speedup: the interpreter beats replay-when-hot; zero-surcharge
resumption still improves over both. -/
theorem modest_speedup :
    bestRatio mild (replay mild) = 4 / 3 ∧
      atSwitch mild (replay mild) (breakEven mild) = 2 ∧
      bestRatio mild (resume mild 0 le_rfl) = 5 / 4 := by
  rw [replay_ratio, at_breakEven, resume_ratio]
  norm_num [mild, replay, breakRatio, min_def]

theorem handoff_cost_can_erase_the_benefit :
    bestRatio mild (resume mild (1 / 3) (by norm_num)) = bestRatio mild (replay mild) := by
  rw [resume_ratio, replay_ratio]
  norm_num [mild, breakEven, gap, min_def]

end Controls
end
end Mettapedia.Machines.TierUpReplayCost
