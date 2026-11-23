import Mettapedia.Machines.TierUpReplayCost

/-!
# Switching at a delayed checkpoint

The waiting charge is the native saving foregone, while the redo charge is
the native cost of the repeated prefix. Only already qualified, unobserved
work can be redone. This file compares costs; it does not erase effects.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TierUpCheckpoint

open TierUpReplayCost

noncomputable section

def checkpointCost (p : Prices) (handoff redo threshold work : ℝ) : ℝ :=
  if work < threshold then work
  else threshold + p.compile + handoff + p.q * (work - threshold + redo)

def charge (p : Prices) (handoff redo : ℝ) (h : 0 ≤ handoff) (d : 0 ≤ redo) : Transfer p :=
  resume p (handoff + p.q * redo) (add_nonneg h (mul_nonneg p.q_pos.le d))

theorem checkpoint_eq_tier (p : Prices) {handoff redo : ℝ}
    (h : 0 ≤ handoff) (d : 0 ≤ redo) (threshold work : ℝ) :
    checkpointCost p handoff redo threshold work =
      tier p (charge p handoff redo h d) threshold work := by
  unfold checkpointCost tier
  split
  · rfl
  · simp only [switched, native, charge, resume, gap]
    ring

theorem redo_mono (p : Prices) (handoff threshold work : ℝ) {early late : ℝ}
    (order : early ≤ late) :
    checkpointCost p handoff early threshold work ≤ checkpointCost p handoff late threshold work := by
  unfold checkpointCost
  split
  · exact le_rfl
  · gcongr
    exact p.q_pos.le

/-- Changing a threshold on the native-offline side has one sign throughout
that side. In particular, the latest boundary is not always the worst. -/
theorem ratio_difference (p : Prices) (path : Transfer p) {first last : ℝ}
    (goodFirst : breakEven p ≤ first) (goodLast : breakEven p ≤ last) :
    atSwitch p path last - atSwitch p path first =
      ((path.lost * p.compile - p.q * path.handoff) * (last - first)) /
        (native p first * native p last) := by
  have x := (breakEven_pos p).trans_le goodFirst
  have y := (breakEven_pos p).trans_le goodLast
  rw [atSwitch_after p path _ y goodLast, atSwitch_after p path _ x goodFirst]
  field_simp [(native_pos p x.le).ne', (native_pos p y.le).ne']
  unfold native
  ring

theorem ratio_le_endpoint_max (p : Prices) (path : Transfer p) {first middle last : ℝ}
    (after : breakEven p ≤ first) (earlier : first ≤ middle) (later : middle ≤ last) :
    atSwitch p path middle ≤ max (atSwitch p path first) (atSwitch p path last) := by
  have hm := after.trans earlier
  have hl := hm.trans later
  by_cases rising : 0 ≤ path.lost * p.compile - p.q * path.handoff
  · have diff := ratio_difference p path hm hl
    have nonneg : 0 ≤ atSwitch p path last - atSwitch p path middle := by
      rw [diff]
      apply div_nonneg (mul_nonneg rising (sub_nonneg.mpr later))
      exact mul_nonneg (native_pos p ((breakEven_pos p).trans_le hm).le).le
        (native_pos p ((breakEven_pos p).trans_le hl).le).le
    exact (sub_nonneg.mp nonneg).trans (le_max_right _ _)
  · have diff := ratio_difference p path after hm
    have nonpos : atSwitch p path middle - atSwitch p path first ≤ 0 := by
      rw [diff]
      apply div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge rising) (sub_nonneg.mpr earlier))
      exact mul_nonneg (native_pos p ((breakEven_pos p).trans_le after).le).le
        (native_pos p ((breakEven_pos p).trans_le hm).le).le
    exact (sub_nonpos.mp nonpos).trans (le_max_left _ _)

/-- Sharp for the envelope of all wait/redo pairs, not an assertion that
both endpoint pairs are reachable in a concrete executor. -/
theorem envelope_competitive_iff (p : Prices) {handoff redo : ℝ}
    (h : 0 ≤ handoff) (d : 0 ≤ redo) {first last : ℝ}
    (after : breakEven p ≤ first) (ordered : first ≤ last) (ratio : ℝ) :
    (∀ threshold ∈ Set.Icc first last, ∀ actual ∈ Set.Icc 0 redo,
      Competitive p (checkpointCost p handoff actual threshold) ratio) ↔
    max (atSwitch p (charge p handoff redo h d) first)
      (atSwitch p (charge p handoff redo h d) last) ≤ ratio := by
  let path := charge p handoff redo h d
  have costs (threshold : ℝ) (positive : 0 < threshold) :
      Competitive p (checkpointCost p handoff redo threshold) ratio ↔
        atSwitch p path threshold ≤ ratio := by
    have same : checkpointCost p handoff redo threshold = tier p path threshold :=
      funext (checkpoint_eq_tier p h d threshold)
    rw [same, threshold_competitive_iff p path threshold ratio positive]
  have fpos := (breakEven_pos p).trans_le after
  constructor
  · intro all
    exact max_le ((costs first fpos).mp (all first ⟨le_rfl, ordered⟩ redo ⟨d, le_rfl⟩))
      ((costs last (fpos.trans_le ordered)).mp (all last ⟨ordered, le_rfl⟩ redo ⟨d, le_rfl⟩))
  · intro bound threshold between actual amount
    have withRedo := (costs threshold (fpos.trans_le between.1)).mpr
      ((ratio_le_endpoint_max p path after between.1 between.2).trans bound)
    intro work hw
    exact (redo_mono p handoff threshold work amount.2).trans (withRedo work hw)

private theorem at_late_le_simple (p : Prices) {handoff delay redo threshold : ℝ}
    (h : 0 ≤ handoff) (d : 0 ≤ redo)
    (early : breakEven p ≤ threshold) (late : threshold ≤ breakEven p + delay) :
    atSwitch p (charge p handoff redo h d) threshold ≤
      1 + gap p + (handoff + gap p * delay + p.q * redo) / breakEven p := by
  have bpos := breakEven_pos p
  have tpos := bpos.trans_le early
  have enough : breakEven p ≤ native p threshold := by
    rw [← native_at_breakEven p]
    unfold native
    gcongr
    exact p.q_pos.le
  have multiply := mul_le_mul_of_nonneg_left late (gap_pos p).le
  have numerator : handoff + p.q * redo + gap p * threshold ≤
      gap p * breakEven p + (handoff + gap p * delay + p.q * redo) := by
    linarith only [multiply]
  rw [atSwitch_after p _ _ tpos early]
  simp only [charge, resume]
  have dec := div_le_div_of_nonneg_left
    (add_nonneg (add_nonneg h (mul_nonneg p.q_pos.le d)) (mul_nonneg (gap_pos p).le tpos.le)) bpos enough
  calc
    _ ≤ 1 + (handoff + p.q * redo + gap p * threshold) / breakEven p :=
      add_le_add (le_refl _) dec
    _ ≤ 1 + (gap p * breakEven p + (handoff + gap p * delay + p.q * redo)) / breakEven p :=
      add_le_add (le_refl _) (div_le_div_of_nonneg_right numerator bpos.le)
    _ = _ := by field_simp [bpos.ne']; ring

theorem delay_and_rewind_bound (p : Prices) {handoff delay redo : ℝ}
    (h : 0 ≤ handoff) (e : 0 ≤ delay) (d : 0 ≤ redo) :
    ∀ threshold ∈ Set.Icc (breakEven p) (breakEven p + delay),
      ∀ actual ∈ Set.Icc 0 redo,
      Competitive p (checkpointCost p handoff actual threshold)
        (1 + gap p + (handoff + gap p * delay + p.q * redo) / breakEven p) := by
  have ordered : breakEven p ≤ breakEven p + delay := le_add_of_nonneg_right e
  apply (envelope_competitive_iff p h d le_rfl ordered _).mpr
  exact max_le (at_late_le_simple p h d le_rfl ordered)
    (at_late_le_simple p h d ordered le_rfl)

/-- On a call long enough for both choices, the trade is exact. This is
pointwise, not the adversarial bound above. -/
theorem wait_beats_rewind_iff (p : Prices) (earlyH lateH redo first delay work : ℝ)
    (e : 0 ≤ delay) (ready : first + delay ≤ work) :
    checkpointCost p lateH 0 (first + delay) work < checkpointCost p earlyH redo first work ↔
      lateH + gap p * delay < earlyH + p.q * redo := by
  have earlier : first ≤ work := (le_add_of_nonneg_right e).trans ready
  simp only [checkpointCost, if_neg (not_lt.mpr ready), if_neg (not_lt.mpr earlier), add_zero, gap]
  constructor <;> intro order <;> nlinarith only [order]

namespace Controls

def half : Prices := ⟨100, 1 / 2, by norm_num, by norm_num, by norm_num⟩

theorem partial_rewind_cost :
    checkpointCost half 20 40 200 200 = 340 ∧ offline half 200 = 200 := by
  norm_num [checkpointCost, offline, native, half, min_def]

/-- With enough transfer overhead, later can improve the ratio even when
the same invocation would pay more absolute work. -/
theorem worst_boundary_can_be_first :
    atSwitch half (resume half 200 (by norm_num)) 300 <
      atSwitch half (resume half 200 (by norm_num)) 200 := by
  norm_num [atSwitch, switched, native, offline, resume, gap, half, min_def]

end Controls
end

section VisibleTrace

variable {Event : Type*}

/-- The earliest cut past all of the observed events. Empty batches
represent unobserved work. Their presence does not move a checkpoint. -/
def replayFloor : List (List Event) → Nat
  | [] => 0
  | events :: rest =>
      if replayFloor rest = 0 ∧ events.isEmpty then 0 else replayFloor rest + 1

/-- Rewind cannot cross an observation even if the replayed observations
have equal payloads. A cut at the floor is allowed, not just later cuts. -/
theorem silent_suffix_iff (batches : List (List Event)) (cut : Nat) :
    (batches.drop cut).flatten = [] ↔ replayFloor batches ≤ cut := by
  induction batches generalizing cut with
  | nil => simp [replayFloor]
  | cons events rest ih =>
      cases events with
      | nil =>
          by_cases noLater : replayFloor rest = 0
          · have quiet : rest.flatten = [] := (ih 0).mpr (by simp [noLater])
            cases cut with
            | zero => simp [replayFloor, noLater, quiet]
            | succ cut => simp [replayFloor, noLater, ih]
          · cases cut with
            | zero =>
                change rest.flatten = [] ↔ replayFloor ([] :: rest) ≤ 0
                rw [show rest.flatten = ([] : List Event) ↔ replayFloor rest ≤ 0 by
                  simpa only [List.drop_zero] using ih 0]
                simp [replayFloor, noLater]
            | succ cut => simp [replayFloor, noLater, ih]
      | cons event events =>
          cases cut with
          | zero => simp [replayFloor]
          | succ cut => simp [replayFloor, ih]

theorem replay_floor_in_bounds (batches : List (List Event)) : replayFloor batches ≤ batches.length := by
  apply (silent_suffix_iff batches batches.length).mp
  simp

/-- Assume the saved state and read view justify replaying the same
steps. Their observed trace can be appended again without changing any
whole observation exactly at the cuts above. State reconstruction and
read-view validity are separate from this trace test. -/
theorem replay_preserves_observed_trace_iff (batches : List (List Event))
    (past future : List Event) (cut : Nat) :
    past ++ (batches.drop cut).flatten ++ future = past ++ future ↔ replayFloor batches ≤ cut := by
  rw [← silent_suffix_iff]
  constructor
  · intro same
    have size := congrArg List.length same
    simp only [List.length_append] at size
    exact List.length_eq_zero_iff.mp (by omega)
  · intro quiet
    simp [quiet]

theorem duplicate_publication_has_no_early_rewind :
    replayFloor ([[], [7], [], [7], [], []] : List (List Nat)) = 4 := by decide

end VisibleTrace

end Mettapedia.Machines.TierUpCheckpoint
