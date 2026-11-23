import Mettapedia.Machines.CollectionHeadroom

/-!
# Collection work while the persistent result grows

An interval of `h` allocations adds `growth * h` permanent live units. A
schedule ends at a collection; the headrooms are the allocated amounts
between collections. Full copying visits the *post*-growth live size. These
assumptions model a growing result phase, not general GC or peak process RSS.

An absolute bound on allocations between collections forces quadratic copy
work when growth is positive. A relative bound admits a geometric schedule
whose *total* copy work is linear in allocations. Promotion changes which
part of the bill remains sensitive to the schedule: fresh copies depend on
survivor growth, but the per-collection root charge depends on headroom.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GrowingSurvivorSchedule

def copyWork (growth live : ℝ) : List ℝ → ℝ
  | [] => 0
  | fresh :: rest =>
      let next := live + growth * fresh
      next + copyWork growth next rest

def constantCap (cap : ℝ) (windows : List ℝ) : Prop :=
  ∀ h ∈ windows, 0 ≤ h ∧ h ≤ cap

def relativeCap (factor growth live : ℝ) : List ℝ → Prop
  | [] => True
  | fresh :: rest => 0 ≤ fresh ∧ fresh ≤ factor * live ∧
      relativeCap factor growth (live + growth * fresh) rest

def unusedRelative (factor growth live : ℝ) : List ℝ → ℝ
  | [] => 0
  | fresh :: rest => factor * live - fresh +
      unusedRelative factor growth (live + growth * fresh) rest

/-- Every gap smaller than the relative budget increases the copy bill by
its unused headroom, divided by the factor (if positive). -/
theorem relative_copy_account (factor growth live : ℝ) (windows : List ℝ) :
    factor * copyWork growth live windows =
      (1 + factor * growth) * windows.sum + unusedRelative factor growth live windows := by
  induction windows generalizing live with
  | nil => simp [copyWork, unusedRelative]
  | cons fresh rest ih =>
      simp only [copyWork, unusedRelative, List.sum_cons]
      linear_combination ih (live + growth * fresh)

theorem unusedRelative_nonneg (factor growth live : ℝ) (windows : List ℝ)
    (fits : relativeCap factor growth live windows) : 0 ≤ unusedRelative factor growth live windows := by
  induction windows generalizing live with
  | nil => simp [unusedRelative]
  | cons fresh rest ih =>
      obtain ⟨_, bound, later⟩ := fits
      exact add_nonneg (sub_nonneg.mpr bound) (ih _ later)

theorem relative_copy_lower_bound (factor growth live : ℝ) (windows : List ℝ)
    (fits : relativeCap factor growth live windows) :
    (1 + factor * growth) * windows.sum ≤ factor * copyWork growth live windows := by
  rw [relative_copy_account]
  exact le_add_of_nonneg_right (unusedRelative_nonneg factor growth live windows fits)

def geometric (factor growth live : ℝ) : Nat → List ℝ
  | 0 => []
  | n + 1 => (factor * live) :: geometric factor growth (live + growth * (factor * live)) n

theorem geometric_fits (factor growth live : ℝ) (n : Nat)
    (hf : 0 ≤ factor) (hg : 0 ≤ growth) (hl : 0 ≤ live) :
    relativeCap factor growth live (geometric factor growth live n) := by
  induction n generalizing live with
  | zero => exact ⟨⟩
  | succ n ih =>
      have fresh := mul_nonneg hf hl
      exact ⟨fresh, le_rfl, ih _ (add_nonneg hl (mul_nonneg hg fresh))⟩

theorem geometric_live (factor growth live : ℝ) (n : Nat) :
    live + growth * (geometric factor growth live n).sum = live * (1 + growth * factor) ^ n := by
  induction n generalizing live with
  | zero => simp [geometric]
  | succ n ih =>
      simp only [geometric, List.sum_cons, pow_succ]
      linear_combination ih (live + growth * (factor * live))

theorem geometric_attains (factor growth live : ℝ) (n : Nat) :
    factor * copyWork growth live (geometric factor growth live n) =
      (1 + factor * growth) * (geometric factor growth live n).sum := by
  have full : ∀ (count : Nat) (initial : ℝ),
      unusedRelative factor growth initial (geometric factor growth initial count) = 0 := by
    intro count
    induction count with
    | zero => intro initial; rfl
    | succ count ih => intro initial; simp [geometric, unusedRelative, ih]
  rw [relative_copy_account, full, add_zero]

/-- At the horizons reached by full relative windows, geometric spacing
minimizes full-copy work, even among schedules with a different number of
collections. No optimality is asserted for a truncated final window. -/
theorem geometric_optimal_at_its_horizons (factor growth live : ℝ) (n : Nat)
    (other : List ℝ) (hf : 0 < factor) (fits : relativeCap factor growth live other)
    (horizon : other.sum = (geometric factor growth live n).sum) :
    copyWork growth live (geometric factor growth live n) ≤ copyWork growth live other := by
  apply le_of_mul_le_mul_left ?_ hf
  rw [geometric_attains, ← horizon]
  exact relative_copy_lower_bound factor growth live other fits

/-! ## A required final collection changes where the partial interval goes -/

/-- Moving fresh allocations from one window into the next reduces exactly
the live growth charged at the intervening collection. The rest of the run
starts with the same live size. -/
theorem shift_work_exact (growth live earlier later moved : ℝ) (rest : List ℝ) :
    copyWork growth live (earlier :: later :: rest) =
      copyWork growth live ((earlier - moved) :: (later + moved) :: rest) + growth * moved := by
  simp only [copyWork]
  have same : live + growth * earlier + growth * later =
      live + growth * (earlier - moved) + growth * (later + moved) := by ring
  rw [same]
  ring

theorem shift_preserves_relative_cap (factor growth live earlier later moved : ℝ) (rest : List ℝ)
    (fits : relativeCap factor growth live (earlier :: later :: rest))
    (hm : 0 ≤ moved) (available : moved ≤ earlier)
    (room : (1 + factor * growth) * moved ≤ factor * (live + growth * earlier) - later) :
    relativeCap factor growth live ((earlier - moved) :: (later + moved) :: rest) := by
  obtain ⟨_, earlyBound, laterNonneg, _, restCap⟩ := fits
  have same : live + growth * (earlier - moved) + growth * (later + moved) =
      live + growth * earlier + growth * later := by ring
  have laterBound : later + moved ≤ factor * (live + growth * (earlier - moved)) := by
    linarith only [room]
  refine ⟨sub_nonneg.mpr available, (sub_le_self _ hm).trans earlyBound,
    add_nonneg laterNonneg hm, laterBound, ?_⟩
  rw [same]
  exact restCap

def LeastCopyAt (factor growth live : ℝ) (windows : List ℝ) : Prop :=
  ∀ other : List ℝ, relativeCap factor growth live other → other.sum = windows.sum →
    copyWork growth live windows ≤ copyWork growth live other

private theorem following_window_full (factor growth live earlier later : ℝ) (rest : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 < growth) (positive : 0 < earlier)
    (fits : relativeCap factor growth live (earlier :: later :: rest))
    (best : LeastCopyAt factor growth live (earlier :: later :: rest)) :
    later = factor * (live + growth * earlier) := by
  by_contra notFull
  have laterBound : later ≤ factor * (live + growth * earlier) := fits.2.2.2.1
  have spare : 0 < factor * (live + growth * earlier) - later :=
    sub_pos.mpr (lt_of_le_of_ne laterBound notFull)
  have scale : 0 < 1 + factor * growth := by positivity
  let moved := min earlier ((factor * (live + growth * earlier) - later) / (1 + factor * growth))
  have movedPos : 0 < moved := lt_min positive (div_pos spare scale)
  have room : (1 + factor * growth) * moved ≤ factor * (live + growth * earlier) - later := by
    rw [mul_comm]
    apply (le_div_iff₀ scale).mp
    exact min_le_right _ _
  have shifted := shift_preserves_relative_cap factor growth live earlier later moved rest
    fits movedPos.le (min_le_left _ _) room
  have sameHorizon : ((earlier - moved) :: (later + moved) :: rest).sum =
      (earlier :: later :: rest).sum := by simp only [List.sum_cons]; ring
  have least := best _ shifted sameHorizon
  rw [shift_work_exact growth live earlier later moved rest] at least
  linarith only [least, mul_pos hg movedPos]

def FullRelative (factor growth live : ℝ) : List ℝ → Prop
  | [] => True
  | fresh :: rest =>
      fresh = factor * live ∧ FullRelative factor growth (live + growth * fresh) rest

/-- Any minimizing positive schedule is full from its second interval
onward. In this finite-horizon problem the partial window, if any, must
come *first*, not at the forced terminal collection. -/
theorem optimal_remainder_full (factor growth live first : ℝ) (rest : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 < growth)
    (positive : ∀ h ∈ first :: rest, 0 < h)
    (fits : relativeCap factor growth live (first :: rest))
    (best : LeastCopyAt factor growth live (first :: rest)) :
    FullRelative factor growth (live + growth * first) rest := by
  induction rest generalizing live first with
  | nil => exact ⟨⟩
  | cons second rest ih =>
      have full := following_window_full factor growth live first second rest hf hg
        (positive _ (by simp)) fits best
      have suffixBest : LeastCopyAt factor growth (live + growth * first) (second :: rest) := by
        intro other allowed horizon
        have better := best (first :: other) ⟨fits.1, fits.2.1, allowed⟩
          (congrArg (first + ·) horizon)
        exact le_of_add_le_add_left better
      exact ⟨full, ih _ _ (fun h member => positive h (List.mem_cons_of_mem _ member)) fits.2.2 suffixBest⟩

private theorem end_le_geometric (factor growth live : ℝ) (windows : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 ≤ growth) (fits : relativeCap factor growth live windows) :
    live + growth * windows.sum ≤ live * (1 + growth * factor) ^ windows.length := by
  induction windows generalizing live with
  | nil => simp
  | cons fresh rest ih =>
      have first := mul_le_mul_of_nonneg_left fits.2.1 hg
      have next : live + growth * fresh ≤ live * (1 + growth * factor) := by linarith
      have future := ih _ fits.2.2
      simp only [List.sum_cons, List.length_cons, pow_succ']
      calc
        live + growth * (fresh + rest.sum) = live + growth * fresh + growth * rest.sum := by ring
        _ ≤ (live + growth * fresh) * (1 + growth * factor) ^ rest.length := future
        _ ≤ (live * (1 + growth * factor)) * (1 + growth * factor) ^ rest.length :=
          mul_le_mul_of_nonneg_right next (by positivity)
        _ = _ := by ring

private theorem end_eq_geometric (factor growth live : ℝ) (windows : List ℝ)
    (full : FullRelative factor growth live windows) :
    live + growth * windows.sum = live * (1 + growth * factor) ^ windows.length := by
  induction windows generalizing live with
  | nil => simp
  | cons fresh rest ih =>
      have later := ih _ full.2
      rw [full.1] at later ⊢
      simp only [List.sum_cons, List.length_cons, pow_succ']
      linear_combination later

/-- Looking backward from the final collection gives a lower bound for
each earlier visit: it must leave enough live data to reach the endpoint
under the remaining geometric growth caps. -/
noncomputable def terminalFloor (factor growth final : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => final / (1 + growth * factor) ^ n + terminalFloor factor growth final n

theorem terminal_floor_lower_bound (factor growth live : ℝ) (windows : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 ≤ growth) (fits : relativeCap factor growth live windows) :
    terminalFloor factor growth (live + growth * windows.sum) windows.length ≤ copyWork growth live windows := by
  induction windows generalizing live with
  | nil => rfl
  | cons fresh rest ih =>
      have same : live + growth * (fresh + rest.sum) = live + growth * fresh + growth * rest.sum := by ring
      have first := (div_le_iff₀ (by positivity : 0 < (1 + growth * factor) ^ rest.length)).mpr
        (end_le_geometric factor growth (live + growth * fresh) rest hf hg fits.2.2)
      simpa only [terminalFloor, List.length_cons, List.sum_cons, same, copyWork] using
        add_le_add first (ih _ fits.2.2)

private theorem terminal_floor_attained (factor growth live first : ℝ) (rest : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 ≤ growth)
    (full : FullRelative factor growth (live + growth * first) rest) :
    terminalFloor factor growth (live + growth * (first :: rest).sum) (first :: rest).length =
      copyWork growth live (first :: rest) := by
  induction rest generalizing live first with
  | nil => simp [terminalFloor, copyWork]
  | cons second rest ih =>
      have endPoint := end_eq_geometric factor growth (live + growth * first) (second :: rest) full
      have power : 0 < (1 + growth * factor) ^ (second :: rest).length := by positivity
      have firstCost := (div_eq_iff power.ne').mpr endPoint
      have suffixCost := ih _ _ full.2
      have same : live + growth * (first :: second :: rest).sum =
          live + growth * first + growth * (second :: rest).sum := by simp only [List.sum_cons]; ring
      simp only [List.length_cons] at firstCost suffixCost ⊢
      rw [terminalFloor, same, firstCost, suffixCost]
      rfl

private theorem terminal_floor_mono (factor growth final : ℝ)
    (hf : 0 ≤ factor) (hg : 0 ≤ growth) (hn : 0 ≤ final) :
    Monotone (terminalFloor factor growth final) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [terminalFloor]
  exact le_add_of_nonneg_left (by positivity)

/-- The converse: a feasible positive first interval followed by full
relative intervals is globally best at its terminal live size. A shorter
schedule cannot reach that endpoint; any longer one must still pay at
least the same backward lower bound. -/
theorem full_remainder_is_best (factor growth live first : ℝ) (rest : List ℝ)
    (hf : 0 ≤ factor) (hg : 0 < growth) (hl : 0 ≤ live) (ha : 0 < first)
    (full : FullRelative factor growth (live + growth * first) rest) :
    LeastCopyAt factor growth live (first :: rest) := by
  intro other fits horizon
  let final := live + growth * (first :: rest).sum
  have terminal : final = (live + growth * first) * (1 + growth * factor) ^ rest.length := by
    calc
      final = live + growth * first + growth * rest.sum := by simp only [final, List.sum_cons]; ring
      _ = _ := end_eq_geometric factor growth _ rest full
  have past : live * (1 + growth * factor) ^ rest.length < final := by
    rw [terminal]
    exact mul_lt_mul_of_pos_right (lt_add_of_pos_right _ (mul_pos hg ha)) (by positivity)
  have feasible := end_le_geometric factor growth live other hf hg.le fits
  rw [horizon] at feasible
  have enough : (first :: rest).length ≤ other.length := by
    by_contra short
    have shorter : other.length ≤ rest.length := by simp only [List.length_cons] at short; omega
    have powers : (1 + growth * factor) ^ other.length ≤ (1 + growth * factor) ^ rest.length :=
      pow_le_pow_right₀ (by linarith [mul_nonneg hg.le hf]) shorter
    exact (not_le_of_gt past) (feasible.trans (mul_le_mul_of_nonneg_left powers hl))
  have finalNonneg : 0 ≤ final := by rw [terminal]; positivity
  calc
    copyWork growth live (first :: rest) = terminalFloor factor growth final (first :: rest).length :=
      (terminal_floor_attained factor growth live first rest hf hg.le full).symm
    _ ≤ terminalFloor factor growth final other.length := terminal_floor_mono factor growth final hf hg.le finalNonneg enough
    _ ≤ copyWork growth live other := by
      have lower := terminal_floor_lower_bound factor growth live other hf hg.le fits
      rwa [horizon] at lower

private theorem geometric_full (factor growth live : ℝ) (n : Nat) :
    FullRelative factor growth live (geometric factor growth live n) := by
  induction n generalizing live with
  | zero => exact ⟨⟩
  | succ n ih => exact ⟨rfl, ih _⟩

private theorem geometric_positive (factor growth live : ℝ) (n : Nat)
    (hf : 0 < factor) (hg : 0 ≤ growth) (hl : 0 < live) :
    ∀ h ∈ geometric factor growth live n, 0 < h := by
  induction n generalizing live with
  | zero => simp [geometric]
  | succ n ih =>
      intro h member
      rcases List.mem_cons.mp member with rfl | later
      · exact mul_pos hf hl
      · exact ih _ (by positivity) h later

/-- An optimal positive schedule exists for every positive horizon in
the continuous growing-set model. Start with the least possible number of
intervals, then compute the first one backward from the terminal size. -/
theorem exists_best_relative (factor growth live horizon : ℝ)
    (hf : 0 < factor) (hg : 0 < growth) (hl : 0 < live) (ht : 0 < horizon) :
    ∃ windows : List ℝ, windows.sum = horizon ∧ (∀ h ∈ windows, 0 < h) ∧
      relativeCap factor growth live windows ∧
      LeastCopyAt factor growth live windows := by
  classical
  let q := 1 + growth * factor
  let final := live + growth * horizon
  have hq : 1 < q := lt_add_of_pos_right _ (mul_pos hg hf)
  obtain ⟨count, bound⟩ := pow_unbounded_of_one_lt (final / live) hq
  have existsCount : ∃ n : Nat, final ≤ live * q ^ n :=
    ⟨count, by simpa only [mul_comm live] using (div_le_iff₀ hl).mp bound.le⟩
  have enough := Nat.find_spec existsCount
  cases chosen : Nat.find existsCount with
  | zero =>
      simp [chosen, final] at enough
      exact ((not_le_of_gt (mul_pos hg ht)) enough).elim
  | succ n =>
      have short : live * q ^ n < final := by
        apply lt_of_not_ge
        exact Nat.find_min existsCount (by rw [chosen]; omega)
      have high : final ≤ live * q ^ (n + 1) := by rwa [chosen] at enough
      let next := final / q ^ n
      have power : 0 < q ^ n := pow_pos (zero_lt_one.trans hq) _
      have nextGt : live < next := (lt_div_iff₀ power).mpr short
      have nextLe : next ≤ live * q := by
        apply (div_le_iff₀ power).mpr
        simpa only [pow_succ', mul_assoc] using high
      let first := (next - live) / growth
      have firstPos : 0 < first := div_pos (sub_pos.mpr nextGt) hg
      have fits : first ≤ factor * live := by
        apply (div_le_iff₀ hg).mpr
        dsimp [q] at nextLe
        linarith only [nextLe]
      have firstEnd : live + growth * first = next := by dsimp [first]; field_simp; ring
      let rest := geometric factor growth next n
      have sameEnd : live + growth * (first :: rest).sum = final := by
        rw [List.sum_cons, mul_add, ← add_assoc, firstEnd, geometric_live]
        exact div_mul_cancel₀ final power.ne'
      have sameHorizon : (first :: rest).sum = horizon := by
        exact mul_left_cancel₀ hg.ne' (add_left_cancel sameEnd)
      have full : FullRelative factor growth (live + growth * first) rest := by
        rw [firstEnd]
        exact geometric_full factor growth next n
      refine ⟨first :: rest, sameHorizon, ?_, ⟨firstPos.le, fits, ?_⟩,
        full_remainder_is_best factor growth live first rest hf.le hg hl.le firstPos full⟩
      · intro h member
        rcases List.mem_cons.mp member with rfl | later
        · exact firstPos
        · exact geometric_positive factor growth next n hf hg.le (hl.trans nextGt) h later
      · rw [firstEnd]
        exact geometric_fits factor growth next n hf.le hg.le (hl.trans nextGt).le

/-- Weight each post-growth visit by its number of new allocations. -/
def weightedVisits (growth live : ℝ) : List ℝ → ℝ
  | [] => 0
  | fresh :: rest =>
      let next := live + growth * fresh
      fresh * next + weightedVisits growth next rest

theorem weighted_visits_identity (growth live : ℝ) (windows : List ℝ) :
    2 * weightedVisits growth live windows =
      2 * live * windows.sum + growth * (windows.sum ^ 2 + (windows.map (· ^ 2)).sum) := by
  induction windows generalizing live with
  | nil => simp [weightedVisits]
  | cons fresh rest ih =>
      simp only [weightedVisits, List.map_cons, List.sum_cons]
      linear_combination ih (live + growth * fresh)

private theorem weightedVisits_le (growth live cap : ℝ) (windows : List ℝ)
    (hg : 0 ≤ growth) (hl : 0 ≤ live) (fits : constantCap cap windows) :
    weightedVisits growth live windows ≤ cap * copyWork growth live windows := by
  induction windows generalizing live with
  | nil => simp [weightedVisits, copyWork]
  | cons fresh rest ih =>
      have ⟨freshPos, freshBound⟩ := fits fresh (by simp)
      have nextPos : 0 ≤ live + growth * fresh := add_nonneg hl (mul_nonneg hg freshPos)
      have sooner := mul_le_mul_of_nonneg_right freshBound nextPos
      have later := ih _ nextPos (fun h member => fits h (List.mem_cons_of_mem _ member))
      simpa only [weightedVisits, copyWork, mul_add] using add_le_add sooner later

/-- No clever placement of collections removes the quadratic term under a
fixed positive spacing cap. Multiplying by twice the cap avoids division. -/
theorem fixed_cap_copy_lower_bound (growth live cap : ℝ) (windows : List ℝ)
    (hg : 0 ≤ growth) (hl : 0 ≤ live) (fits : constantCap cap windows) :
    2 * live * windows.sum + growth * (windows.sum ^ 2 + (windows.map (· ^ 2)).sum) ≤
      2 * cap * copyWork growth live windows := by
  rw [← weighted_visits_identity]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (weightedVisits_le growth live cap windows hg hl fits) (by norm_num : (0 : ℝ) ≤ 2)

/-- A full fixed-spacing run attains this quadratic order, with an exact
triangular copy term in addition to the initial live bytes. -/
theorem fixed_spacing_exact (growth live headroom : ℝ) (n : Nat) :
    2 * copyWork growth live (List.replicate n headroom) =
      2 * (n : ℝ) * live + growth * headroom * n * (n + 1) := by
  induction n generalizing live with
  | zero => simp [copyWork]
  | succ n ih =>
      simp only [List.replicate_succ, copyWork, Nat.cast_succ]
      linear_combination ih (live + growth * headroom)

/-- In the closed-old-region model, charge each distinct fresh survivor
once and charge a fixed root scan on each minor collection. -/
def promotedWork (growth rootCharge : ℝ) (windows : List ℝ) : ℝ :=
  growth * windows.sum + rootCharge * windows.length

theorem promoted_root_floor (growth rootCharge cap : ℝ) (windows : List ℝ)
    (hr : 0 ≤ rootCharge) (hc : 0 < cap) (fits : constantCap cap windows) :
    growth * windows.sum + rootCharge * (windows.sum / cap) ≤ promotedWork growth rootCharge windows := by
  have sumBound : windows.sum ≤ cap * (windows.length : ℝ) := by
    induction windows with
    | nil => simp
    | cons fresh rest ih =>
        have now := (fits fresh (by simp)).2
        have later := ih (fun h member => fits h (List.mem_cons_of_mem _ member))
        simp only [List.sum_cons, List.length_cons, Nat.cast_succ, mul_add, mul_one]
        linarith
  have collections : windows.sum / cap ≤ (windows.length : ℝ) :=
    (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using sumBound)
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left collections hr)

theorem promoted_fixed_spacing (growth rootCharge headroom : ℝ) (n : Nat) (hh : 0 < headroom) :
    promotedWork growth rootCharge (List.replicate n headroom) =
      growth * (n * headroom) + rootCharge * (n * headroom / headroom) := by
  simp [promotedWork, nsmul_eq_mul, hh.ne']

/-- With a price for peak nursery headroom, the horizon's allocation count
times the root charge is the pacing coefficient. The linear survivor charge
does not enter the optimum. The lower bound need not be attained when a
fixed horizon does not tile by the real-valued optimum. -/
theorem promoted_priced_lower_bound (growth rootCharge price cap : ℝ) (windows : List ℝ)
    (hr : 0 < rootCharge) (hp : 0 < price) (hc : 0 < cap) (hn : 0 < windows.sum)
    (fits : constantCap cap windows) :
    growth * windows.sum + CollectionHeadroom.cost price (rootCharge * windows.sum)
        (CollectionHeadroom.optimum price (rootCharge * windows.sum)) ≤
      price * cap + promotedWork growth rootCharge windows := by
  have balance := (CollectionHeadroom.optimum_unique hp (mul_pos hr hn) hc).1
  have scans := promoted_root_floor growth rootCharge cap windows hr.le hc fits
  simp only [CollectionHeadroom.cost, mul_div_assoc] at balance ⊢
  linarith

theorem promoted_priced_attains_when_tiles (growth rootCharge price horizon : ℝ) (n : Nat)
    (hr : 0 < rootCharge) (hp : 0 < price) (hn : 0 < horizon)
    (tiles : (n : ℝ) * CollectionHeadroom.optimum price (rootCharge * horizon) = horizon) :
    let best := CollectionHeadroom.optimum price (rootCharge * horizon)
    price * best + promotedWork growth rootCharge (List.replicate n best) =
      growth * horizon + CollectionHeadroom.cost price (rootCharge * horizon) best := by
  change price * CollectionHeadroom.optimum price (rootCharge * horizon) +
    promotedWork growth rootCharge
      (List.replicate n (CollectionHeadroom.optimum price (rootCharge * horizon))) = _
  rw [promoted_fixed_spacing _ _ _ _ (CollectionHeadroom.optimum_pos hp (mul_pos hr hn)), tiles]
  simp only [CollectionHeadroom.cost, mul_div_assoc]
  ring

namespace Controls

/-- Equal horizons and equal final live sizes, but one does repeatedly
copy the same persistent prefix. -/
theorem seven_allocations :
    (geometric 1 1 1 3).sum = 7 ∧
    copyWork 1 1 (geometric 1 1 1 3) = 14 ∧
    copyWork 1 1 (List.replicate 7 1) = 35 ∧
    promotedWork 1 0 (List.replicate 7 1) = 7 := by
  norm_num [geometric, copyWork, promotedWork, List.replicate]

/-- Equal terminal live size and the same number of collections. The
forward greedy schedule fills the first window; the better one fills the
second. This does not require any assumption about memory measurement. -/
theorem partial_last_can_lose :
    relativeCap 1 1 1 [1, 1 / 2] ∧ relativeCap 1 1 1 [1 / 4, 5 / 4] ∧
    ([1, 1 / 2] : List ℝ).sum = ([1 / 4, 5 / 4] : List ℝ).sum ∧
    copyWork 1 1 [1 / 4, 5 / 4] < copyWork 1 1 [1, 1 / 2] := by
  norm_num [relativeCap, copyWork]

end Controls
end Mettapedia.Machines.GrowingSurvivorSchedule
