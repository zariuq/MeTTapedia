import Mathlib.Tactic

/-!
# Survival-sensitive nursery headroom

The nursery starts with a small sample and grows with measured retained work:
the surviving heap plus the root inventory that a collection scans. A large continuation can have
many roots pointing to one small shared value, so roots must be charged too.
The configured budget bounds fresh nursery headroom, not the live graph.
An additional retained-work interval pays for scanning the roots and copying
an old live graph; pressure adds at most another such interval.

The bounds concern accounted arena storage between safe points. They do not
bound process RSS, an unbounded instruction's allocation burst, or allocations
whose owners have no collection boundary. Semantic collection obligations are
separate from this scheduling arithmetic.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SurvivorBudget

def nursery (configured seed retained : Nat) : Nat :=
  min configured (max seed retained)

def threshold (configured seed retained pressure : Nat) : Nat :=
  retained + nursery configured seed retained + pressure

theorem nursery_le_configured (configured seed retained : Nat) :
    nursery configured seed retained ≤ configured := by
  unfold nursery
  omega

theorem nursery_le_sample_or_retained (configured seed retained : Nat) :
    nursery configured seed retained ≤ max seed retained := by
  unfold nursery
  omega

theorem nursery_mono_retained (configured seed small large : Nat)
    (grows : small ≤ large) :
    nursery configured seed small ≤ nursery configured seed large := by
  unfold nursery
  omega

theorem root_inventory_increases_headroom (configured seed live small large pressure : Nat)
    (grows : small ≤ large) :
    threshold configured seed (live + small) pressure ≤
      threshold configured seed (live + large) pressure := by
  have monotone := nursery_mono_retained configured seed (live + small) (live + large)
    (Nat.add_le_add_left grows live)
  unfold threshold
  omega

theorem first_sample (configured seed : Nat) :
    threshold configured seed 0 0 = min configured seed := by
  simp [threshold, nursery]

theorem transient_headroom (configured seed retained pressure : Nat)
    (small : retained ≤ seed) (pressureBound : pressure ≤ retained) :
    threshold configured seed retained pressure ≤ seed + 2 * retained := by
  unfold threshold nursery
  omega

theorem live_graph_is_not_capped (configured seed retained pressure : Nat) :
    retained ≤ threshold configured seed retained pressure := by
  unfold threshold
  omega

theorem threshold_le_configured_and_live (configured seed retained pressure : Nat)
    (pressureBound : pressure ≤ retained) :
    threshold configured seed retained pressure ≤ configured + 2 * retained := by
  have bound := nursery_le_configured configured seed retained
  unfold threshold
  omega

theorem growing_live_headroom (configured seed retained pressure : Nat)
    (large : seed ≤ retained) (pressureBound : pressure ≤ retained) :
    threshold configured seed retained pressure ≤ 3 * retained := by
  unfold threshold nursery
  omega

/-- Bounded survival and bounded safe-point bursts give a bound independent
of the number of loop iterations. The old survivor arena is counted too. -/
theorem accounted_peak (configured seed retained pressure allocated burst liveBound : Nat)
    (survivalBound : retained ≤ liveBound)
    (pressureBound : pressure ≤ retained)
    (safePoint : allocated ≤ threshold configured seed retained pressure + burst) :
    retained + allocated ≤ seed + 4 * liveBound + burst := by
  unfold threshold nursery at safePoint
  omega

theorem accounted_peak_with_roots (configured seed live roots pressure allocated burst
    liveBound rootBound : Nat)
    (heapBound : live ≤ liveBound) (rootsBound : roots ≤ rootBound)
    (pressureBound : pressure ≤ live + roots)
    (safePoint : allocated ≤ threshold configured seed (live + roots) pressure + burst) :
    live + roots + allocated ≤ seed + 4 * (liveBound + rootBound) + burst := by
  exact accounted_peak configured seed (live + roots) pressure allocated burst
    (liveBound + rootBound) (Nat.add_le_add heapBound rootsBound) pressureBound safePoint

def saturatingAdd (maximum left right : Nat) : Nat := min maximum (left + right)

def saturatingProduct (maximum count width : Nat) : Nat := min maximum (count * width)

theorem guarded_product_eq_saturation (maximum count width : Nat) :
    (if width = 0 then count * width
      else if maximum / width < count then maximum else count * width) =
      saturatingProduct maximum count width := by
  unfold saturatingProduct
  by_cases zero : width = 0
  · simp [zero]
  · have positive : 0 < width := Nat.pos_of_ne_zero zero
    simp only [zero, ↓reduceIte]
    by_cases overflow : maximum / width < count
    · have large : maximum < count * width := by
        by_contra bounded
        have fits : count * width ≤ maximum := by omega
        have quotient := (Nat.le_div_iff_mul_le positive).mpr fits
        omega
      simp [overflow, Nat.min_eq_left (by omega : maximum ≤ count * width)]
    · have quotient : count ≤ maximum / width := by omega
      have fits := (Nat.le_div_iff_mul_le positive).mp quotient
      simp [overflow, Nat.min_eq_right fits]

/-- The overflow guard in the native size-word addition realizes saturation,
rather than wrapping a large collection threshold back to a small one. -/
theorem guarded_add_eq_saturation (maximum left right : Nat)
    (leftBound : left ≤ maximum) :
    (if maximum - left < right then maximum else left + right) =
      saturatingAdd maximum left right := by
  unfold saturatingAdd
  split <;> omega

theorem saturatingAdd_preserves_left (maximum left right : Nat)
    (leftBound : left ≤ maximum) :
    left ≤ saturatingAdd maximum left right := by
  unfold saturatingAdd
  omega

theorem saturatingAdd_exact (maximum left right : Nat)
    (fits : left + right ≤ maximum) :
    saturatingAdd maximum left right = left + right := by
  unfold saturatingAdd
  omega

theorem saturated_threshold_keeps_live_floor (maximum configured seed retained pressure : Nat)
    (liveFits : retained ≤ maximum) :
    retained ≤ saturatingAdd maximum
      (saturatingAdd maximum retained (nursery configured seed retained)) pressure := by
  have first := saturatingAdd_preserves_left maximum retained
    (nursery configured seed retained) liveFits
  have fits : saturatingAdd maximum retained (nursery configured seed retained) ≤ maximum :=
    Nat.min_le_left _ _
  exact first.trans (saturatingAdd_preserves_left _ _ _ fits)

/-- Newly surviving cells came from this interval's allocations. Older cells
are recopied only after at least one old-live-graph's worth of allocation. -/
structure Phase where
  heapLive : Nat
  rootScan : Nat
  newLive : Nat
  allocated : Nat

def copyWork (phase : Phase) : Nat := phase.heapLive + phase.rootScan + phase.newLive

def Admitted (configured seed pressure : Nat) (phase : Phase) : Prop :=
  threshold configured seed (phase.heapLive + phase.rootScan) pressure ≤ phase.allocated ∧
    phase.newLive ≤ phase.allocated

theorem phase_copy_amortized (configured seed pressure : Nat) (phase : Phase)
    (admitted : Admitted configured seed pressure phase) :
    copyWork phase ≤ 2 * phase.allocated := by
  have oldBound := live_graph_is_not_capped configured seed
    (phase.heapLive + phase.rootScan) pressure
  unfold Admitted at admitted
  unfold copyWork
  omega

/-- Copying work over any finite sequence is linear in accounted allocation,
including phases in which the live graph grows. -/
theorem trace_copy_amortized (configured seed : Nat) (phases : List Phase)
    (admitted : ∀ phase ∈ phases, ∃ pressure, Admitted configured seed pressure phase) :
    (phases.map copyWork).sum ≤ 2 * (phases.map Phase.allocated).sum := by
  induction phases with
  | nil => simp
  | cons phase rest ih =>
      obtain ⟨pressure, one⟩ := admitted phase (by simp)
      have bound := phase_copy_amortized configured seed pressure phase one
      have tail := ih (fun p hp => admitted p (by simp [hp]))
      simp only [List.map_cons, List.sum_cons]
      omega

namespace Controls

theorem transient_constructors_do_not_get_three_large_nurseries :
    threshold 256 16 0 0 = 16 ∧ threshold 256 16 0 0 < 3 * 256 := by decide

theorem genuinely_live_structure_grows_the_nursery :
    nursery 256 16 128 = 128 ∧ threshold 256 16 128 128 = 384 := by decide

theorem live_data_may_exceed_the_configured_nursery :
    1024 > 256 ∧ threshold 256 16 1024 0 = 1280 := by decide

theorem overflow_does_not_make_an_early_collection_loop :
    saturatingAdd 255 250 20 = 255 ∧ saturatingAdd 255 250 20 ≠ 14 := by decide

theorem collecting_every_fixed_quantum_does_not_pay_for_large_live_graphs :
    ¬ Admitted 256 16 0 ⟨1024, 0, 0, 16⟩ := by
  simp [Admitted, threshold, nursery]

theorem a_small_heap_does_not_make_a_large_root_inventory_free :
    ¬ Admitted 256 16 0 ⟨0, 1024, 0, 16⟩ := by
  simp [Admitted, threshold, nursery]

theorem a_large_safe_point_burst_is_a_real_obligation :
    1000 > threshold 256 16 0 0 + 1 := by decide

end Controls
end Mettapedia.Machines.SurvivorBudget
