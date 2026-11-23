import Mathlib.Tactic

/-!
# Paying for a plan at call boundaries

Subtract the cost common to both execution routes. Each call then has a
nonnegative saving available if a valid compiled route is used instead
of the generic route. Charging compilation against these *net* savings
accounts for entry validation without ever replaying an earlier call.
Only the next call's saving, not the future invocation sequence, is
visible to the lookahead algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallBoundaryReuse

def offlineExtra (compile : Nat) (savings : List Nat) : Nat := min compile savings.sum

/-- One compile, after interpreting an initial prefix; never compiling
corresponds to the whole list. Compiling again at the same valid key adds
no possible saving in this model. -/
def plannedExtra (compile : Nat) (savings : List Nat) (prefixLength : Nat) : Nat :=
  if prefixLength < savings.length then (savings.take prefixLength).sum + compile else savings.sum

theorem offline_le_plan (compile prefixLength : Nat) (savings : List Nat) :
    offlineExtra compile savings ≤ plannedExtra compile savings prefixLength := by
  unfold offlineExtra plannedExtra
  split
  · exact (min_le_left _ _).trans (Nat.le_add_left _ _)
  · exact min_le_right _ _

theorem offline_attained (compile : Nat) (savings : List Nat) :
    ∃ prefixLength, plannedExtra compile savings prefixLength = offlineExtra compile savings := by
  by_cases cheaper : compile < savings.sum
  · have notEmpty : 0 < savings.length := by
      cases savings <;> simp_all
    exact ⟨0, by simp [plannedExtra, offlineExtra, notEmpty, min_eq_left cheaper.le]⟩
  · exact ⟨savings.length, by simp [plannedExtra, offlineExtra, min_eq_right (le_of_not_gt cheaper)]⟩

/-- Inspect the next call's saving before dispatch. Buy once before the
first call that would push the interpreted debit to the compile price. -/
def lookahead (compile credit : Nat) : List Nat → Nat
  | [] => 0
  | net :: rest =>
      if compile ≤ credit + net then compile else net + lookahead compile (credit + net) rest

theorem lookahead_spec (compile credit : Nat) (savings : List Nat) (cold : credit < compile) :
    (credit + savings.sum < compile → lookahead compile credit savings = savings.sum) ∧
    (compile ≤ credit + savings.sum →
      ∃ spent, credit + spent < compile ∧ lookahead compile credit savings = spent + compile) := by
  induction savings generalizing credit with
  | nil => simp [lookahead, Nat.not_le.mpr cold]
  | cons net rest ih =>
      by_cases reached : compile ≤ credit + net
      · simp only [lookahead, if_pos reached, List.sum_cons]
        constructor
        · omega
        · intro _
          exact ⟨0, by simpa using cold, by simp⟩
      · have induction := ih (credit + net) (by omega)
        simp only [lookahead, if_neg reached, List.sum_cons]
        constructor
        · intro small
          rw [induction.1 (by omega)]
        · intro large
          obtain ⟨spent, bounded, valid⟩ := induction.2 (by omega)
          refine ⟨net + spent, by omega, ?_⟩
          rw [valid, Nat.add_assoc]

/-- The off-line baseline is attained by a real dispatch plan. The online
bound is on the extra cost *over* unavoidable execution work. -/
theorem lookahead_bound (compile : Nat) (savings : List Nat) (positive : 0 < compile) :
    lookahead compile 0 savings ≤ 2 * offlineExtra compile savings ∧
    (savings.sum < compile → lookahead compile 0 savings = offlineExtra compile savings) ∧
    (compile ≤ savings.sum → lookahead compile 0 savings < 2 * offlineExtra compile savings) := by
  have ⟨early, late⟩ := lookahead_spec compile 0 savings positive
  constructor
  · by_cases small : savings.sum < compile
    · simp [offlineExtra, min_eq_right small.le, early (by simpa using small)]
      omega
    · obtain ⟨spent, bound, same⟩ := late (by omega)
      rw [same, offlineExtra, min_eq_left (by omega : compile ≤ savings.sum)]
      omega
  · constructor
    · intro small
      rw [offlineExtra, min_eq_right small.le, early (by simpa using small)]
    · intro large
      obtain ⟨spent, bound, same⟩ := late (by simpa using large)
      rw [same, offlineExtra, min_eq_left large]
      omega

/-- Seeing only previous debits: if the next debit is arbitrarily large,
the caller has already paid it when it detects the crossover. -/
def retrospective (compile credit : Nat) : List Nat → Nat
  | [] => 0
  | net :: rest =>
      if compile ≤ credit then compile else net + retrospective compile (credit + net) rest

theorem unbounded_overshoot_without_lookahead (compile multiple : Nat) (positive : 0 < compile) :
    ∃ saving : Nat, multiple * offlineExtra compile [saving] < retrospective compile 0 [saving] := by
  let saving := multiple * compile + 1
  refine ⟨saving, ?_⟩
  simp only [offlineExtra, List.sum_singleton, retrospective, if_neg (Nat.not_le_of_lt positive), add_zero]
  have paid := Nat.mul_le_mul_left multiple (min_le_left compile saving)
  exact paid.trans_lt (Nat.lt_succ_self _)

private theorem retrospect_small (compile credit : Nat) (savings : List Nat)
    (small : credit + savings.sum < compile) :
    retrospective compile credit savings = savings.sum := by
  induction savings generalizing credit with
  | nil => rfl
  | cons net rest ih =>
      have before : ¬ compile ≤ credit := by simp only [List.sum_cons] at small; omega
      have later : credit + net + rest.sum < compile := by simpa [Nat.add_assoc] using small
      simp [retrospective, before, ih _ later]

private theorem retrospect_overshoot (compile credit maximum : Nat) (savings : List Nat)
    (cold : credit < compile) (bounded : ∀ net ∈ savings, net ≤ maximum) :
    credit + retrospective compile credit savings < 2 * compile + maximum := by
  induction savings generalizing credit with
  | nil => simp only [retrospective, Nat.add_zero]; omega
  | cons net rest ih =>
      rw [retrospective, if_neg (not_le.mpr cold)]
      have head := bounded net (by simp)
      by_cases crossed : compile ≤ credit + net
      · have done : retrospective compile (credit + net) rest ≤ compile := by
          cases rest <;> simp [retrospective, crossed]
        omega
      · have done := ih (credit + net) (lt_of_not_ge crossed)
          (fun cost present => bounded cost (List.mem_cons_of_mem net present))
        omega

/-- Without exact previews, only the crossing call can overshoot. A
known upper bound on that debit yields an additive, not a gratuitous
multiplicative, allowance. Small histories still pay exactly their debit. -/
theorem retrospective_bounded (compile maximum : Nat) (savings : List Nat)
    (positive : 0 < compile) (bounded : ∀ net ∈ savings, net ≤ maximum) :
    (savings.sum < compile → retrospective compile 0 savings = offlineExtra compile savings) ∧
    (compile ≤ savings.sum → retrospective compile 0 savings < 2 * offlineExtra compile savings + maximum) := by
  constructor
  · intro small
    rw [offlineExtra, min_eq_right small.le, retrospect_small compile 0 savings (by simpa using small)]
  · intro large
    simpa [offlineExtra, min_eq_left large] using retrospect_overshoot compile 0 maximum savings positive bounded

private theorem unit_crossing (compile credit calls : Nat)
    (cold : credit < compile) (exactly : credit + calls = compile) :
    lookahead compile credit (List.replicate calls 1) = calls - 1 + compile := by
  induction calls generalizing credit with
  | zero => omega
  | succ calls ih =>
      rw [List.replicate_succ, lookahead]
      by_cases reached : compile ≤ credit + 1
      · rw [if_pos reached]
        omega
      · rw [if_neg reached, ih (credit + 1) (by omega) (by omega)]
        omega

/-- Discrete sharpness for this policy; continuation is unknown even
though the price of each call is visible at its entry. -/
theorem unit_history_hits_worst_case (compile : Nat) (positive : 0 < compile) :
    lookahead compile 0 (List.replicate compile 1) = 2 * compile - 1 ∧
      offlineExtra compile (List.replicate compile 1) = compile := by
  constructor
  · rw [unit_crossing compile 0 compile positive (by simp)]
    omega
  · simp [offlineExtra]

/-! ## Paying for invalidation, even with an optimal compiler -/

/-- Splitting an actually reusable generation into two independent pieces
cannot lower optimal extra cost. This compares one price and does not
assume that any particular stamp really is sound on the larger region. -/
theorem split_extra (compile first second : Nat) :
    min compile (first + second) ≤ min compile first + min compile second := by
  by_cases left : compile ≤ first
  · rw [min_eq_left left]
    exact (min_le_left _ _).trans (Nat.le_add_right _ _)
  · by_cases right : compile ≤ second
    · rw [min_eq_left right]
      exact (min_le_left _ _).trans (Nat.le_add_left _ _)
    · rw [min_eq_right (by omega : first ≤ compile), min_eq_right (by omega : second ≤ compile)]
      exact min_le_right _ _

/-- For two nonempty positive saving intervals, a needless invalidation
costs strictly once their combined savings could pay for compilation. -/
theorem split_costs_strictly_iff (compile first second : Nat)
    (c : 0 < compile) (f : 0 < first) (s : 0 < second) :
    min compile (first + second) < min compile first + min compile second ↔
      compile < first + second := by
  by_cases small : first + second ≤ compile
  · have left : first ≤ compile := by omega
    have right : second ≤ compile := by omega
    simp [min_eq_right small, min_eq_right left, min_eq_right right, not_lt.mpr small]
  · have below : compile < first + second := by omega
    rw [min_eq_left below.le]
    simp only [below, iff_true]
    by_cases fmin : compile ≤ first
    · rw [min_eq_left fmin]
      exact Nat.lt_add_of_pos_right (lt_min c s)
    · by_cases smin : compile ≤ second
      · rw [min_eq_left smin]
        exact Nat.lt_add_of_pos_left (lt_min c f)
      · rwa [min_eq_right (by omega : first ≤ compile), min_eq_right (by omega : second ≤ compile)]

def splitHistoryExtra (compile : Nat) (generations : List (List Nat)) : Nat :=
  (generations.map (offlineExtra compile)).sum

theorem splitting_reusable_history_cannot_help (compile : Nat) (generations : List (List Nat)) :
    offlineExtra compile generations.flatten ≤ splitHistoryExtra compile generations := by
  induction generations with
  | nil => simp [offlineExtra, splitHistoryExtra]
  | cons generation rest ih =>
      simp only [offlineExtra, splitHistoryExtra, List.flatten_cons, List.sum_append, List.map_cons, List.sum_cons]
      exact (split_extra compile generation.sum rest.flatten.sum).trans (Nat.add_le_add_left ih _)

namespace Controls

theorem lookahead_avoids_whale_call :
    lookahead 10 0 [3, 1000] = 13 ∧ retrospective 10 0 [3, 1000] = 1003 := by decide

theorem unrelated_bump_can_materially_cost :
    offlineExtra 60 [[40], [40]].flatten = 60 ∧ splitHistoryExtra 60 [[40], [40]] = 80 := by decide

end Controls
end Mettapedia.Machines.CallBoundaryReuse
