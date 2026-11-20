import Mettapedia.Logic.Arithmetic.FourierMotzkin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Real.Basic

/-!
# Bounded projection of rational halfspaces

Each elimination keeps the rows independent of its pivot and generates
at most the requested number of lower/upper pairs. These consequences
give an outer projection at every budget. Deduplication preserves their
conjunction. Sufficient work recovers the full projection.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.FourierMotzkin.Budget

def allPairs {n : Nat} (low high : List (Bound n)) : List (Atom n) :=
  low.flatMap fun lo => high.map (cross lo)

def takePairs {n : Nat} (high : List (Bound n)) : List (Bound n) → Nat → List (Atom n)
  | [], _ => []
  | lo :: rest, fuel =>
    if fuel = 0 then []
    else (high.take fuel).map (cross lo) ++ takePairs high rest (fuel - high.length)

theorem takePairs_subset {n : Nat} (low high : List (Bound n)) (fuel : Nat) :
    takePairs high low fuel ⊆ allPairs low high := by
  induction low generalizing fuel with
  | nil => simp [takePairs]
  | cons lo rest ih =>
    intro row h
    simp only [takePairs] at h
    split at h
    · contradiction
    · simp only [allPairs, List.flatMap_cons, List.mem_append]
      rcases List.mem_append.mp h with left | right
      · obtain ⟨hi, member, rfl⟩ := List.mem_map.mp left
        exact Or.inl (List.mem_map.mpr ⟨hi, List.mem_of_mem_take member, rfl⟩)
      · exact Or.inr (ih _ right)

theorem takePairs_length {n : Nat} (low high : List (Bound n)) (fuel : Nat) :
    (takePairs high low fuel).length ≤ fuel := by
  induction low generalizing fuel with
  | nil => simp [takePairs]
  | cons lo rest ih =>
    simp only [takePairs]
    split
    · simp
    · simp only [List.length_append, List.length_map, List.length_take]
      have used := ih (fuel - high.length)
      omega

theorem takePairs_complete {n : Nat} (low high : List (Bound n)) (fuel : Nat)
    (enough : low.length * high.length ≤ fuel) :
    takePairs high low fuel = allPairs low high := by
  induction low generalizing fuel with
  | nil => rfl
  | cons lo rest ih =>
    have size : rest.length * high.length + high.length ≤ fuel := by
      simpa only [List.length_cons, Nat.add_mul, one_mul] using enough
    by_cases zero : fuel = 0
    · have noUpper : high = [] := List.length_eq_zero_iff.mp (by omega)
      subst high
      simp [takePairs, zero, allPairs]
    · rw [takePairs, if_neg zero, List.take_of_length_le (by omega)]
      rw [ih _ (by omega)]
      rfl

private def equalityBound {n : Nat} (low high : List (Bound n)) : Option (Bound n) :=
  low.find? fun b => !b.strict && decide (b ∈ high)

private theorem equalityBound_sound {n : Nat} {low high : List (Bound n)} {b : Bound n}
    (found : equalityBound low high = some b) : b ∈ low ∧ b ∈ high ∧ b.strict = false := by
  have test := List.find?_some found
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at test
  exact ⟨List.mem_of_find?_eq_some found, test.2, test.1⟩

/-- When a pivot has matching closed lower and upper bounds, substituting
that equality requires only linearly many pairs. -/
private def plannedPairs {n : Nat} (low high : List (Bound n)) : List (Atom n) :=
  match equalityBound low high with
  | none => allPairs low high
  | some b => low.map (fun lo => cross lo b) ++ high.map (cross b)

private def plannedCount {n : Nat} (low high : List (Bound n)) : Nat :=
  match equalityBound low high with
  | none => low.length * high.length
  | some _ => low.length + high.length

private def takePlanned {n : Nat} (fuel : Nat) (low high : List (Bound n)) : List (Atom n) :=
  match equalityBound low high with
  | none => takePairs high low fuel
  | some b => (low.take fuel).map (fun lo => cross lo b) ++
      (high.take (fuel - low.length)).map (cross b)

private theorem takePlanned_subset {n : Nat} (fuel : Nat) (low high : List (Bound n)) :
    takePlanned fuel low high ⊆ plannedPairs low high := by
  cases h : equalityBound low high with
  | none => simpa only [takePlanned, plannedPairs, h] using takePairs_subset low high fuel
  | some b =>
    intro a member
    simp only [takePlanned, plannedPairs, h, List.mem_append] at member ⊢
    rcases member with head | tail
    · obtain ⟨l, present, rfl⟩ := List.mem_map.mp head
      exact Or.inl (List.mem_map.mpr ⟨l, List.mem_of_mem_take present, rfl⟩)
    · obtain ⟨u, present, rfl⟩ := List.mem_map.mp tail
      exact Or.inr (List.mem_map.mpr ⟨u, List.mem_of_mem_take present, rfl⟩)

private theorem takePlanned_length {n : Nat} (fuel : Nat) (low high : List (Bound n)) :
    (takePlanned fuel low high).length ≤ fuel := by
  cases h : equalityBound low high with
  | none => simpa only [takePlanned, h] using takePairs_length low high fuel
  | some b =>
    simp only [takePlanned, h, List.length_append, List.length_map, List.length_take]
    omega

private theorem takePlanned_complete {n : Nat} (fuel : Nat) (low high : List (Bound n))
    (enough : plannedCount low high ≤ fuel) : takePlanned fuel low high = plannedPairs low high := by
  cases h : equalityBound low high with
  | none =>
    simp only [plannedCount, h] at enough
    simpa only [takePlanned, plannedPairs, h] using takePairs_complete low high fuel enough
  | some b =>
    simp only [plannedCount, h] at enough
    simp only [takePlanned, plannedPairs, h,
      List.take_of_length_le (show low.length ≤ fuel by omega),
      List.take_of_length_le (show high.length ≤ fuel - low.length by omega)]

private theorem plannedPairs_subset {n : Nat} (low high : List (Bound n)) :
    plannedPairs low high ⊆ allPairs low high := by
  cases h : equalityBound low high with
  | none => simp [plannedPairs, h]
  | some b =>
    obtain ⟨bl, bh, _⟩ := equalityBound_sound h
    intro a member
    simp only [plannedPairs, h, List.mem_append] at member
    rcases member with lower | upper
    · obtain ⟨l, present, rfl⟩ := List.mem_map.mp lower
      exact List.mem_flatMap.mpr ⟨l, present, List.mem_map.mpr ⟨b, bh, rfl⟩⟩
    · obtain ⟨u, present, rfl⟩ := List.mem_map.mp upper
      exact List.mem_flatMap.mpr ⟨b, bl, List.mem_map.mpr ⟨u, present, rfl⟩⟩

def pairCount {n : Nat} (rows : List (Atom (n + 1))) : Nat :=
  plannedCount (lowers rows) (uppers rows)

private def leading {n : Nat} : Coeff n → ℚ
  | .nil => 0
  | .cons c rest => if c = 0 then leading rest else c

private def normalScale {n : Nat} (row : Atom n) : ℚ :=
  let c := leading row.term.coeff
  if c = 0 then 1 else |c|⁻¹

private theorem normalScale_pos {n : Nat} (row : Atom n) : 0 < normalScale row := by
  unfold normalScale
  dsimp only
  split
  · exact zero_lt_one
  · exact inv_pos.mpr (abs_pos.mpr (by assumption))

/-- Canonicalize positive scalar multiples to keep repeated rows small. -/
def normalize {n : Nat} (row : Atom n) : Atom n :=
  { row with term := row.term.scale (normalScale row) }

@[simp] theorem normalize_rel {n : Nat} (row : Atom n) : (normalize row).rel = row.rel := rfl

theorem normalize_sat {n : Nat} (row : Atom n) (e : Fin n → ℝ) :
    (normalize row).sat e ↔ row.sat e := by
  have scale : 0 < (normalScale row : ℝ) := Rat.cast_pos.mpr (normalScale_pos row)
  simp only [normalize, Atom.sat, eval_scale]
  cases row.rel <;> simp only [holds]
  · rw [← mul_zero (normalScale row : ℝ), mul_le_mul_iff_right₀ scale, mul_zero]
  · rw [← mul_zero (normalScale row : ℝ), mul_lt_mul_iff_right₀ scale, mul_zero]

def simplify {n : Nat} (rows : List (Atom n)) : List (Atom n) :=
  (rows.map normalize).dedup

theorem simplify_sat {n : Nat} (rows : List (Atom n)) (e : Fin n → ℝ) :
    allSat (simplify rows) e ↔ allSat rows e := by
  simp only [allSat, simplify, List.mem_dedup, List.forall_mem_map, normalize_sat]

def step {n : Nat} (fuel : Nat) (rows : List (Atom (n + 1))) : List (Atom n) :=
  simplify (residuals rows ++ takePlanned fuel (lowers rows) (uppers rows))

def fullStep {n : Nat} (rows : List (Atom (n + 1))) : List (Atom n) :=
  simplify (residuals rows ++ plannedPairs (lowers rows) (uppers rows))

theorem step_length {n : Nat} (fuel : Nat) (rows : List (Atom (n + 1))) :
    (step fuel rows).length ≤ (residuals rows).length + fuel := by
  unfold step simplify
  apply (List.dedup_sublist _).length_le.trans
  simp only [List.length_map, List.length_append]
  exact Nat.add_le_add_left (takePlanned_length fuel (lowers rows) (uppers rows)) _

theorem step_eq_full {n : Nat} (fuel : Nat) (rows : List (Atom (n + 1)))
    (enough : pairCount rows ≤ fuel) : step fuel rows = fullStep rows := by
  simp only [step, fullStep, takePlanned_complete _ _ _ enough]

theorem step_subset {n : Nat} (fuel : Nat) (rows : List (Atom (n + 1))) :
    step fuel rows ⊆ fullStep rows := by
  intro row h
  rw [step, simplify, List.mem_dedup] at h
  rw [fullStep, simplify, List.mem_dedup]
  obtain ⟨a, found, rfl⟩ := List.mem_map.mp h
  have included := (List.mem_append.mp found).imp id (fun inside => takePlanned_subset _ _ _ inside)
  exact List.mem_map.mpr ⟨a, List.mem_append.mpr included, rfl⟩

theorem fullStep_member {n : Nat} (rows : List (Atom (n + 1))) (a : Atom n)
    (member : a ∈ fullStep rows) :
    ∃ original ∈ residuals rows ++ allPairs (lowers rows) (uppers rows), normalize original = a := by
  simp only [fullStep, simplify, List.mem_dedup] at member
  obtain ⟨r, found, rfl⟩ := List.mem_map.mp member
  have included := (List.mem_append.mp found).imp id (fun pair => plannedPairs_subset _ _ pair)
  exact ⟨r, List.mem_append.mpr included, rfl⟩

theorem fullStep_iff {n : Nat} (rows : List (Atom (n + 1))) (e : Fin n → ℝ) :
    allSat (fullStep rows) e ↔ ∃ x, allSat rows (envCons x e) := by
  constructor
  · intro accepted
    rw [fullStep, simplify_sat, allSat_append] at accepted
    apply (exists_iff_pieces rows e).mpr
    refine ⟨accepted.1, ?_⟩
    intro lo hlo hi hhi
    cases h : equalityBound (lowers rows) (uppers rows) with
    | none =>
      exact accepted.2 _ (by
        rw [plannedPairs, h]
        exact List.mem_flatMap.mpr ⟨lo, hlo, List.mem_map.mpr ⟨hi, hhi, rfl⟩⟩)
    | some b =>
      have low := accepted.2 (cross lo b) (by
        rw [plannedPairs, h]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨lo, hlo, rfl⟩))
      have high := accepted.2 (cross b hi) (by
        rw [plannedPairs, h]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨hi, hhi, rfl⟩))
      have closed := (equalityBound_sound h).2.2
      rw [cross_iff_pairLe] at low high ⊢
      cases l : lo.strict <;> cases u : hi.strict <;>
        simp only [pairLe, ev, l, u, closed, Bool.or_self,
          Bool.or_false, Bool.or_true, Bool.false_eq_true, if_false, if_true] at low high ⊢ <;>
        linarith
  · intro witness
    obtain ⟨base, pairs⟩ := (exists_iff_pieces rows e).mp witness
    rw [fullStep, simplify_sat, allSat_append]
    refine ⟨base, fun a member => ?_⟩
    obtain ⟨lo, hlo, found⟩ := List.mem_flatMap.mp (plannedPairs_subset _ _ member)
    obtain ⟨hi, hhi, rfl⟩ := List.mem_map.mp found
    exact pairs lo hlo hi hhi

theorem step_sound {n : Nat} (fuel : Nat) (rows : List (Atom (n + 1)))
    (e : Fin n → ℝ) (model : ∃ x, allSat rows (envCons x e)) :
    allSat (step fuel rows) e := fun row member =>
  ((fullStep_iff rows e).mpr model) row (step_subset fuel rows member)

def limited (fuel : Nat) : (n : Nat) → List (Atom (n + 1)) → List (Atom 1)
  | 0, rows => rows
  | n + 1, rows => limited fuel n (step fuel rows)

def complete : (n : Nat) → List (Atom (n + 1)) → List (Atom 1)
  | 0, rows => rows
  | n + 1, rows => complete n (fullStep rows)

theorem complete_iff (n : Nat) (rows : List (Atom (n + 1))) (v : ℝ) :
    allSat (complete n rows) (fun _ => v) ↔
      ∃ e, allSat rows e ∧ e (Fin.last n) = v := by
  induction n with
  | zero =>
    constructor
    · intro accepted
      exact ⟨fun _ => v, accepted, rfl⟩
    · rintro ⟨e, holds, equal⟩
      have same : e = fun _ => v := by
        funext i
        have last : i = Fin.last 0 := by apply Fin.ext; omega
        exact last ▸ equal
      exact same ▸ holds
  | succ n ih =>
    rw [complete, ih]
    constructor
    · rintro ⟨e, held, same⟩
      obtain ⟨x, hx⟩ := (fullStep_iff rows e).mp held
      exact ⟨envCons x e, hx, same⟩
    · rintro ⟨e, held, same⟩
      have whole : envCons (e 0) (envTail e) = e := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      exact ⟨envTail e, (fullStep_iff rows _).mpr ⟨e 0, whole.symm ▸ held⟩, same⟩

theorem partial_sound (fuel n : Nat) (rows : List (Atom (n + 1)))
    (e : Fin (n + 1) → ℝ) (held : allSat rows e) :
    allSat (limited fuel n rows) (fun _ => e (Fin.last n)) := by
  induction n with
  | zero =>
    have same : (fun _ : Fin 1 => e (Fin.last 0)) = e := by
      funext i
      rw [show i = Fin.last 0 by apply Fin.ext; omega]
    simpa only [limited, same] using held
  | succ n ih =>
    have whole : envCons (e 0) (envTail e) = e := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    exact ih (step fuel rows) (envTail e) (step_sound fuel rows _ ⟨e 0, whole.symm ▸ held⟩)

theorem eventually_complete (n : Nat) (rows : List (Atom (n + 1))) :
    ∃ enough, ∀ fuel ≥ enough, limited fuel n rows = complete n rows := by
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨budget, stable⟩ := ih (fullStep rows)
    refine ⟨max budget (pairCount rows), fun fuel above => ?_⟩
    rw [limited, step_eq_full fuel rows ((le_max_right _ _).trans above), complete]
    exact stable fuel ((le_max_left _ _).trans above)

/-- The flag records that every elimination kept all of its pairs. -/
def run (fuel : Nat) : (n : Nat) → List (Atom (n + 1)) → List (Atom 1) × Bool
  | 0, rows => (rows, true)
  | n + 1, rows =>
    let rest := run fuel n (step fuel rows)
    (rest.1, decide (pairCount rows ≤ fuel) && rest.2)

theorem run_rows (fuel n : Nat) (rows : List (Atom (n + 1))) :
    (run fuel n rows).1 = limited fuel n rows := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (step fuel rows)

theorem run_completed (fuel n : Nat) (rows : List (Atom (n + 1)))
    (done : (run fuel n rows).2 = true) : (run fuel n rows).1 = complete n rows := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, Bool.and_eq_true, decide_eq_true_eq] at done
    simp only [run, complete]
    rw [ih _ done.2, step_eq_full fuel rows done.1]

end Mettapedia.Logic.Arithmetic.FourierMotzkin.Budget
