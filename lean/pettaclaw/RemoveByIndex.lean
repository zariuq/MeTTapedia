/-!
# RemoveByIndex — when a removal may read an index instead of every row

A transaction workspace removes occurrences of a pattern from the rows it
overlays. The scan visits every visible row; with tens of thousands of rows
that is the cost of every removal. An index can name the candidate rows
instead. This file says when that changes only the cost:

* `removes_same_rows`: removing EVERY match through a complete index (every
  visible matching row is a candidate, and every candidate is a row) removes
  exactly the rows the scan removes. Order does not matter here.
* `indexed_eq_scan`: removing ONE occurrence through an index agrees with
  the scan when the index yields the least matching candidate, i.e. when it
  follows row order.
* `streams_differ`: the store's index does not follow row order. It yields
  the rows whose indexed field holds that exact value, then the rows that hold
  a variable there. Taking the first match in that order can take another
  occurrence than the scan, so a bounded removal keeps the scan.

The model abstracts a row's visibility and the comparison into one
predicate `wanted`; the runtime applies the same comparison in both paths.
-/

namespace RemoveByIndex

/-- The first `i` in `[k, n)` with `wanted i`, scanning upwards. -/
def firstFrom (wanted : Nat → Bool) (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k => if k < n then (if wanted k then some k else firstFrom wanted n fuel (k + 1)) else none

/-- The scan over rows `0 .. n-1`. -/
def scan (wanted : Nat → Bool) (n : Nat) : Option Nat := firstFrom wanted n n 0

/-- The least element of a list. -/
def least : List Nat → Option Nat
  | [] => none
  | x :: xs => match least xs with
    | none => some x
    | some y => some (min x y)

/-- The indexed removal: the least wanted candidate. -/
def indexed (wanted : Nat → Bool) (candidates : List Nat) : Option Nat :=
  least (candidates.filter wanted)

/-! ## What each one returns -/

theorem firstFrom_some (wanted : Nat → Bool) (n : Nat) :
    ∀ fuel k i, firstFrom wanted n fuel k = some i →
      k ≤ i ∧ i < n ∧ wanted i = true ∧ ∀ j, k ≤ j → j < i → wanted j = false := by
  intro fuel
  induction fuel with
  | zero => intro k i h; simp [firstFrom] at h
  | succ m ih =>
    intro k i h
    simp only [firstFrom] at h
    split at h
    · rename_i hk
      split at h
      · rename_i hw; cases h; exact ⟨Nat.le_refl _, hk, hw, fun j h1 h2 => by omega⟩
      · rename_i hw
        have ⟨h1, h2, h3, h4⟩ := ih (k + 1) i h
        refine ⟨by omega, h2, h3, fun j hj1 hj2 => ?_⟩
        by_cases e : j = k
        · subst e; simpa using hw
        · exact h4 j (by omega) hj2
    · simp at h

theorem firstFrom_none (wanted : Nat → Bool) (n : Nat) :
    ∀ fuel k, n ≤ fuel + k → firstFrom wanted n fuel k = none → ∀ j, k ≤ j → j < n → wanted j = false := by
  intro fuel
  induction fuel with
  | zero => intro k hk _ j h1 h2; omega
  | succ m ih =>
    intro k hk h j h1 h2
    simp only [firstFrom] at h
    split at h
    · split at h
      · simp at h
      · rename_i _ hw
        by_cases e : j = k
        · subst e; simpa using hw
        · exact ih (k + 1) (by omega) h j (by omega) h2
    · omega

theorem least_some (l : List Nat) : ∀ m, least l = some m → m ∈ l ∧ ∀ x ∈ l, m ≤ x := by
  induction l with
  | nil => intro m h; simp [least] at h
  | cons x xs ih =>
    intro m h
    simp only [least] at h
    split at h
    · rename_i hn; cases h
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys =>
          exfalso; simp only [least] at hn; split at hn <;> simp at hn
      subst this; exact ⟨List.mem_cons_self .., fun z hz => by simp at hz; omega⟩
    · rename_i y hy; cases h
      have ⟨hy1, hy2⟩ := ih y hy
      refine ⟨?_, fun z hz => ?_⟩
      · rcases Nat.le_total x y with hle | hle
        · rw [Nat.min_eq_left hle]; exact List.mem_cons_self ..
        · rw [Nat.min_eq_right hle]; exact List.mem_cons_of_mem _ hy1
      · cases hz with
        | head => exact Nat.min_le_left _ _
        | tail _ hz' => exact Nat.le_trans (Nat.min_le_right _ _) (hy2 z hz')

theorem least_none (l : List Nat) (h : least l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs => simp only [least] at h; split at h <;> simp at h

/-! ## The indexed removal takes the scan's row -/

theorem indexed_eq_scan (wanted : Nat → Bool) (n : Nat) (candidates : List Nat)
    (complete : ∀ i, i < n → wanted i = true → i ∈ candidates)
    (rows : ∀ c ∈ candidates, c < n) :
    indexed wanted candidates = scan wanted n := by
  unfold indexed scan
  cases hs : firstFrom wanted n n 0 with
  | some i =>
    have ⟨_, hi, hw, hbelow⟩ := firstFrom_some wanted n n 0 i hs
    have hmem : i ∈ candidates.filter wanted := List.mem_filter.mpr ⟨complete i hi hw, hw⟩
    cases hl : least (candidates.filter wanted) with
    | none => rw [least_none _ hl] at hmem; simp at hmem
    | some m =>
      have ⟨hm, hmin⟩ := least_some _ m hl
      have ⟨hmc, hmw⟩ := List.mem_filter.mp hm
      have hle : m ≤ i := hmin i hmem
      -- m is a wanted row, and no wanted row lies below i, so m = i.
      have : ¬ m < i := fun hlt => by
        have := hbelow m (Nat.zero_le _) hlt; rw [hmw] at this; simp at this
      exact congrArg some (by omega)
  | none =>
    have hnone := firstFrom_none wanted n n 0 (by omega) hs
    cases hl : least (candidates.filter wanted) with
    | none => rfl
    | some m =>
      have ⟨hm, _⟩ := least_some _ m hl
      have ⟨hmc, hmw⟩ := List.mem_filter.mp hm
      have := hnone m (Nat.zero_le _) (rows m hmc); rw [hmw] at this; simp at this

/-! ## Removing every match -/

/-- The rows a scan of `0 .. n-1` removes when it removes every match. -/
def scanAll (wanted : Nat → Bool) (n : Nat) : List Nat := (List.range n).filter wanted

/-- The rows an index's candidates give when every match is removed. -/
def indexedAll (wanted : Nat → Bool) (candidates : List Nat) : List Nat := candidates.filter wanted

theorem removes_same_rows (wanted : Nat → Bool) (n : Nat) (candidates : List Nat)
    (complete : ∀ i, i < n → wanted i = true → i ∈ candidates)
    (rows : ∀ c ∈ candidates, c < n) (i : Nat) :
    i ∈ indexedAll wanted candidates ↔ i ∈ scanAll wanted n := by
  unfold indexedAll scanAll
  constructor
  · intro h
    have ⟨hc, hw⟩ := List.mem_filter.mp h
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (rows i hc), hw⟩
  · intro h
    have ⟨hr, hw⟩ := List.mem_filter.mp h
    exact List.mem_filter.mpr ⟨complete i (List.mem_range.mp hr) hw, hw⟩

/-! ## One occurrence through the store's streams -/

/-- The first wanted row in the order the store's index yields its candidates: the rows whose
field is exact (`exact`), then the others, each stream in row order. -/
def streamFirst (wanted exact : Nat → Bool) (n : Nat) : Option Nat :=
  ((List.range n).filter (fun i => exact i) ++ (List.range n).filter (fun i => !exact i)).find? wanted

/-- Row 0 holds a variable at the indexed field, row 1 the exact value; both match. The scan takes
row 0; the streams take row 1. -/
theorem streams_differ :
    streamFirst (fun _ => true) (fun i => i == 1) 2 ≠ scan (fun _ => true) 2 := by decide

/-- Without completeness the two can differ: an index that omits the first
matching row removes a later occurrence, which is why the runtime falls back
to the scan whenever the index cannot vouch for completeness. -/
theorem incomplete_index_differs :
    indexed (fun i => i == 1 || i == 3) [3] ≠ scan (fun i => i == 1 || i == 3) 4 := by decide

end RemoveByIndex

#print axioms RemoveByIndex.indexed_eq_scan
#print axioms RemoveByIndex.incomplete_index_differs
#print axioms RemoveByIndex.removes_same_rows
#print axioms RemoveByIndex.streams_differ
