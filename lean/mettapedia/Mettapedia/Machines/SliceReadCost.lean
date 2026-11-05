import Mathlib.Tactic

/-!
# Reading a document in slices: the peak is a slice plus what is kept

A document of facts is parsed into the term universe before it runs.  Read
whole, every record of every form is alive at once, though a relation keeps
only part of each fact (its holes) once the form has run: deep facts ten
levels deep peaked at 5.9 times MORK's memory.  Read in slices, with a
collection between slices, the records a slice's forms leave as garbage go
before the next slice is parsed, so the peak is one slice's records plus
what the relation keeps from the slices before.

The model: `m` slices of `k` forms, each form making `r` records of which the
relation keeps `h`; read whole, the peak holds all `m * k * r` records
(`wholePeak`).  This file proves:
* `sliced_peak_le`: read in slices, it holds at most `m * k * h + k * r`;
* `sliced_peak_lt`: with fewer kept than made (`h < r`) and more slices than
  `r` (so that the slice itself is small against the garbage saved), the
  sliced peak is below the whole one, by at least `m * k * (r - h) - k * r`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SliceReadCost

/-- Records alive while slice `j` is read: what the relation keeps from the
`j` slices before, and the slice's own records. -/
def sliceLive (k r h j : ℕ) : ℕ := j * k * h + k * r

/-- The peak over `m` slices. -/
def slicedPeak (m k r h : ℕ) : ℕ :=
  ((List.range m).map (sliceLive k r h)).foldr max 0

/-- Read whole, every form's records are alive when the last form is read. -/
def wholePeak (m k r : ℕ) : ℕ := m * k * r

theorem foldr_max_le (l : List ℕ) (b : ℕ) (h : ∀ x ∈ l, x ≤ b) :
    l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldr_cons]
    exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem sliced_peak_le (m k r h : ℕ) :
    slicedPeak m k r h ≤ m * k * h + k * r := by
  unfold slicedPeak
  apply foldr_max_le
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  unfold sliceLive
  have : j * k * h ≤ m * k * h := by
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_right k (by omega)
  omega

theorem sliced_peak_lt (m k r h : ℕ) (hk : 1 ≤ k) (hhr : h < r) (hm : r < m) :
    slicedPeak m k r h + (m * k * (r - h) - k * r) ≤ wholePeak m k r ∧
      slicedPeak m k r h < wholePeak m k r := by
  have hle := sliced_peak_le m k r h
  have hgap : k * r < m * k * (r - h) := by
    have h1 : r < m * (r - h) := by
      have : 1 ≤ r - h := by omega
      nlinarith
    have : k * r < k * (m * (r - h)) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
    nlinarith
  have hsplit : m * k * r = m * k * h + m * k * (r - h) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  unfold wholePeak
  constructor <;> omega

end Mettapedia.Machines.SliceReadCost
