import Mathlib

/-!
# Entropy-form bounds for binomial coefficients

Exact natural-number forms of the standard Shannon-entropy bounds
`2^(n·H(k/n)) / (n+1) ≤ C(n,k) ≤ 2^(n·H(k/n))`, written without real
logarithms:

* `choose_mul_pow_pow_le` : `C(n,k) · kᵏ · (n-k)ⁿ⁻ᵏ ≤ nⁿ`
  (one term of the binomial expansion of `(k + (n-k))ⁿ` is at most the sum);
* `pow_le_succ_mul_choose_mul` : `nⁿ ≤ (n+1) · C(n,k) · kᵏ · (n-k)ⁿ⁻ᵏ`
  (the `j = k` term is the largest of the `n+1` terms).

These are the workhorse estimates for large-deviation counting bounds on
binomial slices, e.g. bounding `C(w, q) · C(n-w, k-q)` against `C(n, k)`.
-/

namespace Mettapedia.InformationTheory

open Finset

/-- The `j`-th term of the binomial expansion of `(k + (n-k))^n`. -/
def tiltTerm (n k j : ℕ) : ℕ :=
  k ^ j * (n - k) ^ (n - j) * n.choose j

theorem tiltTerm_def (n k j : ℕ) :
    tiltTerm n k j = k ^ j * (n - k) ^ (n - j) * n.choose j := rfl

theorem sum_tiltTerm (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), tiltTerm n k j = n ^ n := by
  have hsplit : k + (n - k) = n := Nat.add_sub_cancel' hk
  calc ∑ j ∈ range (n + 1), tiltTerm n k j
      = (k + (n - k)) ^ n := (add_pow k (n - k) n).symm
    _ = n ^ n := by rw [hsplit]

/-- Upper entropy bound: `C(n,k) · kᵏ · (n-k)ⁿ⁻ᵏ ≤ nⁿ`. -/
theorem choose_mul_pow_pow_le {n k : ℕ} (hk : k ≤ n) :
    n.choose k * (k ^ k * (n - k) ^ (n - k)) ≤ n ^ n := by
  have hmem : k ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hk)
  have hsingle :
      tiltTerm n k k ≤ ∑ j ∈ range (n + 1), tiltTerm n k j :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
  calc n.choose k * (k ^ k * (n - k) ^ (n - k))
      = tiltTerm n k k := by rw [tiltTerm_def]; ring
    _ ≤ ∑ j ∈ range (n + 1), tiltTerm n k j := hsingle
    _ = n ^ n := sum_tiltTerm n k hk

/-- Ascending step: for `j < k ≤ n` the expansion terms increase. -/
theorem tiltTerm_le_succ {n k j : ℕ} (hjk : j + 1 ≤ k) (hk : k ≤ n) :
    tiltTerm n k j ≤ tiltTerm n k (j + 1) := by
  have hjn : j + 1 ≤ n := le_trans hjk hk
  have hexp : n - j = (n - (j + 1)) + 1 := by omega
  -- key scalar inequality: (n-k)·(j+1) ≤ k·(n-j)
  have hscalar : (n - k) * (j + 1) ≤ k * (n - j) := by
    have h1 : (n - k) * (j + 1) ≤ (n - k) * k :=
      Nat.mul_le_mul_left _ hjk
    have h2 : (n - k) * k ≤ (n - j) * k := by
      have : n - k ≤ n - j := by omega
      exact Nat.mul_le_mul_right _ this
    calc (n - k) * (j + 1) ≤ (n - k) * k := h1
      _ ≤ (n - j) * k := h2
      _ = k * (n - j) := Nat.mul_comm _ _
  -- choose recurrence: C(n, j+1)·(j+1) = C(n, j)·(n - j)
  have hchoose : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) :=
    Nat.choose_succ_right_eq n j
  -- compare after multiplying both sides by (j+1) > 0
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos j)
  calc tiltTerm n k j * (j + 1)
      = k ^ j * ((n - k) ^ (n - (j + 1)) * (n - k)) * (n.choose j * (j + 1)) := by
        rw [tiltTerm_def, hexp]; ring
    _ = (k ^ j * (n - k) ^ (n - (j + 1)) * n.choose j) * ((n - k) * (j + 1)) := by
        ring
    _ ≤ (k ^ j * (n - k) ^ (n - (j + 1)) * n.choose j) * (k * (n - j)) :=
        Nat.mul_le_mul_left _ hscalar
    _ = k ^ (j + 1) * (n - k) ^ (n - (j + 1)) * (n.choose j * (n - j)) := by
        ring
    _ = k ^ (j + 1) * (n - k) ^ (n - (j + 1)) * (n.choose (j + 1) * (j + 1)) := by
        rw [hchoose]
    _ = tiltTerm n k (j + 1) * (j + 1) := by
        rw [tiltTerm_def]; ring

/-- Descending step: for `k ≤ j < n` the expansion terms decrease. -/
theorem tiltTerm_succ_le {n k j : ℕ} (hkj : k ≤ j) (hjn : j + 1 ≤ n) :
    tiltTerm n k (j + 1) ≤ tiltTerm n k j := by
  have hexp : n - j = (n - (j + 1)) + 1 := by omega
  -- key scalar inequality: k·(n-j) ≤ (n-k)·(j+1)
  have hscalar : k * (n - j) ≤ (n - k) * (j + 1) := by
    have h1 : k * (n - j) ≤ k * (n - k) := by
      have : n - j ≤ n - k := by omega
      exact Nat.mul_le_mul_left _ this
    have h2 : k * (n - k) ≤ (j + 1) * (n - k) := by
      have : k ≤ j + 1 := le_trans hkj (Nat.le_succ j)
      exact Nat.mul_le_mul_right _ this
    calc k * (n - j) ≤ k * (n - k) := h1
      _ ≤ (j + 1) * (n - k) := h2
      _ = (n - k) * (j + 1) := Nat.mul_comm _ _
  have hchoose : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) :=
    Nat.choose_succ_right_eq n j
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos j)
  calc tiltTerm n k (j + 1) * (j + 1)
      = k ^ (j + 1) * (n - k) ^ (n - (j + 1)) * (n.choose (j + 1) * (j + 1)) := by
        rw [tiltTerm_def]; ring
    _ = k ^ (j + 1) * (n - k) ^ (n - (j + 1)) * (n.choose j * (n - j)) := by
        rw [hchoose]
    _ = (k ^ j * (n - k) ^ (n - (j + 1)) * n.choose j) * (k * (n - j)) := by
        ring
    _ ≤ (k ^ j * (n - k) ^ (n - (j + 1)) * n.choose j) * ((n - k) * (j + 1)) :=
        Nat.mul_le_mul_left _ hscalar
    _ = k ^ j * ((n - k) ^ (n - (j + 1)) * (n - k)) * (n.choose j * (j + 1)) := by
        ring
    _ = tiltTerm n k j * (j + 1) := by
        rw [tiltTerm_def, hexp]; ring

/-- Every expansion term is at most the `j = k` term. -/
theorem tiltTerm_le_self {n k : ℕ} (hk : k ≤ n) :
    ∀ j, j ≤ n → tiltTerm n k j ≤ tiltTerm n k k := by
  -- ascending side, by downward induction on the distance to k
  have up : ∀ d j, j + d = k → tiltTerm n k j ≤ tiltTerm n k k := by
    intro d
    induction d with
    | zero => intro j hj; rw [Nat.add_zero] at hj; rw [hj]
    | succ d ih =>
        intro j hj
        have hstep : tiltTerm n k j ≤ tiltTerm n k (j + 1) :=
          tiltTerm_le_succ (by omega) hk
        exact le_trans hstep (ih (j + 1) (by omega))
  -- descending side
  have down : ∀ d j, k + d = j → j ≤ n → tiltTerm n k j ≤ tiltTerm n k k := by
    intro d
    induction d with
    | zero => intro j hj _; rw [Nat.add_zero] at hj; rw [← hj]
    | succ d ih =>
        intro j hj hjn
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨k + d, by omega⟩
        have hstep : tiltTerm n k (j' + 1) ≤ tiltTerm n k j' :=
          tiltTerm_succ_le (by omega) hjn
        exact le_trans hstep (ih j' (by omega) (by omega))
  intro j hjn
  rcases Nat.le_total j k with hjk | hkj
  · exact up (k - j) j (by omega)
  · exact down (j - k) j (by omega) hjn

/-- One term of the Vandermonde convolution: `C(a,i)·C(b,j) ≤ C(a+b,i+j)`.
This is the "no saving" baseline for split-binomial counting bounds: a
product of two binomial slices never exceeds the joint binomial. The
entropy lemmas above quantify how much *smaller* an off-center term is. -/
theorem choose_mul_choose_le_choose_add (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  have hmem : ((i, j) : ℕ × ℕ) ∈ Finset.antidiagonal (i + j) :=
    Finset.mem_antidiagonal.mpr rfl
  exact Finset.single_le_sum
    (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun p _ => Nat.zero_le _) hmem

/-- Lower entropy bound (max-term):
`nⁿ ≤ (n+1) · C(n,k) · kᵏ · (n-k)ⁿ⁻ᵏ`. -/
theorem pow_le_succ_mul_choose_mul {n k : ℕ} (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * (k ^ k * (n - k) ^ (n - k))) := by
  have hbound :
      ∑ j ∈ range (n + 1), tiltTerm n k j ≤
        (range (n + 1)).card * tiltTerm n k k := by
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro j hj
    exact tiltTerm_le_self hk j (Nat.lt_succ_iff.mp (mem_range.mp hj))
  have hterm : tiltTerm n k k = n.choose k * (k ^ k * (n - k) ^ (n - k)) := by
    rw [tiltTerm_def]; ring
  calc n ^ n = ∑ j ∈ range (n + 1), tiltTerm n k j :=
        (sum_tiltTerm n k hk).symm
    _ ≤ (range (n + 1)).card * tiltTerm n k k := hbound
    _ = (n + 1) * (n.choose k * (k ^ k * (n - k) ^ (n - k))) := by
        rw [card_range, hterm]

end Mettapedia.InformationTheory
