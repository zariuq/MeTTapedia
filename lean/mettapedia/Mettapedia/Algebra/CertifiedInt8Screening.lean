import Mettapedia.Algebra.SupportTensorScreening
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Certified 8-bit screening for exact top-k inner-product retrieval

Every stored row `x` keeps an 8-bit copy `x̃ = σ • c` (one scale `σ` per row, integer codes
`|c j| ≤ 127`), and the query `q` gets one, `q̃ = τ • d`. A screen computes the integer dot
product `D = ∑ c j * d j` exactly: an `Int32` accumulator cannot overflow while
`n ≤ 2 ^ 17` (`codeDot_partial_lt_int32`). One scaled value `σ τ D` then approximates the
score, and Cauchy–Schwarz bounds the distance to the exact one:

  `|⟪x, q⟫ - ⟪x̃, q̃⟫| ≤ ‖x - x̃‖ ‖q‖ + ‖x̃‖ ‖q - q̃‖`   (`quantized_score_error`).

Every row whose upper bound reaches the `k`-th largest lower bound is rescored with the
reference scores. By `SupportTensorScreening.stable_masked_screened_rerank_exact`, the stable
top-`k` is then exactly that of a full scan, boundary ties included
(`int8_screen_rerank_exact`). No shortlist length is a parameter: the certificate alone
decides which rows are read in full. The reference scores may themselves be rounded; their
error enters the radius (`int8_bounds_contain`), so "exact" means equal to the reference scan.

## Relation to the state of the art

* **FEXIPRO** (H. Li, T. N. Chan, M. L. Yiu, N. Mamoulis, *FEXIPRO: Fast and Exact Inner
  Product Retrieval in Recommender Systems*, SIGMOD 2017, pp. 835–850,
  doi:10.1145/3035918.3064009). Exact top-`k` inner products by sequential scan, pruning with
  upper bounds computed from integer-approximated vectors. The bound here is of that kind,
  two-sided, with the query's quantization and the final rounding included.
* **Quantized copies with rescoring**, as in Qdrant's scalar and binary quantization and in
  Faiss (J. Johnson, M. Douze, H. Jégou, *Billion-scale similarity search with GPUs*, IEEE
  Transactions on Big Data, 2021; M. Douze et al., *The Faiss library*, 2024). Compressed
  copies are scored first and the originals are reread for an oversampled shortlist of fixed
  length. Here the shortlist is whatever the certificate admits, so no answer is lost.
* **Learned compression with reranking**: product quantization (H. Jégou, M. Douze, C.
  Schmid, *Product Quantization for Nearest Neighbor Search*, IEEE TPAMI 33(1), 2011) and
  anisotropic quantization (R. Guo et al., *Accelerating Large-Scale Inference with
  Anisotropic Vector Quantization*, ICML 2020). Neither carries an error certificate.
* **RaBitQ** (J. Gao, C. Long, *RaBitQ: Quantizing High-Dimensional Vectors with a
  Theoretical Error Bound for Approximate Nearest Neighbor Search*, Proc. ACM Manag. Data
  2(3), SIGMOD 2024). One-bit codes whose estimator has a probabilistic error bound, used to
  choose what to rerank. The bound here is deterministic.
* **Graph routing over compressed vectors**: DiskANN (S. J. Subramanya, Devvrit, R. Kadekodi,
  R. Krishnaswamy, H. V. Simhadri, *DiskANN: Fast Accurate Billion-point Nearest Neighbor
  Search on a Single Node*, NeurIPS 2019) and HNSW (Y. A. Malkov, D. A. Yashunin, IEEE TPAMI
  42(4), 2020). They read few vectors but are approximate.
* **Pruning while reading dimensions**: ADSampling (J. Gao, C. Long, SIGMOD 2023,
  doi:10.1145/3589282) and PDX with PDX-BOND (L. Kuffo, E. Krippner, P. Boncz, *PDX: A Data
  Layout for Vector Similarity Search*, Proc. ACM Manag. Data 3(3), Article 196, SIGMOD
  2025). PDX-BOND is exact. A dimension-blocked layout and this certificate compose.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.CertifiedInt8Screening

open scoped BigOperators
open Mettapedia.Algebra.SupportTensorScreening

variable {n : Nat}

/-- The inner product of two coordinate vectors. -/
def dot (x y : Fin n → ℝ) : ℝ := ∑ j, x j * y j

/-- The Euclidean norm of a coordinate vector. -/
noncomputable def norm2 (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, x j ^ 2)

theorem norm2_nonneg (x : Fin n → ℝ) : 0 ≤ norm2 x := Real.sqrt_nonneg _

/-- Cauchy–Schwarz for coordinate vectors. -/
theorem abs_dot_le (x y : Fin n → ℝ) : |dot x y| ≤ norm2 x * norm2 y := by
  have square := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have bound : |dot x y| ≤ Real.sqrt ((∑ j, x j ^ 2) * ∑ j, y j ^ 2) :=
    Real.abs_le_sqrt square
  rw [Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg (x j))] at bound
  exact bound

theorem dot_sub_left (x x' y : Fin n → ℝ) : dot x y - dot x' y = dot (x - x') y := by
  simp only [dot, Pi.sub_apply, ← Finset.sum_sub_distrib, sub_mul]

theorem dot_sub_right (x y y' : Fin n → ℝ) : dot x y - dot x y' = dot x (y - y') := by
  simp only [dot, Pi.sub_apply, ← Finset.sum_sub_distrib, mul_sub]

/-- Quantizing both the row and the query moves the score by at most the two error norms,
each weighed by the other side. -/
theorem quantized_score_error (x q x' q' : Fin n → ℝ) :
    |dot x q - dot x' q'| ≤ norm2 (x - x') * norm2 q + norm2 x' * norm2 (q - q') := by
  have split : dot x q - dot x' q' = dot (x - x') q + dot x' (q - q') := by
    rw [← dot_sub_left, ← dot_sub_right]; ring
  rw [split]
  calc |dot (x - x') q + dot x' (q - q')|
      ≤ |dot (x - x') q| + |dot x' (q - q')| := abs_add_le _ _
    _ ≤ _ := add_le_add (abs_dot_le _ _) (abs_dot_le _ _)

/-- An 8-bit copy: one nonnegative scale and integer codes in `[-127, 127]`. -/
structure Int8Copy (n : Nat) where
  scale : ℝ
  code : Fin n → ℤ
  scale_nonneg : 0 ≤ scale
  code_bound : ∀ j, |code j| ≤ 127

/-- The real vector an 8-bit copy stands for. -/
def Int8Copy.value (c : Int8Copy n) : Fin n → ℝ := fun j => c.scale * (c.code j : ℝ)

/-- The integer dot product of two code vectors over a set of coordinates. -/
def codeDot (s : Finset (Fin n)) (a b : Fin n → ℤ) : ℤ := ∑ j ∈ s, a j * b j

/-- The dot product of two 8-bit copies is their scales times one integer. -/
theorem value_dot (a b : Int8Copy n) :
    dot a.value b.value = a.scale * b.scale * (codeDot Finset.univ a.code b.code : ℝ) := by
  simp only [dot, Int8Copy.value, codeDot, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every partial integer sum, in any accumulation order, stays inside `Int32` while
`n ≤ 2 ^ 17`: each product is at most `127 ^ 2` in magnitude. -/
theorem codeDot_partial_lt_int32 (a b : Int8Copy n) (small : n ≤ 2 ^ 17)
    (s : Finset (Fin n)) : |codeDot s a.code b.code| < 2 ^ 31 := by
  have term : ∀ j ∈ s, |a.code j * b.code j| ≤ 127 * 127 := fun j _ => by
    rw [abs_mul]
    exact mul_le_mul (a.code_bound j) (b.code_bound j) (abs_nonneg _) (by norm_num)
  have total : |codeDot s a.code b.code| ≤ (s.card : ℤ) * (127 * 127) := by
    calc |codeDot s a.code b.code| ≤ ∑ j ∈ s, |a.code j * b.code j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ s, (127 * 127 : ℤ) := Finset.sum_le_sum term
      _ = (s.card : ℤ) * (127 * 127) := by rw [Finset.sum_const, nsmul_eq_mul]
  have card_le : (s.card : ℤ) ≤ 2 ^ 17 := by
    have := Finset.card_le_univ s
    simp only [Fintype.card_fin] at this
    exact_mod_cast this.trans small
  have : (s.card : ℤ) * (127 * 127) ≤ 2 ^ 17 * (127 * 127) :=
    mul_le_mul_of_nonneg_right card_le (by norm_num)
  calc |codeDot s a.code b.code| ≤ 2 ^ 17 * (127 * 127) := total.trans this
    _ < 2 ^ 31 := by norm_num

/-- One binary multiplication `fl (m * D)` after `m = fl (σ * τ)`, each with relative error
`u` and absolute error `η`, stays within this slack of the real `σ τ D`. -/
theorem scaled_product_error (u eta scale integer exactScale approximate : ℝ)
    (u_nonneg : 0 ≤ u)
    (scale_error : |scale - exactScale| ≤ u * |exactScale| + eta)
    (product_error : |approximate - scale * integer| ≤ u * |scale * integer| + eta) :
    |approximate - exactScale * integer| ≤
      (2 * u + u ^ 2) * |exactScale * integer| + eta * (1 + u) * |integer| + eta := by
  have first : |scale * integer - exactScale * integer| ≤ (u * |exactScale| + eta) * |integer| := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right scale_error (abs_nonneg _)
  have magnitude : |scale * integer| ≤ |exactScale * integer| + (u * |exactScale| + eta) * |integer| := by
    have := abs_sub_abs_le_abs_sub (scale * integer) (exactScale * integer)
    linarith
  have triangle := abs_sub_le approximate (scale * integer) (exactScale * integer)
  have bounded : u * |scale * integer| ≤ u * (|exactScale * integer| + (u * |exactScale| + eta) * |integer|) :=
    mul_le_mul_of_nonneg_left magnitude u_nonneg
  have regroup : (u * |exactScale| + eta) * |integer| = u * |exactScale * integer| + eta * |integer| := by
    rw [abs_mul]; ring
  nlinarith [abs_nonneg integer, abs_nonneg (exactScale * integer)]

/-- The certified radius of one row: both quantization errors, the screen's own rounding
`slack`, and the reference score's rounding `reference`. -/
noncomputable def radius (rowError queryNorm copyNorm queryError slack reference : ℝ) : ℝ :=
  rowError * queryNorm + copyNorm * queryError + slack + reference

/-- The certified interval contains the reference score. -/
theorem int8_bounds_contain (x q : Fin n → ℝ) (row query : Int8Copy n)
    (score approximate rowError queryNorm copyNorm queryError slack reference : ℝ)
    (row_error : norm2 (x - row.value) ≤ rowError)
    (query_norm : norm2 q ≤ queryNorm)
    (copy_norm : norm2 row.value ≤ copyNorm)
    (query_error : norm2 (q - query.value) ≤ queryError)
    (screen_rounding : |approximate - dot row.value query.value| ≤ slack)
    (reference_rounding : |score - dot x q| ≤ reference) :
    approximate - radius rowError queryNorm copyNorm queryError slack reference ≤ score ∧
      score ≤ approximate + radius rowError queryNorm copyNorm queryError slack reference := by
  have quantized := quantized_score_error x q row.value query.value
  have first : norm2 (x - row.value) * norm2 q ≤ rowError * queryNorm :=
    mul_le_mul row_error query_norm (norm2_nonneg _) ((norm2_nonneg _).trans row_error)
  have second : norm2 row.value * norm2 (q - query.value) ≤ copyNorm * queryError :=
    mul_le_mul copy_norm query_error (norm2_nonneg _) ((norm2_nonneg _).trans copy_norm)
  have total : |score - approximate| ≤
      radius rowError queryNorm copyNorm queryError slack reference := by
    have chain := abs_sub_le score (dot x q) approximate
    have middle := abs_sub_le (dot x q) (dot row.value query.value) approximate
    rw [abs_sub_comm (dot row.value query.value) approximate] at middle
    unfold radius
    linarith
  exact interval_contains total

/-- **Exact certified 8-bit retrieval.** For every eligible row, let the screen's interval be
`approximate ± radius` with the hypotheses of `int8_bounds_contain`. Take the `k` rows with the
largest lower bounds as witnesses, keep every eligible row whose upper bound reaches their
smallest lower bound, and rerank those rows by reference score with the stable ordinal tie
break. The result is exactly the stable top-`k` of the full scan. -/
theorem int8_screen_rerank_exact {I : Type*} [DecidableEq I]
    (score lower upper : I → ℝ) (ordinal : I → Nat) (distinct : Function.Injective ordinal)
    (mask : I → Option Bool) {k : Nat} {source witnesses original result : Finset I}
    (nonempty : witnesses.Nonempty)
    (bracket : ∀ row ∈ eligible source mask, lower row ≤ score row ∧ score row ≤ upper row)
    (original_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k (eligible source mask) original)
    (lower_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      lower k (eligible source mask) witnesses)
    (result_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k
      (Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper
        (lowerThreshold lower witnesses nonempty) (eligible source mask)) result) :
    result = original :=
  stable_masked_screened_rerank_exact score lower upper ordinal distinct mask nonempty
    original_top lower_top (fun row member => (bracket row member).1)
    (fun row member => (bracket row member).2) result_top

/-- The per-row data an implementation stores and computes, assembled into the bracket that
`int8_screen_rerank_exact` needs. -/
theorem int8_rows_bracket {I : Type*} (source : Finset I) (mask : I → Option Bool)
    (x : I → Fin n → ℝ) (q : Fin n → ℝ) (rows : I → Int8Copy n) (query : Int8Copy n)
    (score approximate rowError copyNorm slack reference : I → ℝ) (queryNorm queryError : ℝ)
    (row_error : ∀ row, norm2 (x row - (rows row).value) ≤ rowError row)
    (copy_norm : ∀ row, norm2 (rows row).value ≤ copyNorm row)
    (query_norm : norm2 q ≤ queryNorm) (query_error : norm2 (q - query.value) ≤ queryError)
    (screen_rounding : ∀ row, |approximate row - dot (rows row).value query.value| ≤ slack row)
    (reference_rounding : ∀ row, |score row - dot (x row) q| ≤ reference row) :
    ∀ row ∈ eligible source mask,
      approximate row - radius (rowError row) queryNorm (copyNorm row) queryError (slack row)
          (reference row) ≤ score row ∧
        score row ≤ approximate row + radius (rowError row) queryNorm (copyNorm row) queryError
          (slack row) (reference row) :=
  fun row _ => int8_bounds_contain (x row) q (rows row) query (score row) (approximate row)
    (rowError row) queryNorm (copyNorm row) queryError (slack row) (reference row)
    (row_error row) query_norm (copy_norm row) query_error (screen_rounding row)
    (reference_rounding row)

end Mettapedia.Algebra.CertifiedInt8Screening
