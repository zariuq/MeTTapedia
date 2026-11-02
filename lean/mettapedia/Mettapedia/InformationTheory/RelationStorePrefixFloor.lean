import Mettapedia.InformationTheory.RelationStoreFloors
import Mettapedia.Computability.KolmogorovComplexity.Prefix

/-!
# The mean floor for self-delimiting stores

A store read from a stream must say where it ends: its descriptions form a
prefix-free code.  By Kraft's inequality such a code of `K` values has mean
length at least `log₂ K`, so a self-delimiting store of the `N`-element
relations over `M` tuples spends at least `log₂ C(M, N)` bits on average, the
information in a uniformly drawn relation.

* `card_le_two_rpow_mean_length` : a prefix-free code, injective on `F`, has
  `#F ≤ 2 ^ (mean length over F)`;
* `choose_le_two_rpow_mean_length` : for codes of the `N`-element relations,
  `C(M, N) ≤ 2 ^ (mean length)`.
-/

namespace Mettapedia.InformationTheory.RelationStoreFloors

open Finset KolmogorovComplexity

/-- Kraft's inequality for averages: a prefix-free code, injective on `F`, has
mean length over `F` at least `log₂ #F`. -/
theorem card_le_two_rpow_mean_length {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    (c : ι → BinString) (hinj : Set.InjOn c F)
    (hpf : PrefixFree (↑(F.image c) : Set BinString)) :
    (F.card : ℝ) ≤ (2 : ℝ) ^ ((∑ x ∈ F, ((c x).length : ℝ)) / F.card) := by
  classical
  have hK : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hkraft : ∑ x ∈ F, (2 : ℝ) ^ (-((c x).length : ℝ)) ≤ 1 := by
    have h := kraft_inequality (F.image c) hpf
    have hsum : kraftSum (F.image c) = ∑ x ∈ F, (2 : ℝ) ^ (-((c x).length : ℤ)) := by
      unfold kraftSum Mettapedia.UniversalAI.SolomonoffPrior.kraftSum
      exact sum_image fun x hx y hy hxy => hinj hx hy hxy
    rw [hsum] at h
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun x _ => ?_
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, zpow_neg, zpow_natCast]
  have hamgm := Real.geom_mean_le_arith_mean_weighted F (fun _ => 1 / (F.card : ℝ))
    (fun x => (2 : ℝ) ^ (-((c x).length : ℝ)))
    (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  have hprod : ∏ x ∈ F, ((2 : ℝ) ^ (-((c x).length : ℝ))) ^ (1 / (F.card : ℝ)) =
      (2 : ℝ) ^ (-((∑ x ∈ F, ((c x).length : ℝ)) / F.card)) := by
    have hfac : ∀ x ∈ F, ((2 : ℝ) ^ (-((c x).length : ℝ))) ^ (1 / (F.card : ℝ)) =
        (2 : ℝ) ^ (-((c x).length : ℝ) * (1 / (F.card : ℝ))) := fun x _ =>
      (Real.rpow_mul (by norm_num) _ _).symm
    rw [prod_congr rfl hfac, ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [← sum_mul, sum_neg_distrib]
    ring
  have hmean : (2 : ℝ) ^ (-((∑ x ∈ F, ((c x).length : ℝ)) / F.card)) ≤ 1 / F.card := by
    calc (2 : ℝ) ^ (-((∑ x ∈ F, ((c x).length : ℝ)) / F.card))
        = ∏ x ∈ F, ((2 : ℝ) ^ (-((c x).length : ℝ))) ^ (1 / (F.card : ℝ)) := hprod.symm
      _ ≤ ∑ x ∈ F, 1 / (F.card : ℝ) * (2 : ℝ) ^ (-((c x).length : ℝ)) := hamgm
      _ = 1 / F.card * ∑ x ∈ F, (2 : ℝ) ^ (-((c x).length : ℝ)) := by rw [mul_sum]
      _ ≤ 1 / F.card * 1 := by gcongr
      _ = 1 / F.card := mul_one _
  rw [Real.rpow_neg (by norm_num)] at hmean
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((∑ x ∈ F, ((c x).length : ℝ)) / F.card) := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ hpos hK] at hmean
  linarith

/-- A self-delimiting store of the `N`-element relations over `M` tuples spends
at least `log₂ C(M, N)` bits on average: `C(M, N) ≤ 2 ^ (mean length)`. -/
theorem choose_le_two_rpow_mean_length {M N : ℕ} (hN : N ≤ M)
    (c : Finset (Fin M) → BinString)
    (hinj : Set.InjOn c ((univ : Finset (Fin M)).powersetCard N : Set (Finset (Fin M))))
    (hpf : PrefixFree (↑(((univ : Finset (Fin M)).powersetCard N).image c) :
      Set BinString)) :
    (M.choose N : ℝ) ≤ (2 : ℝ) ^
      ((∑ s ∈ (univ : Finset (Fin M)).powersetCard N, ((c s).length : ℝ)) / M.choose N) := by
  have hcard : ((univ : Finset (Fin M)).powersetCard N).card = M.choose N := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  have hne : ((univ : Finset (Fin M)).powersetCard N).Nonempty :=
    powersetCard_nonempty.mpr (by simpa using hN)
  have h := card_le_two_rpow_mean_length _ hne c hinj hpf
  rwa [hcard] at h

end Mettapedia.InformationTheory.RelationStoreFloors
