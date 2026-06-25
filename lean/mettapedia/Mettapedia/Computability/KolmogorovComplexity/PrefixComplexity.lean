import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Real
import Mettapedia.Computability.KolmogorovComplexity.Prefix

/-!
# Prefix-free Kolmogorov Complexity (Chapter 2 bridge)

This file provides the minimal Chapter‑2 interface needed for Chapter 3 (Hutter 2005):

- `Kpf[U](x)` : prefix-free Kolmogorov complexity relative to a prefix-free machine `U`.
- Invariance: universal prefix-free machines agree up to an additive constant.
- Kraft/summability: `∑' x, 2^{-Kpf(x)} ≤ 1` (as an `ENNReal` statement).

We reuse the existing prefix-free machine framework from `Mettapedia.UniversalAI.SolomonoffPrior` and the
finite Kraft inequality from `Mettapedia.Computability.KolmogorovComplexity.Prefix`.
-/

namespace KolmogorovComplexity

open scoped Classical BigOperators

open Mettapedia.UniversalAI.SolomonoffPrior

abbrev PrefixFreeMachine := Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine
abbrev UniversalPFM := Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM

/-- Prefix-free Kolmogorov complexity relative to a prefix-free machine `U`. -/
noncomputable abbrev prefixComplexity (U : PrefixFreeMachine) (x : BinString) : ℕ :=
  Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity U x

notation "Kpf[" U "](" x ")" => prefixComplexity U x

/-- A universal prefix-free machine can output any finite binary string. -/
theorem universalPFM_has_program (U : PrefixFreeMachine) [UniversalPFM U] (x : BinString) :
    ∃ p : BinString, U.compute p = some x := by
  classical
  let Mx : PrefixFreeMachine :=
    { compute := fun p => if p = [] then some x else none
      prefix_free := by
        intro p q _ hpne hp
        have hp0 : p = [] := by
          by_contra hp0
          have : (if p = [] then some x else none) = none := by simp [hp0]
          exact hp this
        subst hp0
        have hq0 : q ≠ [] := by
          intro hq0
          apply hpne
          simp [hq0]
        simp [hq0] }
  obtain ⟨_c, hc⟩ := UniversalPFM.universal (U := U) (M := Mx)
  have hm : Mx.compute [] = some x := by simp [Mx]
  obtain ⟨q, hq, _hq_len⟩ := hc [] x hm
  exact ⟨q, hq⟩

/-- A chosen shortest program for `x` under a universal prefix-free machine. -/
noncomputable def shortestProgram (U : PrefixFreeMachine) [UniversalPFM U] (x : BinString) : BinString :=
  Classical.choose
    (Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity (U := U) (x := x)
      (h := universalPFM_has_program (U := U) x))

theorem shortestProgram_spec (U : PrefixFreeMachine) [UniversalPFM U] (x : BinString) :
    U.compute (shortestProgram U x) = some x ∧ (shortestProgram U x).length = Kpf[U](x) := by
  classical
  simpa [shortestProgram, prefixComplexity] using
    (Classical.choose_spec
      (Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity (U := U) (x := x)
        (h := universalPFM_has_program (U := U) x)))

theorem shortestProgram_injective (U : PrefixFreeMachine) [UniversalPFM U] :
    Function.Injective (shortestProgram U) := by
  intro x y hxy
  have hx := (shortestProgram_spec (U := U) x).1
  have hy := (shortestProgram_spec (U := U) y).1
  have hx' : U.compute (shortestProgram U y) = some x := by simpa [hxy] using hx
  exact Option.some.inj <| by
    calc
      (some x : Option BinString) = U.compute (shortestProgram U y) := hx'.symm
      _ = some y := hy

/-- Invariance: universal prefix-free machines agree up to an additive constant. -/
theorem invariance_Kpf (U V : PrefixFreeMachine) [UniversalPFM U] [UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString, Kpf[U](x) ≤ Kpf[V](x) + c := by
  obtain ⟨c, hc⟩ := Mettapedia.UniversalAI.SolomonoffPrior.invariance (U := U) (V := V)
  refine ⟨c, ?_⟩
  intro x
  have hx : ∃ p, V.compute p = some x := universalPFM_has_program (U := V) x
  exact hc x hx

/-- Convert the real weight `2^{-n}` into the `ENNReal`-native expression. -/
theorem ofReal_two_zpow_neg_nat (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) = (2 : ENNReal) ^ (-(n : ℤ)) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have h2pos : 0 < (2 : ℝ) := by norm_num
      change ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n)) = (2 : ENNReal) ^ (Int.negSucc n)
      simp [zpow_negSucc, ENNReal.ofReal_inv_of_pos, h2pos, ENNReal.ofReal_pow, h2pos.le]

theorem two_zpow_neg_nat (n : ℕ) : (2 : ENNReal) ^ (-(n : ℤ)) = ((2 : ENNReal) ^ n)⁻¹ := by
  cases n with
  | zero =>
      simp
  | succ n =>
      change (2 : ENNReal) ^ (Int.negSucc n) = ((2 : ENNReal) ^ n.succ)⁻¹
      simp [zpow_negSucc]

/-- Finite Kraft bound for the weights `2^{-Kpf[U](x)}`. -/
theorem sum_weightByKpf_le_one (U : PrefixFreeMachine) [UniversalPFM U] (s : Finset BinString) :
    (∑ x ∈ s, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ)))) ≤ 1 := by
  classical
  let progSet : Finset BinString := s.image (shortestProgram U)

  have hpf : PrefixFree (↑progSet : Set BinString) := by
    intro p hp q hq hpq hpref
    rcases Finset.mem_image.1 hp with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.1 hq with ⟨y, hy, rfl⟩
    have hxComp : U.compute (shortestProgram U x) ≠ none := by
      simp [shortestProgram_spec (U := U) x |>.1]
    have hyComp : U.compute (shortestProgram U y) = some y :=
      (shortestProgram_spec (U := U) y).1
    have hyNone : U.compute (shortestProgram U y) = none :=
      U.prefix_free (shortestProgram U x) (shortestProgram U y) hpref hpq hxComp
    simp [hyComp] at hyNone

  have hinj : Set.InjOn (shortestProgram U) (↑s : Set BinString) := by
    intro x hx y hy hxy
    exact shortestProgram_injective (U := U) hxy

  have h_prog_sum :
      (∑ p ∈ progSet, (2 : ℝ) ^ (-(p.length : ℤ))) =
        ∑ x ∈ s, (2 : ℝ) ^ (-((shortestProgram U x).length : ℤ)) := by
    simpa [progSet] using
      (Finset.sum_image (s := s) (g := shortestProgram U)
        (f := fun p => (2 : ℝ) ^ (-(p.length : ℤ))) hinj)

  have h_len_sum :
      (∑ x ∈ s, (2 : ℝ) ^ (-((shortestProgram U x).length : ℤ))) =
        ∑ x ∈ s, (2 : ℝ) ^ (-(Kpf[U](x) : ℤ)) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    simp [shortestProgram_spec (U := U) x |>.2]

  have h_kraft :
      (∑ p ∈ progSet, (2 : ℝ) ^ (-(p.length : ℤ))) ≤ 1 := by
    simpa [kraftSum, Mettapedia.UniversalAI.SolomonoffPrior.kraftSum] using
      (kraft_inequality (S := progSet) (hpf := hpf))

  have h_real :
      (∑ x ∈ s, (2 : ℝ) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 := by
    -- Rewrite the Kraft bound along `progSet` ↔ `s`.
    have h_eq :
        (∑ p ∈ progSet, (2 : ℝ) ^ (-(p.length : ℤ))) =
          ∑ x ∈ s, (2 : ℝ) ^ (-(Kpf[U](x) : ℤ)) :=
      h_prog_sum.trans h_len_sum
    have h_kraft' := h_kraft
    rw [h_eq] at h_kraft'
    exact h_kraft'

  have h_nonneg : ∀ x, x ∈ s → 0 ≤ (2 : ℝ) ^ (-(Kpf[U](x) : ℤ)) := by
    intro x _hx
    exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _

  -- Convert the real bound to `ENNReal`.
  have h_ofReal :
      (∑ x ∈ s, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ)))) =
        ENNReal.ofReal (∑ x ∈ s, (2 : ℝ) ^ (-(Kpf[U](x) : ℤ))) := by
    symm
    simpa using (ENNReal.ofReal_sum_of_nonneg (s := s)
      (f := fun x => (2 : ℝ) ^ (-(Kpf[U](x) : ℤ))) h_nonneg)

  calc
    (∑ x ∈ s, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ))))
        = ENNReal.ofReal (∑ x ∈ s, (2 : ℝ) ^ (-(Kpf[U](x) : ℤ))) := h_ofReal
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_real
    _ = 1 := by simp

/-- Finite Kraft bound, using `ENNReal` powers (matches Chapter 3 weights). -/
theorem sum_weightByKpf_le_one_ennreal (U : PrefixFreeMachine) [UniversalPFM U] (s : Finset BinString) :
    (∑ x ∈ s, (2 : ENNReal) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 := by
  simpa [two_zpow_neg_nat] using (sum_weightByKpf_le_one (U := U) s)

/-- Kraft/summability: `∑' x, 2^{-Kpf[U](x)} ≤ 1`. -/
theorem tsum_weightByKpf_le_one (U : PrefixFreeMachine) [UniversalPFM U] :
    (∑' x : BinString, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ)))) ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro s
  simpa using (sum_weightByKpf_le_one (U := U) s)

/-- Kraft/summability: `∑' x, 2^{-Kpf[U](x)} ≤ 1` using `ENNReal` powers. -/
theorem tsum_weightByKpf_le_one_ennreal (U : PrefixFreeMachine) [UniversalPFM U] :
    (∑' x : BinString, (2 : ENNReal) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro s
  simpa using (sum_weightByKpf_le_one_ennreal (U := U) s)

end KolmogorovComplexity
