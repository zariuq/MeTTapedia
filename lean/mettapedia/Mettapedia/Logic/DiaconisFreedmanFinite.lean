import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open BigOperators

namespace Mettapedia.Logic

/-! ## Finite L1 pushforward bound

This is a purely finite combinatorial inequality: pushing forward two
distributions along a function cannot increase the L1 distance.
-/

lemma l1_pushforward_le
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (μ ν : Ω → ℝ) (f : Ω → Γ) :
    (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
      ≤ ∑ ω, abs (μ ω - ν ω) := by
  classical
  -- Triangle inequality inside each fiber.
  have hγ :
      ∀ γ : Γ,
        abs ((∑ ω, if f ω = γ then μ ω else 0) -
            (∑ ω, if f ω = γ then ν ω else 0))
          ≤ ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    intro γ
    have hdiff :
        (∑ ω, if f ω = γ then (μ ω - ν ω) else 0) =
          (∑ ω, if f ω = γ then μ ω else 0) -
            (∑ ω, if f ω = γ then ν ω else 0) := by
      have hsub :=
        (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset Ω))
          (f := fun ω => if f ω = γ then μ ω else 0)
          (g := fun ω => if f ω = γ then ν ω else 0))
      have hsub' :
          ∑ ω, ((if f ω = γ then μ ω else 0) - (if f ω = γ then ν ω else 0)) =
            ∑ ω, if f ω = γ then (μ ω - ν ω) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro ω _
        by_cases hω : f ω = γ
        · simp [hω, sub_eq_add_neg]
        · simp [hω]
      exact (hsub'.symm.trans hsub)
    have h :=
      (Finset.abs_sum_le_sum_abs
        (s := (Finset.univ : Finset Ω))
        (f := fun ω => if f ω = γ then (μ ω - ν ω) else 0))
    have hrewrite :
        (∑ ω, abs (if f ω = γ then (μ ω - ν ω) else 0)) =
          ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro ω _
      by_cases hω : f ω = γ
      · simp [hω]
      · simp [hω]
    have h' : abs (∑ ω, if f ω = γ then (μ ω - ν ω) else 0) ≤
        ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
      simpa [hrewrite] using h
    simpa [hdiff] using h'

  -- Sum inequality over all γ (finite induction).
  have hsum_le :
      (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
        ≤ ∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset Γ)) ?h0 ?hstep
    · simp
    · intro γ s hγs ih
      have hγ' := hγ γ
      have hsum :=
        add_le_add hγ' ih
      -- expand sums over insert
      simpa [Finset.sum_insert, hγs, add_comm, add_left_comm, add_assoc] using hsum

  -- Swap sums.
  have hswap :
      (∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0) =
        ∑ ω, ∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    classical
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset Γ))
        (t := (Finset.univ : Finset Ω))
        (f := fun γ ω => if f ω = γ then abs (μ ω - ν ω) else 0))

  -- Finish by computing the inner γ-sum.
  calc
    (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
        ≤ ∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := hsum_le
    _ = ∑ ω, ∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0 := hswap
    _ = ∑ ω, abs (μ ω - ν ω) := by
        refine Finset.sum_congr rfl ?_
        intro ω _
        have :
            (∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0) =
              abs (μ ω - ν ω) := by
          classical
          simp
        simp

end Mettapedia.Logic

/-! ## IID vs injective sampling

We use a finite total-variation bound between uniform iid maps and uniform
injective maps. The concrete bound is the standard collision estimate.
-/

namespace Mettapedia.Logic

/-- Pair-collision mass bound for uniform maps `Fin (n+1) → Fin R`. -/
private lemma pair_mass_le_inv
    (R n : ℕ) (hR : 0 < R)
    (i j0 : Fin (n + 1)) (hij : i ≠ j0) :
    (∑ f : Fin (n + 1) → Fin R,
      if f i = f j0 then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0)
      ≤ (1 : ℝ) / (R : ℝ) := by
  classical
  let S : Finset (Fin (n + 1) → Fin R) :=
    (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter (fun f => f i = f j0)
  let c : ℝ := ((1 : ℝ) / (R : ℝ) ^ (n + 1))
  change (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0) ≤ (1 : ℝ) / (R : ℝ)
  have hsum_card :
      (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0) = (S.card : ℝ) * c := by
    have hcount :
        (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then (1 : ℝ) else 0) = (S.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [S]
    calc
      (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0)
        = c * (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then (1 : ℝ) else 0) := by
            refine Eq.symm ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro f _
            by_cases h : f i = f j0
            · simp [h, c]
            · simp [h, c]
      _ = c * (S.card : ℝ) := by rw [hcount]
      _ = (S.card : ℝ) * c := by ring
  have hcard_le : S.card ≤ Fintype.card (Fin n → Fin R) := by
    refine Finset.card_le_card_of_injOn (f := fun f : Fin (n + 1) → Fin R => j0.removeNth f) ?hmaps ?hinj
    · intro f hf
      simp
    · intro f hf g hg hfg
      apply funext
      intro x
      by_cases hx : x = j0
      · subst x
        have hfi_eq_fj : f i = f j0 := (Finset.mem_filter.mp hf).2
        have hgi_eq_gj : g i = g j0 := (Finset.mem_filter.mp hg).2
        have hi_eq : f i = g i := by
          have hi_mem : i ∈ Set.range j0.succAbove := by
            have : i ∈ ({j0}ᶜ : Set (Fin (n + 1))) := by
              simpa [Set.mem_compl] using hij
            simpa [Fin.range_succAbove] using this
          rcases hi_mem with ⟨t, rfl⟩
          have hfg' := congrArg (fun h : Fin n → Fin R => h t) hfg
          simpa [Fin.removeNth] using hfg'
        exact (hfi_eq_fj.symm.trans hi_eq).trans hgi_eq_gj
      · have hx_mem : x ∈ Set.range j0.succAbove := by
          have : x ∈ ({j0}ᶜ : Set (Fin (n + 1))) := by
            simpa [Set.mem_compl] using hx
          simpa [Fin.range_succAbove] using this
        rcases hx_mem with ⟨t, rfl⟩
        have hfg' := congrArg (fun h : Fin n → Fin R => h t) hfg
        simpa [Fin.removeNth] using hfg'
  have hcard_pow : Fintype.card (Fin n → Fin R) = R ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hcard_bound : (S.card : ℝ) ≤ (R : ℝ) ^ n := by
    have hnat : S.card ≤ R ^ n := by simpa [hcard_pow] using hcard_le
    exact_mod_cast hnat
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  calc
    (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0)
      = (S.card : ℝ) * c := hsum_card
    _ ≤ ((R : ℝ) ^ n) * c := by exact mul_le_mul_of_nonneg_right hcard_bound (by positivity)
    _ = (1 : ℝ) / (R : ℝ) := by
      dsimp [c]
      have hpow : (R : ℝ) ^ (n + 1) = (R : ℝ) ^ n * (R : ℝ) := by
        simp [pow_succ, mul_comm]
      rw [hpow]
      field_simp [hRr]

/-- Sum of all ordered off-diagonal pair-collision masses is bounded by
`m(m-1) / R` for `m = n+1`. -/
private lemma pair_sum_le_sq_inv
    (R n : ℕ) (hR : 0 < R) :
    let c : ℝ := ((1 : ℝ) / (R : ℝ) ^ (n + 1))
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if i = j then (0 : ℝ)
      else (∑ f : Fin (n + 1) → Fin R, if f i = f j then c else 0))
      ≤ ((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ) := by
  classical
  dsimp
  have hterm :
      ∀ i : Fin (n + 1),
      ∀ j : Fin (n + 1),
      (if i = j then (0 : ℝ)
        else (∑ f : Fin (n + 1) → Fin R,
          if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ (1 : ℝ) / (R : ℝ) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
      simpa [one_div] using pair_mass_le_inv R n hR i j hij
  have hsum_le :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if i = j then (0 : ℝ)
        else (∑ f : Fin (n + 1) → Fin R,
          if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (if i = j then (0 : ℝ) else ((1 : ℝ) / (R : ℝ))) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · exact (hterm i j).trans_eq (by simp [hij])
  calc
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if i = j then (0 : ℝ)
      else (∑ f : Fin (n + 1) → Fin R,
        if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (if i = j then (0 : ℝ) else ((1 : ℝ) / (R : ℝ))) := hsum_le
    _ = ((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ) := by
      have hinner :
          ∀ i : Fin (n + 1),
            (∑ j : Fin (n + 1), if i = j then (0 : ℝ) else ((1 : ℝ) / (R : ℝ)))
              = (n : ℝ) * ((1 : ℝ) / (R : ℝ)) := by
        intro i
        calc
          (∑ j : Fin (n + 1), if i = j then (0 : ℝ) else ((1 : ℝ) / (R : ℝ)))
              = ∑ j : Fin (n + 1),
                  (((1 : ℝ) / (R : ℝ)) - (if i = j then ((1 : ℝ) / (R : ℝ)) else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    by_cases hij : i = j
                    · simp [hij]
                    · simp [hij]
          _ = (∑ _j : Fin (n + 1), ((1 : ℝ) / (R : ℝ))) -
                (∑ j : Fin (n + 1), if i = j then ((1 : ℝ) / (R : ℝ)) else 0) := by
                  rw [Finset.sum_sub_distrib]
          _ = ((n + 1 : ℝ) * ((1 : ℝ) / (R : ℝ))) - ((1 : ℝ) / (R : ℝ)) := by
                simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
          _ = (n : ℝ) * ((1 : ℝ) / (R : ℝ)) := by ring
      calc
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (if i = j then (0 : ℝ) else ((1 : ℝ) / (R : ℝ))))
            = ∑ i : Fin (n + 1), ((n : ℝ) * ((1 : ℝ) / (R : ℝ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  exact hinner i
        _ = (n + 1 : ℝ) * ((n : ℝ) * ((1 : ℝ) / (R : ℝ))) := by
              simp [Finset.sum_const, Fintype.card_fin]
        _ = ((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ) := by ring

/-- Tight base L1 collision bound (`m(m-1)/R`) between iid and injective
distributions. This is the finite Diaconis–Freedman core estimate in
without-replacement form. -/
lemma l1_iid_inj_le_choose2
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R) :
    (∑ f : Fin m → Fin R,
        abs ((1 : ℝ) / (R : ℝ) ^ m -
          (if Function.Injective f then (1 : ℝ) / (R : ℝ) ^ m / (∑ g : Fin m → Fin R,
           if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
           else 0)))
      ≤ ((m : ℝ) * ((m : ℝ) - 1)) / (R : ℝ) := by
  classical
  cases m with
  | zero =>
      have hInj0 : Function.Injective (default : Fin 0 → Fin R) := by
        intro i
        exact Fin.elim0 i
      have hcard :
          ({x ∈ ({default} : Finset (Fin 0 → Fin R)) | Function.Injective x}).card = 1 := by
        have hfilter_eq :
            ({x ∈ ({default} : Finset (Fin 0 → Fin R)) | Function.Injective x}) =
              ({default} : Finset (Fin 0 → Fin R)) := by
          ext x
          constructor
          · intro hx
            exact (Finset.mem_filter.mp hx).1
          · intro hx
            refine Finset.mem_filter.mpr ?_
            refine ⟨hx, ?_⟩
            have hx' : x = default := Finset.mem_singleton.mp hx
            subst x
            simpa using hInj0
        simp [hfilter_eq]
      simp [hInj0, hcard]
  | succ n =>
      let μ0 : ℝ := (1 : ℝ) / (R : ℝ) ^ (n + 1)
      let Z : ℝ :=
        ∑ g : Fin (n + 1) → Fin R, if Function.Injective g then μ0 else 0
      let Pbad : ℝ :=
        ∑ f : Fin (n + 1) → Fin R, if Function.Injective f then 0 else μ0
      have hμ0_nonneg : 0 ≤ μ0 := by
        dsimp [μ0]
        positivity
      have hμ0_pos : 0 < μ0 := by
        dsimp [μ0]
        have hRr : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
        positivity
      have hPbad_nonneg : 0 ≤ Pbad := by
        dsimp [Pbad]
        refine Finset.sum_nonneg ?_
        intro f hf
        by_cases hif : Function.Injective f
        · simp [hif]
        · simp [hif, hμ0_nonneg]
      have hsum_all :
          (∑ f : Fin (n + 1) → Fin R, μ0) = 1 := by
        dsimp [μ0]
        have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
        calc
          (∑ f : Fin (n + 1) → Fin R, (1 : ℝ) / (R : ℝ) ^ (n + 1))
              = (Fintype.card (Fin (n + 1) → Fin R) : ℝ) * ((1 : ℝ) / (R : ℝ) ^ (n + 1)) := by
                  simp [Finset.sum_const]
          _ = ((R ^ (n + 1) : ℕ) : ℝ) * ((1 : ℝ) / (R : ℝ) ^ (n + 1)) := by
                simp [Fintype.card_fin]
          _ = 1 := by
                have hpow : ((R ^ (n + 1) : ℕ) : ℝ) = (R : ℝ) ^ (n + 1) := by
                  norm_num
                rw [hpow]
                field_simp [hRr]
      have hsplit_total : Z + Pbad = ∑ f : Fin (n + 1) → Fin R, μ0 := by
        calc
          Z + Pbad =
              (∑ f : Fin (n + 1) → Fin R,
                ((if Function.Injective f then μ0 else 0) +
                 (if Function.Injective f then 0 else μ0))) := by
                dsimp [Z, Pbad]
                rw [Finset.sum_add_distrib]
          _ = ∑ f : Fin (n + 1) → Fin R, μ0 := by
                refine Finset.sum_congr rfl ?_
                intro f hf
                by_cases hif : Function.Injective f
                · simp [hif]
                · simp [hif]
      have hPbad_eq : Pbad = 1 - Z := by
        have : Z + Pbad = 1 := by simpa [hsum_all] using hsplit_total
        linarith
      have hZ_le_one : Z ≤ 1 := by
        linarith [hPbad_nonneg, hPbad_eq]
      have hZ_pos : 0 < Z := by
        have hRm' : n + 1 ≤ R := by simpa using hRm
        have hμ0_le_Z : μ0 ≤ Z := by
          have hinj0 : Function.Injective (Fin.castLE hRm') := Fin.castLE_injective hRm'
          have hnonneg :
              ∀ g : Fin (n + 1) → Fin R, 0 ≤ if Function.Injective g then μ0 else 0 := by
            intro g
            by_cases hif : Function.Injective g
            · simp [hif, hμ0_nonneg]
            · simp [hif]
          calc
            μ0 = (if Function.Injective (Fin.castLE hRm') then μ0 else 0) := by simp [hinj0]
            _ ≤ Z := by
                  dsimp [Z]
                  exact Finset.single_le_sum (fun g hg => hnonneg g) (by simp)
        exact lt_of_lt_of_le hμ0_pos hμ0_le_Z
      have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
      have hOneLeInv : 1 ≤ 1 / Z := by
        rw [le_div_iff₀ hZ_pos]
        nlinarith [hZ_le_one]
      have hμ0_le_div : μ0 ≤ μ0 / Z := by
        have hmul : μ0 * 1 ≤ μ0 * (1 / Z) :=
          mul_le_mul_of_nonneg_left hOneLeInv hμ0_nonneg
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hsum_split :
          Finset.sum (Finset.univ : Finset (Fin (n + 1) → Fin R))
              (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
            =
          Finset.sum ((Finset.univ : Finset (Fin (n + 1) → Fin R)).filter Function.Injective)
              (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) +
          Finset.sum ((Finset.univ : Finset (Fin (n + 1) → Fin R)).filter (fun f => ¬ Function.Injective f))
              (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) := by
        simp [Finset.filter_not]
      let Sinj : Finset (Fin (n + 1) → Fin R) :=
        (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter Function.Injective
      let Sbad : Finset (Fin (n + 1) → Fin R) :=
        (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter (fun f => ¬ Function.Injective f)
      have hgood :
          Finset.sum Sinj (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
            = 1 - Z := by
        have hconst :
            ∀ f : Fin (n + 1) → Fin R,
              Function.Injective f →
              abs (μ0 - (if Function.Injective f then μ0 / Z else 0)) = μ0 / Z - μ0 := by
          intro f hf
          have hsub_nonpos : μ0 - μ0 / Z ≤ 0 := by linarith [hμ0_le_div]
          simp [hf, abs_of_nonpos hsub_nonpos]
        have hcardMul :
            Finset.sum Sinj (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
              = (Sinj.card : ℝ) * (μ0 / Z - μ0) := by
          calc
            Finset.sum Sinj (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
                = Finset.sum Sinj (fun _ => (μ0 / Z - μ0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro f hf
                    exact hconst f (by
                      have hf' : f ∈ (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter Function.Injective := by
                        simpa [Sinj] using hf
                      exact (Finset.mem_filter.mp hf').2)
            _ = (Sinj.card : ℝ) * (μ0 / Z - μ0) := by
                  simp [Finset.sum_const]
                  ring
        have hsum_inj_mu0 :
            Finset.sum Sinj (fun _ => μ0) = Z := by
          dsimp [Sinj, Z]
          calc
            Finset.sum (Finset.filter Function.Injective Finset.univ) (fun _ => μ0)
                = ∑ x : Fin (n + 1) → Fin R, if Function.Injective x then μ0 else 0 := by
                    rw [Finset.sum_filter]
            _ = ∑ g : Fin (n + 1) → Fin R, if Function.Injective g then μ0 else 0 := by
                  rfl
        calc
          Finset.sum Sinj (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
              = Finset.sum Sinj (fun _ => μ0 * (1 / Z - 1)) := by
                  refine Finset.sum_congr rfl ?_
                  intro f hf
                  have hf' : Function.Injective f := by
                    have hf'' : f ∈ (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter Function.Injective := by
                      simpa [Sinj] using hf
                    exact (Finset.mem_filter.mp hf'').2
                  calc
                    abs (μ0 - (if Function.Injective f then μ0 / Z else 0))
                        = μ0 / Z - μ0 := hconst f hf'
                    _ = μ0 * (1 / Z - 1) := by ring
          _ = (Finset.sum Sinj (fun _ => μ0)) * (1 / Z - 1) := by
                rw [Finset.sum_mul]
          _ = Z * (1 / Z - 1) := by rw [hsum_inj_mu0]
          _ = 1 - Z := by
                have hZinv : Z * Z⁻¹ = 1 := by field_simp [hZ_ne]
                calc
                  Z * (1 / Z - 1) = Z * (1 / Z) - Z := by ring
                  _ = 1 - Z := by simp [hZinv]
      have hbad :
          Finset.sum Sbad (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) = Pbad := by
        calc
          Finset.sum Sbad (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
              = Finset.sum Sbad (fun _ => μ0) := by
                    refine Finset.sum_congr rfl ?_
                    intro f hf
                    have hf' : ¬ Function.Injective f := by
                      have hf'' : f ∈ (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter (fun f => ¬ Function.Injective f) := by
                        simpa [Sbad] using hf
                      exact (Finset.mem_filter.mp hf'').2
                    simp [hf', abs_of_nonneg hμ0_nonneg]
          _ = Pbad := by
                dsimp [Pbad, Sbad]
                rw [Finset.sum_filter]
                simp
      have hL1_eq :
          Finset.sum (Finset.univ : Finset (Fin (n + 1) → Fin R))
            (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
            = 2 * Pbad := by
        calc
          Finset.sum (Finset.univ : Finset (Fin (n + 1) → Fin R))
            (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0)))
              =
            Finset.sum Sinj (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) +
            Finset.sum Sbad (fun f => abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) := by
              simpa [Sinj, Sbad] using hsum_split
          _ = (1 - Z) + Pbad := by rw [hgood, hbad]
          _ = Pbad + Pbad := by linarith [hPbad_eq]
          _ = 2 * Pbad := by ring
      have hPbad_le :
          Pbad ≤ (1 / 2 : ℝ) * (((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ)) := by
        have hper :
            ∀ f : Fin (n + 1) → Fin R,
              (if Function.Injective f then (0 : ℝ) else μ0)
                ≤ (1 / 2 : ℝ) *
                    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                      if i = j then (0 : ℝ) else if f i = f j then μ0 else 0) := by
          intro f
          have hnonneg :
              ∀ i' j' : Fin (n + 1),
                0 ≤ (if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0) := by
            intro i' j'
            by_cases hij' : i' = j'
            · simp [hij']
            · by_cases hfeq : f i' = f j'
              · simp [hij', hfeq, hμ0_nonneg]
              · simp [hij', hfeq]
          by_cases hf : Function.Injective f
          · have hsum_nonneg :
                0 ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                      if i = j then (0 : ℝ) else if f i = f j then μ0 else 0 := by
                exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))
            have hhalf_nonneg :
                0 ≤ (1 / 2 : ℝ) *
                    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                      if i = j then (0 : ℝ) else if f i = f j then μ0 else 0) := by
              exact mul_nonneg (by positivity) hsum_nonneg
            simpa [hf] using hhalf_nonneg
          · rcases Function.not_injective_iff.mp hf with ⟨i, j, hij_eq, hij_ne⟩
            let term : Fin (n + 1) × Fin (n + 1) → ℝ :=
              fun p => if p.1 = p.2 then (0 : ℝ) else if f p.1 = f p.2 then μ0 else 0
            let pairs : Finset (Fin (n + 1) × Fin (n + 1)) :=
              (Finset.univ : Finset (Fin (n + 1))).product (Finset.univ : Finset (Fin (n + 1)))
            let pair2 : Finset (Fin (n + 1) × Fin (n + 1)) := ({(i, j), (j, i)} : Finset _)
            have hsum_prod :
                (∑ i' : Fin (n + 1), ∑ j' : Fin (n + 1),
                  if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0)
                  = Finset.sum pairs term := by
              simpa [pairs, term] using
                (Finset.sum_product
                  (s := (Finset.univ : Finset (Fin (n + 1))))
                  (t := (Finset.univ : Finset (Fin (n + 1))))
                  (f := term)
                ).symm
            have hs2_sub :
                pair2 ⊆ pairs := by
              intro p hp
              simp [pairs]
            have hterm_nonneg : ∀ p : Fin (n + 1) × Fin (n + 1), 0 ≤ term p := by
              intro p
              exact hnonneg p.1 p.2
            have htwo_terms_le :
                Finset.sum pair2 term ≤ Finset.sum pairs term := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hs2_sub
                (by
                  intro p hp hpn
                  exact hterm_nonneg p)
            have hpair_ne : (i, j) ≠ (j, i) := by
              intro hpair
              exact hij_ne (by simpa using congrArg Prod.fst hpair)
            have htwo_terms_eval :
                Finset.sum pair2 term
                  = μ0 + μ0 := by
              dsimp [pair2]
              simp [term, hpair_ne, hij_eq, hij_ne, eq_comm]
            have htwo_mu_le :
                (2 : ℝ) * μ0
                  ≤ ∑ i' : Fin (n + 1), ∑ j' : Fin (n + 1),
                      if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0 := by
              calc
                (2 : ℝ) * μ0 = μ0 + μ0 := by ring
                _ = Finset.sum pair2 term := by
                      rw [htwo_terms_eval]
                _ ≤ Finset.sum pairs term := htwo_terms_le
                _ = ∑ i' : Fin (n + 1), ∑ j' : Fin (n + 1),
                      if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0 := by
                      exact hsum_prod.symm
            have hhalf :
                μ0 ≤ (1 / 2 : ℝ) *
                    (∑ i' : Fin (n + 1), ∑ j' : Fin (n + 1),
                      if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0) := by
              nlinarith [htwo_mu_le]
            calc
              (if Function.Injective f then (0 : ℝ) else μ0) = μ0 := by simp [hf]
              _ ≤ (1 / 2 : ℝ) *
                    (∑ i' : Fin (n + 1), ∑ j' : Fin (n + 1),
                      if i' = j' then (0 : ℝ) else if f i' = f j' then μ0 else 0) := hhalf
        have hsum_f :
            Pbad ≤
              ∑ f : Fin (n + 1) → Fin R,
                (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  if i = j then (0 : ℝ) else if f i = f j then μ0 else 0) := by
          dsimp [Pbad]
          refine Finset.sum_le_sum ?_
          intro f hf
          exact hper f
        have hsum_f_scaled :
            Pbad ≤
              (1 / 2 : ℝ) *
                (∑ f : Fin (n + 1) → Fin R,
                  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                    if i = j then (0 : ℝ) else if f i = f j then μ0 else 0) := by
          simpa [Finset.mul_sum] using hsum_f
        have hswap :
            (∑ f : Fin (n + 1) → Fin R,
              ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                if i = j then (0 : ℝ) else if f i = f j then μ0 else 0)
              =
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              if i = j then (0 : ℝ)
              else (∑ f : Fin (n + 1) → Fin R, if f i = f j then μ0 else 0)) := by
          calc
            (∑ f : Fin (n + 1) → Fin R,
              ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                if i = j then (0 : ℝ) else if f i = f j then μ0 else 0)
                = ∑ i : Fin (n + 1), ∑ f : Fin (n + 1) → Fin R,
                    ∑ j : Fin (n + 1), if i = j then (0 : ℝ) else if f i = f j then μ0 else 0 := by
                    simpa using
                      (Finset.sum_comm
                        (s := (Finset.univ : Finset (Fin (n + 1) → Fin R)))
                        (t := (Finset.univ : Finset (Fin (n + 1))))
                        (f := fun f i =>
                          ∑ j : Fin (n + 1), if i = j then (0 : ℝ) else if f i = f j then μ0 else 0))
            _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                    ∑ f : Fin (n + 1) → Fin R, if i = j then (0 : ℝ) else if f i = f j then μ0 else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simpa using
                    (Finset.sum_comm
                      (s := (Finset.univ : Finset (Fin (n + 1) → Fin R)))
                      (t := (Finset.univ : Finset (Fin (n + 1))))
                      (f := fun f j =>
                        if i = j then (0 : ℝ) else if f i = f j then μ0 else 0))
            _ = (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  if i = j then (0 : ℝ)
                  else (∑ f : Fin (n + 1) → Fin R, if f i = f j then μ0 else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    by_cases hij : i = j
                    · simp [hij]
                    · simp [hij]
        have hpair_bound :
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              if i = j then (0 : ℝ)
              else (∑ f : Fin (n + 1) → Fin R, if f i = f j then μ0 else 0))
            ≤ ((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ) := by
          dsimp [μ0]
          simpa using pair_sum_le_sq_inv R n hR
        have hpair_bound_half :
            (1 / 2 : ℝ) *
              (∑ f : Fin (n + 1) → Fin R,
                ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  if i = j then (0 : ℝ) else if f i = f j then μ0 else 0)
              ≤ (1 / 2 : ℝ) * (((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [hswap] using hpair_bound) (by positivity)
        exact hsum_f_scaled.trans hpair_bound_half
      calc
        (∑ f : Fin (n + 1) → Fin R,
            abs ((1 : ℝ) / (R : ℝ) ^ (n + 1) -
              (if Function.Injective f then (1 : ℝ) / (R : ℝ) ^ (n + 1) / (∑ g : Fin (n + 1) → Fin R,
               if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ (n + 1) else 0)
               else 0)))
            = (∑ f : Fin (n + 1) → Fin R, abs (μ0 - (if Function.Injective f then μ0 / Z else 0))) := by
              simp [μ0, Z]
        _ = 2 * Pbad := hL1_eq
        _ ≤ 2 * ((1 / 2 : ℝ) * (((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hPbad_le (by positivity)
        _ = ((n + 1 : ℝ) * (n : ℝ)) / (R : ℝ) := by ring
        _ = ((n + 1 : ℝ) * ((n + 1 : ℝ) - 1)) / (R : ℝ) := by ring
        _ = ((↑(n + 1) : ℝ) * (((↑(n + 1) : ℝ) - 1)) / (R : ℝ)) := by
              norm_num

/-- Coarse L1 collision bound (legacy form). -/
lemma l1_iid_inj_le
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R) :
    (∑ f : Fin m → Fin R,
        abs ((1 : ℝ) / (R : ℝ) ^ m -
          (if Function.Injective f then (1 : ℝ) / (R : ℝ) ^ m / (∑ g : Fin m → Fin R,
           if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
           else 0)))
      ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  have htight :
      (∑ f : Fin m → Fin R,
          abs ((1 : ℝ) / (R : ℝ) ^ m -
            (if Function.Injective f then (1 : ℝ) / (R : ℝ) ^ m / (∑ g : Fin m → Fin R,
             if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
             else 0)))
        ≤ ((m : ℝ) * ((m : ℝ) - 1)) / (R : ℝ) :=
    l1_iid_inj_le_choose2 R m hR hRm
  have hm1_le_m : (m : ℝ) - 1 ≤ (m : ℝ) := by nlinarith
  have hmul : (m : ℝ) * ((m : ℝ) - 1) ≤ (m : ℝ) * (m : ℝ) := by
    exact mul_le_mul_of_nonneg_left hm1_le_m (by positivity)
  have hdiv :
      ((m : ℝ) * ((m : ℝ) - 1)) / (R : ℝ) ≤ ((m : ℝ) * (m : ℝ)) / (R : ℝ) := by
    have hRnonneg : 0 ≤ (R : ℝ) := by positivity
    exact div_le_div_of_nonneg_right hmul hRnonneg
  have hfactor4 :
      ((m : ℝ) * (m : ℝ)) / (R : ℝ) ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
    have hXnonneg : 0 ≤ ((m : ℝ) * (m : ℝ)) / (R : ℝ) := by positivity
    calc
      ((m : ℝ) * (m : ℝ)) / (R : ℝ)
          ≤ (4 : ℝ) * (((m : ℝ) * (m : ℝ)) / (R : ℝ)) := by nlinarith
      _ = (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by ring
  exact htight.trans (hdiv.trans hfactor4)

end Mettapedia.Logic
