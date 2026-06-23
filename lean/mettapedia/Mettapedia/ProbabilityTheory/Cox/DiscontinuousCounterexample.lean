import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.Basic
import Mettapedia.ProbabilityTheory.Cox.Basic

/-!
# Cox's Theorem Requires Continuity: A Formal Counterexample

This file proves that Cox's theorem genuinely requires the continuity axiom.
Without continuity, the functional equation has pathological solutions that
are NOT equivalent to the standard product rule.

## Main Results

1. `discontinuousAdditive_exists`: There exists a discontinuous additive function ℝ → ℝ
   (classical result, Hamel 1905 - constructed here from a ℚ-basis)
2. `cox_underdetermined_without_continuity`: Without continuity, Cox's axioms admit
   multiple non-equivalent solutions

## Mathematical Background

Cauchy's functional equation f(x + y) = f(x) + f(y) has:
- Continuous solutions: only f(x) = cx (linear)
- Discontinuous solutions: pathological functions built from Hamel bases

The discontinuous solutions are constructed by:
1. Choosing a Hamel basis H for ℝ as a ℚ-vector space (requires Choice)
2. Defining f arbitrarily on H, then extending ℚ-linearly
3. If f is not ℝ-linear on H, the extension is discontinuous

Reference: https://en.wikipedia.org/wiki/Cauchy's_functional_equation

## Comparison with SD Counterexample

This is analogous to our SD (semidirect product) counterexample for K&S:
- SD shows K&S basic axioms don't imply commutativity → need Separation
- Hamel functions show Cox basic axioms don't determine F uniquely → need Continuity
-/

namespace Mettapedia.ProbabilityTheory.Cox.DiscontinuousCounterexample

open Classical Filter

open scoped Topology

noncomputable section

/-!
## Part 1: Discontinuous Additive Functions Exist

We construct the classical result (Hamel, 1905) that discontinuous
additive functions exist. The full construction requires:
1. ℝ is a ℚ-vector space (Module ℚ ℝ)
2. Existence of a Hamel basis (requires Axiom of Choice)
3. Extending a non-ℝ-linear function on the basis
-/

/-- A function is additive (satisfies Cauchy's functional equation) -/
def IsAdditive (f : ℝ → ℝ) : Prop := ∀ x y, f (x + y) = f x + f y

/-- Continuous additive functions are linear: f(x) = c·x for some c.
    This is a standard result from real analysis. -/
theorem continuous_additive_is_linear (f : ℝ → ℝ) (hf : IsAdditive f) (hc : Continuous f) :
    ∃ c : ℝ, ∀ x, f x = c * x := by
  -- The standard proof uses:
  -- 1. f(qx) = q·f(x) for rational q (from additivity)
  -- 2. Continuity extends this to all reals
  -- 3. So f(x) = f(1)·x
  have hf0 : f 0 = 0 := by
    have h0 : f 0 = f 0 + f 0 := by
      simpa using hf 0 0
    have h0' : 0 = f 0 := by
      have h0'' : f 0 + 0 = f 0 + f 0 := by
        simpa using h0
      exact add_left_cancel h0''
    simpa using h0'.symm
  let f_add : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := hf0
      map_add' := by
        intro x y
        exact hf x y }
  have hf_cont : Continuous f_add := by
    simpa using! hc
  refine ⟨f 1, ?_⟩
  intro x
  have hsmul :
      f_add (x • (1 : ℝ)) = x • f_add 1 :=
    map_real_smul (f := f_add) hf_cont x 1
  have hsmul' : f x = x * f 1 := by
    simpa [f_add, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmul
  simpa [mul_comm] using hsmul'

/-- **Hamel (1905)**: There exist discontinuous additive functions.

We give a concrete construction using a ℚ-basis of ℝ. The key idea:
1. `{1, √2}` is ℚ-linearly independent (since √2 is irrational).
2. Extend this set to a basis `B` of ℝ over ℚ.
3. Define a ℚ-linear map `f` that sends the basis element `√2` to `1`
   and all other basis elements to `0`.
4. Then `f` is additive but not of the form `c·x`, hence not continuous.
-/
theorem discontinuousAdditive_exists : ∃ f : ℝ → ℝ, IsAdditive f ∧ ¬Continuous f := by
  classical
  let s : Set ℝ := {(1 : ℝ), Real.sqrt 2}
  have hlin : LinearIndepOn ℚ id s := by
    refine linearIndepOn_id_pair (K := ℚ) (x := (1 : ℝ)) (y := Real.sqrt 2) ?_ ?_
    · norm_num
    · intro a
      have hrat : (Real.sqrt 2) ≠ (a : ℝ) := (irrational_sqrt_two.ne_rat a)
      have hrat' : (a : ℝ) ≠ (Real.sqrt 2) := hrat.symm
      simpa [smul_eq_mul] using hrat'
  let B : Module.Basis (hlin.extend (Set.subset_univ s)) ℚ ℝ :=
    Module.Basis.extend (K := ℚ) (V := ℝ) hlin
  have hsubset : s ⊆ hlin.extend (Set.subset_univ s) :=
    Module.Basis.subset_extend (K := ℚ) (V := ℝ) hlin
  have h1 : (1 : ℝ) ∈ hlin.extend (Set.subset_univ s) := hsubset (by simp [s])
  have h2 : (Real.sqrt 2) ∈ hlin.extend (Set.subset_univ s) := hsubset (by simp [s])
  let x1 : hlin.extend (Set.subset_univ s) := ⟨1, h1⟩
  let x2 : hlin.extend (Set.subset_univ s) := ⟨Real.sqrt 2, h2⟩
  have hx12 : x1 ≠ x2 := by
    intro h
    have h' : (1 : ℝ) = Real.sqrt 2 := by
      simpa [x1, x2] using congrArg Subtype.val h
    exact (irrational_sqrt_two.ne_rat (1 : ℚ)) (by simpa using h'.symm)
  let g : hlin.extend (Set.subset_univ s) → ℝ := fun x => if x = x2 then 1 else 0
  let fLin : ℝ →ₗ[ℚ] ℝ := B.constr ℚ g
  let f : ℝ → ℝ := fun x => fLin x
  have hf_add : IsAdditive f := by
    intro x y
    change fLin (x + y) = fLin x + fLin y
    exact map_add fLin x y
  have hf1 : f 1 = 0 := by
    have hfx1 : f 1 = g x1 := by
      simpa [f, fLin, B, x1] using
        (B.constr_basis (S := ℚ) (f := g) (i := x1))
    have hgx1 : g x1 = 0 := by
      simp [g, x1, x2, hx12]
    simpa [hgx1] using hfx1
  have hf2 : f (Real.sqrt 2) = 1 := by
    have hfx2 : f (Real.sqrt 2) = g x2 := by
      simpa [f, fLin, B, x2] using
        (B.constr_basis (S := ℚ) (f := g) (i := x2))
    have hgx2 : g x2 = 1 := by
      simp [g, x2]
    simpa [hgx2] using hfx2
  have hnot : ¬Continuous f := by
    intro hcont
    obtain ⟨c, hc⟩ := continuous_additive_is_linear f hf_add hcont
    have hc1 : f 1 = c := by simpa using hc 1
    have hc0 : c = 0 := by simpa [hf1] using hc1.symm
    have hfs : f (Real.sqrt 2) = 0 := by
      simpa [hc0] using hc (Real.sqrt 2)
    have : (1 : ℝ) = 0 := by
      have hfs' := hfs
      rw [hf2] at hfs'
      exact hfs'
    exact one_ne_zero this
  exact ⟨f, hf_add, hnot⟩

/-!
## Part 2: Cox Without Continuity is Underdetermined

If F : ℝ → ℝ → ℝ satisfies:
- Associativity: F(F(x,y), z) = F(x, F(y,z))
- Identity: F(1,y) = y, F(x,1) = x

Then F(x,y) = φ⁻¹(φ(x) + φ(y)) for some additive φ.

Without continuity, φ can be any of the uncountably many discontinuous
additive functions, giving uncountably many non-equivalent solutions.
-/

/-- A conjunction rule (without continuity requirement) -/
structure ConjunctionRuleNoCont where
  F : ℝ → ℝ → ℝ
  F_assoc : ∀ x y z, F (F x y) z = F x (F y z)
  F_one_left : ∀ y, F 1 y = y
  F_one_right : ∀ x, F x 1 = x

/-- The standard product rule x · y -/
def standardF : ℝ → ℝ → ℝ := fun x y => x * y

/-- Standard product satisfies the axioms -/
def standardConjunctionRule : ConjunctionRuleNoCont where
  F := standardF
  F_assoc := fun x y z => by simp [standardF, mul_assoc]
  F_one_left := fun y => by simp [standardF]
  F_one_right := fun x => by simp [standardF]

/-! ### Swap-based conjunction rules (explicit discontinuous models) -/

private def swapF (b : ℝ) : ℝ → ℝ → ℝ := fun x y =>
  (Equiv.swap (0 : ℝ) b).symm ((Equiv.swap (0 : ℝ) b) x + (Equiv.swap (0 : ℝ) b) y - 1)

private lemma swapF_assoc (b : ℝ) : ∀ x y z, swapF b (swapF b x y) z = swapF b x (swapF b y z) := by
  intro x y z
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have hψ : ∀ x y, ψ (swapF b x y) = ψ x + ψ y - 1 := by
    intro x y
    simp [swapF, ψ]
  apply ψ.injective
  have h1 : ψ (swapF b (swapF b x y) z) = ψ x + ψ y + ψ z - 2 := by
    calc
      ψ (swapF b (swapF b x y) z) = ψ (swapF b x y) + ψ z - 1 := by
        simp [swapF, ψ]
      _ = (ψ x + ψ y - 1) + ψ z - 1 := by simp [hψ]
      _ = ψ x + ψ y + ψ z - 2 := by ring
  have h2 : ψ (swapF b x (swapF b y z)) = ψ x + ψ y + ψ z - 2 := by
    calc
      ψ (swapF b x (swapF b y z)) = ψ x + ψ (swapF b y z) - 1 := by
        simp [swapF, ψ]
      _ = ψ x + (ψ y + ψ z - 1) - 1 := by simp [hψ]
      _ = ψ x + ψ y + ψ z - 2 := by ring
  simp [h1, h2]

private lemma swapF_one_left (b : ℝ) (hb : b ≠ 1) : ∀ y, swapF b 1 y = y := by
  intro y
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have h1 : ψ 1 = (1 : ℝ) := by
    have h10 : (1 : ℝ) ≠ 0 := by norm_num
    have h1b : (1 : ℝ) ≠ b := by simpa using hb.symm
    simp [ψ, Equiv.swap_apply_of_ne_of_ne, h10, h1b]
  apply ψ.injective
  simp [swapF, ψ, h1]

private lemma swapF_one_right (b : ℝ) (hb : b ≠ 1) : ∀ x, swapF b x 1 = x := by
  intro x
  let ψ : ℝ ≃ ℝ := Equiv.swap (0 : ℝ) b
  have h1 : ψ 1 = (1 : ℝ) := by
    have h10 : (1 : ℝ) ≠ 0 := by norm_num
    have h1b : (1 : ℝ) ≠ b := by simpa using hb.symm
    simp [ψ, Equiv.swap_apply_of_ne_of_ne, h10, h1b]
  apply ψ.injective
  simp [swapF, ψ, h1]

private lemma swapF_discontinuous (b : ℝ) (hb : 1 < b) :
    ¬Continuous (Function.uncurry (swapF b)) := by
  intro hcont
  let g : ℝ → ℝ := fun x => swapF b x b
  have hg_cont : Continuous g := by
    have hpair : Continuous fun x : ℝ => (x, b) := continuous_id.prodMk continuous_const
    simpa [g] using! hcont.comp hpair
  have hbpos : (0 : ℝ) < b := lt_trans (by norm_num) hb
  have hb1ne0 : b - 1 ≠ 0 := by linarith
  have hb1neb : b - 1 ≠ b := by linarith
  have hswap_b1 : Equiv.swap (0 : ℝ) b (b - 1) = b - 1 := by
    exact Equiv.swap_apply_of_ne_of_ne hb1ne0 hb1neb
  have hg0 : g 0 = b - 1 := by
    calc
      g 0 = Equiv.swap (0 : ℝ) b (b + 0 - 1) := by
        simp [g, swapF, Equiv.swap_apply_left, Equiv.swap_apply_right]
      _ = Equiv.swap (0 : ℝ) b (b - 1) := by simp
      _ = b - 1 := hswap_b1
  have hseq_val : ∀ n : ℕ, g ((n : ℝ) + 2)⁻¹ = ((n : ℝ) + 2)⁻¹ - 1 := by
    intro n
    have hden : 0 < (n : ℝ) + 2 := by nlinarith
    have hxpos : 0 < ((n : ℝ) + 2)⁻¹ := by
      have hxpos' : 0 < (1 : ℝ) / ((n : ℝ) + 2) := one_div_pos.mpr hden
      simpa [one_div] using hxpos'
    have hxlt1 : ((n : ℝ) + 2)⁻¹ < 1 := by
      have hpos : (0 : ℝ) < 1 := by norm_num
      have hlt : (1 : ℝ) < (n : ℝ) + 2 := by nlinarith
      have h := one_div_lt_one_div_of_lt hpos hlt
      simpa [one_div] using h
    have hx0 : ((n : ℝ) + 2)⁻¹ ≠ 0 := ne_of_gt hxpos
    have hxb : ((n : ℝ) + 2)⁻¹ ≠ b := by
      exact ne_of_lt (lt_trans hxlt1 hb)
    have hxneg : ((n : ℝ) + 2)⁻¹ - 1 < 0 := sub_lt_zero.mpr hxlt1
    have hx1ne0 : ((n : ℝ) + 2)⁻¹ - 1 ≠ 0 := ne_of_lt hxneg
    have hx1neb : ((n : ℝ) + 2)⁻¹ - 1 ≠ b := by
      have hx1ltb : ((n : ℝ) + 2)⁻¹ - 1 < b := lt_trans hxneg hbpos
      exact ne_of_lt hx1ltb
    have hswap_x : Equiv.swap (0 : ℝ) b ((n : ℝ) + 2)⁻¹ = ((n : ℝ) + 2)⁻¹ := by
      exact Equiv.swap_apply_of_ne_of_ne hx0 hxb
    have hswap_b : Equiv.swap (0 : ℝ) b b = (0 : ℝ) := by
      simp [Equiv.swap_apply_right]
    have hswap_x1 :
        Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ - 1) = ((n : ℝ) + 2)⁻¹ - 1 := by
      simpa using (Equiv.swap_apply_of_ne_of_ne hx1ne0 hx1neb)
    calc
      g ((n : ℝ) + 2)⁻¹
          = Equiv.swap (0 : ℝ) b
              (Equiv.swap (0 : ℝ) b ((n : ℝ) + 2)⁻¹ + Equiv.swap (0 : ℝ) b b - 1) := by
                simp [g, swapF]
      _ = Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ + 0 - 1) := by
        simp [hswap_x, hswap_b]
      _ = Equiv.swap (0 : ℝ) b (((n : ℝ) + 2)⁻¹ - 1) := by simp
      _ = ((n : ℝ) + 2)⁻¹ - 1 := hswap_x1
  have hx : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hshift :=
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : ℝ) + 1)⁻¹) 1).2 hbase
    simpa [one_add_one_eq_two, add_assoc, add_comm, add_left_comm] using hshift
  have hx' : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹ - 1) atTop (𝓝 (-1)) := by
    simpa using (hx.sub tendsto_const_nhds)
  have hseq : Tendsto (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) atTop (𝓝 (-1)) := by
    have hfun :
        (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) =
          fun n : ℕ => ((n : ℝ) + 2)⁻¹ - 1 := funext hseq_val
    simpa [hfun] using hx'
  have hcont0 : Tendsto (fun n : ℕ => g ((n : ℝ) + 2)⁻¹) atTop (𝓝 (g 0)) :=
    (hg_cont.tendsto 0).comp hx
  have hg0eq' : (-1 : ℝ) = g 0 :=
    tendsto_nhds_unique (l := atTop) (f := fun n : ℕ => g ((n : ℝ) + 2)⁻¹) hseq hcont0
  have hg0eq : g 0 = (-1 : ℝ) := hg0eq'.symm
  have hg0ne : g 0 ≠ (-1 : ℝ) := by
    have hb1pos : (0 : ℝ) < b - 1 := by linarith
    have hb1ne : b - 1 ≠ (-1 : ℝ) := by
      exact ne_of_gt (lt_trans (by norm_num : (-1 : ℝ) < 0) hb1pos)
    simpa [hg0] using hb1ne
  exact (hg0ne hg0eq).elim

/-- Given a discontinuous additive φ, we can construct a non-standard
    conjunction rule that is NOT equivalent to multiplication. -/
theorem nonstandard_conjunction_exists :
    ∃ (C : ConjunctionRuleNoCont), ¬Continuous (Function.uncurry C.F) ∧
      C.F ≠ standardF := by
  classical
  let C : ConjunctionRuleNoCont :=
    { F := swapF 2
      F_assoc := swapF_assoc 2
      F_one_left := swapF_one_left 2 (by norm_num)
      F_one_right := swapF_one_right 2 (by norm_num) }
  have hdisc : ¬Continuous (Function.uncurry C.F) := by
    simpa [C] using swapF_discontinuous 2 (by norm_num)
  have hneq : C.F ≠ standardF := by
    intro h
    have hval := congrArg (fun F => F 0 2) h
    have hleft : C.F 0 2 = (1 : ℝ) := by
      have h10 : (1 : ℝ) ≠ 0 := by norm_num
      have h12 : (1 : ℝ) ≠ 2 := by norm_num
      have hswap1 : Equiv.swap (0 : ℝ) 2 (1 : ℝ) = (1 : ℝ) := by
        simpa using (Equiv.swap_apply_of_ne_of_ne (a := 0) (b := 2) h10 h12)
      calc
        C.F 0 2 = Equiv.swap (0 : ℝ) 2 (2 - 1) := by
          simp [C, swapF, Equiv.swap_apply_left, Equiv.swap_apply_right]
        _ = Equiv.swap (0 : ℝ) 2 (1 : ℝ) := by norm_num
        _ = (1 : ℝ) := hswap1
    have hright : standardF 0 2 = (0 : ℝ) := by simp [standardF]
    have hval' : C.F 0 2 = standardF 0 2 := by
      change (fun F => F 0 2) C.F = (fun F => F 0 2) standardF
      exact hval
    have hcontra : (1 : ℝ) = 0 := by
      have hval'' := hval'
      rw [hleft, hright] at hval''
      exact hval''
    exact one_ne_zero hcontra
  exact ⟨C, hdisc, hneq⟩

/-- Main theorem: Cox's axioms without continuity admit multiple
    non-equivalent solutions, proving continuity is essential. -/
theorem cox_underdetermined_without_continuity :
    ∃ (C₁ C₂ : ConjunctionRuleNoCont),
      ¬Continuous (Function.uncurry C₁.F) ∧
      ¬Continuous (Function.uncurry C₂.F) ∧
      C₁.F ≠ C₂.F := by
  classical
  let C₁ : ConjunctionRuleNoCont :=
    { F := swapF 2
      F_assoc := swapF_assoc 2
      F_one_left := swapF_one_left 2 (by norm_num)
      F_one_right := swapF_one_right 2 (by norm_num) }
  let C₂ : ConjunctionRuleNoCont :=
    { F := swapF 3
      F_assoc := swapF_assoc 3
      F_one_left := swapF_one_left 3 (by norm_num)
      F_one_right := swapF_one_right 3 (by norm_num) }
  have hdisc₁ : ¬Continuous (Function.uncurry C₁.F) := by
    simpa [C₁] using swapF_discontinuous 2 (by norm_num)
  have hdisc₂ : ¬Continuous (Function.uncurry C₂.F) := by
    simpa [C₂] using swapF_discontinuous 3 (by norm_num)
  have hneq : C₁.F ≠ C₂.F := by
    intro h
    have hval := congrArg (fun F => F 0 2) h
    have hleft : C₁.F 0 2 = (1 : ℝ) := by
      have h10 : (1 : ℝ) ≠ 0 := by norm_num
      have h12 : (1 : ℝ) ≠ 2 := by norm_num
      have hswap1 : Equiv.swap (0 : ℝ) 2 (1 : ℝ) = (1 : ℝ) := by
        simpa using (Equiv.swap_apply_of_ne_of_ne (a := 0) (b := 2) h10 h12)
      calc
        C₁.F 0 2 = Equiv.swap (0 : ℝ) 2 (2 - 1) := by
          simp [C₁, swapF, Equiv.swap_apply_left, Equiv.swap_apply_right]
        _ = Equiv.swap (0 : ℝ) 2 (1 : ℝ) := by norm_num
        _ = (1 : ℝ) := hswap1
    have hright : C₂.F 0 2 = (4 : ℝ) := by
      have hswap2 : Equiv.swap (0 : ℝ) 3 (2 : ℝ) = (2 : ℝ) := by
        have h20 : (2 : ℝ) ≠ 0 := by norm_num
        have h23 : (2 : ℝ) ≠ 3 := by norm_num
        simpa using (Equiv.swap_apply_of_ne_of_ne (a := 0) (b := 3) h20 h23)
      have hswap4 : Equiv.swap (0 : ℝ) 3 (4 : ℝ) = (4 : ℝ) := by
        have h40 : (4 : ℝ) ≠ 0 := by norm_num
        have h43 : (4 : ℝ) ≠ 3 := by norm_num
        simpa using (Equiv.swap_apply_of_ne_of_ne (a := 0) (b := 3) h40 h43)
      calc
        C₂.F 0 2 = Equiv.swap (0 : ℝ) 3 (3 + 2 - 1) := by
          simp [C₂, swapF, Equiv.swap_apply_left, hswap2]
        _ = Equiv.swap (0 : ℝ) 3 (4 : ℝ) := by norm_num
        _ = (4 : ℝ) := hswap4
    have hval' : C₁.F 0 2 = C₂.F 0 2 := by
      change (fun F => F 0 2) C₁.F = (fun F => F 0 2) C₂.F
      exact hval
    have hcontra : (1 : ℝ) = 4 := by
      have hval'' := hval'
      rw [hleft, hright] at hval''
      exact hval''
    exact by linarith [hcontra]
  exact ⟨C₁, C₂, hdisc₁, hdisc₂, hneq⟩

/-!
## Part 3: The Philosophical Point

Without continuity:
- Cox's axioms have UNCOUNTABLY many solutions (one for each Hamel basis choice)
- None of these is "the" probability product rule
- Continuity is what singles out F(x,y) = x·y as the unique solution

This is analogous to how K&S's separation axiom is needed to rule out
the semidirect product counterexample SD.

| Axiom System | Without Extra Axiom | With Extra Axiom |
|--------------|---------------------|------------------|
| K&S          | SD counterexample   | Separation → ℝ₊  |
| Cox          | Hamel pathologies   | Continuity → x·y |
-/

/-- The graph of any discontinuous additive function is dense in ℝ² -/
theorem discontinuousAdditive_graph_dense (f : ℝ → ℝ)
    (hf : IsAdditive f) (hdisc : ¬Continuous f) :
    Dense {p : ℝ × ℝ | p.2 = f p.1} := by
  classical
  have hf0 : f 0 = 0 := by
    have h0 : f 0 = f 0 + f 0 := by
      simpa using hf 0 0
    have h0' : 0 = f 0 := by
      have h0'' : f 0 + 0 = f 0 + f 0 := by
        simpa using h0
      exact add_left_cancel h0''
    simpa using h0'.symm
  let f_add : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := hf0
      map_add' := by
        intro x y
        exact hf x y }
  have hf_rat : ∀ q : ℚ, ∀ x, f (q • x) = q • f x := by
    intro q x
    simpa [f_add] using (map_rat_smul (f := f_add) q x)
  have hf_rat_mul : ∀ q : ℚ, ∀ x, f ((q : ℝ) * x) = (q : ℝ) * f x := by
    intro q x
    have hcast_x : (q : ℝ) * x = q • x := by
      simpa [smul_eq_mul] using (Rat.cast_smul_eq_qsmul (R := ℝ) (q := q) (x := x))
    have hcast_fx : (q : ℝ) * f x = q • f x := by
      simpa [smul_eq_mul] using (Rat.cast_smul_eq_qsmul (R := ℝ) (q := q) (x := f x))
    calc
      f ((q : ℝ) * x) = f (q • x) := by
        simp [hcast_x]
      _ = q • f x := hf_rat q x
      _ = (q : ℝ) * f x := by
        simp [hcast_fx]
  have hx0 : ∃ x, f x ≠ f 1 * x := by
    by_contra h
    push_neg at h
    have hcont : Continuous f := by
      have hfun : f = fun x => f 1 * x := funext h
      refine hfun ▸ (continuous_const.mul continuous_id)
    exact hdisc hcont
  rcases hx0 with ⟨x0, hx0⟩
  let det : ℝ := f x0 - f 1 * x0
  have hdet : det ≠ 0 := sub_ne_zero.mpr hx0
  let L : ℝ × ℝ → ℝ × ℝ :=
    fun p => (p.1 + p.2 * x0, p.1 * f 1 + p.2 * f x0)
  have hL_cont : Continuous L := by
    refine (continuous_fst.add (continuous_snd.mul continuous_const)).prodMk ?_
    exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)
  have hL_surj : Function.Surjective L := by
    intro p
    let b : ℝ := (p.2 - p.1 * f 1) / det
    let a : ℝ := p.1 - b * x0
    refine ⟨(a, b), ?_⟩
    ext
    · simp [L, a, add_comm, add_left_comm, sub_eq_add_neg]
    ·
      have hbdet : b * det = p.2 - p.1 * f 1 := by
        simp [b, det, hdet]
      calc
        a * f 1 + b * f x0
            = (p.1 - b * x0) * f 1 + b * f x0 := by simp [a]
        _ = p.1 * f 1 + b * (f x0 - x0 * f 1) := by ring
        _ = p.1 * f 1 + b * det := by simp [det, mul_comm]
        _ = p.1 * f 1 + (p.2 - p.1 * f 1) := by simp [hbdet]
        _ = p.2 := by ring
  have hL_dense : DenseRange L := Function.Surjective.denseRange hL_surj
  let f_rat : ℚ × ℚ → ℝ × ℝ :=
    fun q => ((q.1 : ℝ), (q.2 : ℝ))
  have hRat : DenseRange f_rat := by
    have hQ : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.denseRange_cast
    simpa [f_rat] using! (DenseRange.prodMap hQ hQ)
  have hDenseRange : DenseRange (L ∘ f_rat) :=
    DenseRange.comp hL_dense hRat hL_cont
  have hDense : Dense (Set.range (L ∘ f_rat)) := by
    simpa [DenseRange] using hDenseRange
  have hsubset : Set.range (L ∘ f_rat) ⊆ {p : ℝ × ℝ | p.2 = f p.1} := by
    rintro p ⟨q, rfl⟩
    have h1 : f (q.1 : ℝ) = (q.1 : ℝ) * f 1 := by
      simpa using (hf_rat_mul q.1 1)
    have h2 : f ((q.2 : ℝ) * x0) = (q.2 : ℝ) * f x0 := by
      simpa using (hf_rat_mul q.2 x0)
    dsimp [L, f_rat]
    calc
      (q.1 : ℝ) * f 1 + (q.2 : ℝ) * f x0
          = f (q.1 : ℝ) + f ((q.2 : ℝ) * x0) := by
            simp [h1, h2]
      _ = f ((q.1 : ℝ) + (q.2 : ℝ) * x0) := by
            symm
            simpa using hf (q.1 : ℝ) ((q.2 : ℝ) * x0)
  exact Dense.mono hsubset hDense

end

end Mettapedia.ProbabilityTheory.Cox.DiscontinuousCounterexample
