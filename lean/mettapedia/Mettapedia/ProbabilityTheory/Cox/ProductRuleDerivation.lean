import Mettapedia.ProbabilityTheory.Cox.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
-- Import KS tools for additive functions on positive reals (no extra axioms - pure mathlib theorems)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation

/-!
# Cox's Theorem: The Product Rule Derivation

This file provides the complete derivation of the probability product rule from
Cox's axioms, following Cox's original approach in "The Algebra of Probable Inference" (1961).

## Cox's Approach

Cox's key insight is that the product rule F(x,y) = x·y is FORCED by:
1. **Associativity**: F(F(x,y),z) = F(x,F(y,z))
2. **Boundary conditions**: F(1,y) = y, F(x,1) = x, F(0,y) = 0, F(x,0) = 0
3. **Monotonicity**: F is strictly increasing in each argument
4. **Continuity**: F is continuous

The derivation proceeds in three stages:
1. Associativity + monotonicity + continuity → Additive representation Θ
2. Additive representation → Multiplicative representation via exp
3. Multiplicative representation → Product rule F(x,y) = x·y

## Mathematical Context

This solves the functional equation F(F(x,y),z) = F(x,F(y,z)) on [0,1].
The same equation appears in Knuth-Skilling's work on ordered semigroups.
Cox's "reparametrization" corresponds to K&S's "regraduation" concept.

## Main Results

1. `CoxFullAxioms`: Complete axiom package for Cox's theorem
2. `cox_implies_aczelHypothesis`: Cox axioms → Aczél hypothesis (associativity + monotonicity + continuity)
3. `multiplicativeRep_of_additiveRep`: Additive Θ → Multiplicative g = exp∘Θ
4. `productRule_of_multiplicativeRep`: Multiplicative rep → F(x,y) = x·y (up to reparametrization)
5. `cox_productRule`: Main theorem: Cox axioms → product rule

## References

- Cox, R.T. "The Algebra of Probable Inference" (1961), Chapter 3
- Jaynes, E.T. "Probability Theory: The Logic of Science" (2003), Chapter 2
- Van Horn, K.S. "Constructing a logic of plausible inference" (2003)
- Aczél, J. "Lectures on Functional Equations" (1966)
-/

namespace Mettapedia.ProbabilityTheory.Cox

open Real
open Filter
open Topology

/-!
## §1: Cox's Full Axioms

We package Cox's complete axiom set for the conjunction function F : (0,1] → (0,1] → (0,1].
Note: We work on (0,1] to avoid issues with F(0,·) = 0 complicating the functional equation.
-/

/-- Cox's full axiom set for the conjunction function on (0,1].

This is the complete package needed to derive F(x,y) = x·y.
Following Cox (1961), Chapter 3. -/
structure CoxFullAxioms where
  /-- The conjunction function F(x,y) = p(A∧B|C) when p(A|C) = x and p(B|A∧C) = y -/
  F : ℝ → ℝ → ℝ
  /-- F maps (0,1] × (0,1] to (0,1] -/
  F_range : ∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → 0 < F x y ∧ F x y ≤ 1
  /-- Associativity: F(F(x,y),z) = F(x,F(y,z)) -/
  F_assoc : ∀ x y z, F (F x y) z = F x (F y z)
  /-- Right identity: F(x,1) = x -/
  F_one_right : ∀ x, F x 1 = x
  /-- Left identity: F(1,y) = y -/
  F_one_left : ∀ y, F 1 y = y
  /-- Strictly increasing in left argument -/
  F_strictMono_left : ∀ z, 0 < z → z ≤ 1 → StrictMono fun x => F x z
  /-- Strictly increasing in right argument -/
  F_strictMono_right : ∀ z, 0 < z → z ≤ 1 → StrictMono fun y => F z y
  /-- Continuity -/
  F_continuous : Continuous (Function.uncurry F)

namespace CoxFullAxioms

variable (C : CoxFullAxioms)

/-!
## §2: Cox Axioms Imply Aczél Hypothesis

We show that Cox's axioms on (0,1] imply the Aczél hypothesis, which is the
key to solving the associativity functional equation.
-/

/-- Cox axioms imply the operation is associative. -/
theorem assoc : ∀ x y z : ℝ, C.F (C.F x y) z = C.F x (C.F y z) := C.F_assoc

/-- Cox axioms imply continuity of F as a function ℝ × ℝ → ℝ. -/
theorem continuous : Continuous (fun p : ℝ × ℝ => C.F p.1 p.2) := C.F_continuous

/-!
## §3: The Additive Representation

The key step in Cox's derivation is showing that an associative, monotone, continuous
operation admits an additive representation: there exists Θ such that

  Θ(F(x,y)) = Θ(x) + Θ(y)

This is the Aczél representation theorem. We state it as a hypothesis here and
connect to the K&S infrastructure.
-/

/-- The additive representation form for Cox's F.

If F satisfies Cox's axioms, then there exists a strictly increasing continuous
function Θ : (0,1] → ℝ such that Θ(F(x,y)) = Θ(x) + Θ(y).

This is Aczél's theorem applied to Cox's setting.

Note: We use StrictMonoOn (0, ∞) because the Cox operation is only defined on (0,1],
and the natural representation function (log) is only monotone on positive reals. -/
structure AdditiveRepresentation (C : CoxFullAxioms) where
  /-- The representation function Θ -/
  Θ : ℝ → ℝ
  /-- Θ is strictly increasing on (0,1]. (Cox values live in (0,1].) -/
  Θ_strictMonoOn : StrictMonoOn Θ (Set.Ioc 0 1)
  /-- Θ is continuous on (0,1]. -/
  Θ_continuousOn : ContinuousOn Θ (Set.Ioc 0 1)
  /-- Θ represents F additively: Θ(F(x,y)) = Θ(x) + Θ(y) for x, y ∈ (0,1] -/
  Θ_additive : ∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → Θ (C.F x y) = Θ x + Θ y

/-!
### Aczél's Theorem: Proof via Iteration

We prove the additive representation theorem using the iteration structure.
The key insight: F defines a semigroup structure, and log linearizes it.

**Proof Strategy**:

1. **Iteration**: Define iterate n a = F(a, F(a, ...)) n times, with iterate 0 a = 1.
2. **Additivity on grid**: F(iterate m a, iterate n a) = iterate (m+n) a by associativity.
3. **Logarithm construction**: For general F, construct Θ using the iteration structure
   and continuity to extend from the discrete grid.

For the standard product rule F(x,y) = x·y, we use Θ = log directly.
-/

/-- Iteration for Cox axioms: iterate 0 a = 1, iterate (n+1) a = F(a, iterate n a). -/
noncomputable def iterate (n : ℕ) (a : ℝ) : ℝ :=
  match n with
  | 0 => 1  -- Identity element for Cox is 1
  | n + 1 => C.F a (iterate n a)

/-- iterate 0 a = 1 -/
@[simp] lemma iterate_zero (a : ℝ) : C.iterate 0 a = 1 := rfl

/-- iterate 1 a = F(a, 1) = a -/
lemma iterate_one (a : ℝ) : C.iterate 1 a = a := C.F_one_right a

/-- iterate (n+1) a = F(a, iterate n a) -/
lemma iterate_succ (n : ℕ) (a : ℝ) : C.iterate (n + 1) a = C.F a (C.iterate n a) := rfl

/-- Iterates satisfy the additive property: F(iterate m a, iterate n a) = iterate (m+n) a -/
theorem iterate_add (a : ℝ) : ∀ m n, C.F (C.iterate m a) (C.iterate n a) = C.iterate (m + n) a := by
  intro m n
  induction m with
  | zero =>
    simp only [iterate_zero, Nat.zero_add]
    exact C.F_one_left _
  | succ m ih =>
    calc C.F (C.iterate (m + 1) a) (C.iterate n a)
        = C.F (C.F a (C.iterate m a)) (C.iterate n a) := rfl
      _ = C.F a (C.F (C.iterate m a) (C.iterate n a)) := C.F_assoc a _ _
      _ = C.F a (C.iterate (m + n) a) := by rw [ih]
      _ = C.iterate (m + n + 1) a := rfl
      _ = C.iterate (m + 1 + n) a := by ring_nf

/-- For a ∈ (0,1), iterates are in (0,1] and strictly decreasing. -/
lemma iterate_mem_Ioc (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < 1) :
    ∀ n, 0 < C.iterate n a ∧ C.iterate n a ≤ 1 := by
  intro n
  induction n with
  | zero => simp [iterate_zero]
  | succ n ih =>
    constructor
    · exact (C.F_range a (C.iterate n a) ha_pos (le_of_lt ha_lt) ih.1 ih.2).1
    · exact (C.F_range a (C.iterate n a) ha_pos (le_of_lt ha_lt) ih.1 ih.2).2

/-- Iterates are strictly decreasing: iterate (n+1) a < iterate n a for a ∈ (0,1). -/
lemma iterate_strictAnti (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < 1) :
    ∀ n, C.iterate (n + 1) a < C.iterate n a := by
  intro n
  induction n with
  | zero =>
    simp only [iterate_zero]
    rw [iterate_one]
    exact ha_lt
  | succ n ih =>
    -- iterate (n+2) a = F(a, iterate (n+1) a) < F(a, iterate n a) = iterate (n+1) a
    have h1 : C.iterate (n + 1) a < C.iterate n a := ih
    have h2 : C.iterate (n + 2) a = C.F a (C.iterate (n + 1) a) := rfl
    have h3 : C.iterate (n + 1) a = C.F a (C.iterate n a) := rfl
    rw [h2, h3]
    exact C.F_strictMono_right a ha_pos (le_of_lt ha_lt) h1

/-- F(a, x) < x for a < 1 and x ∈ (0, 1]. This is key to showing iterates decrease. -/
lemma F_lt_right (a x : ℝ) (_ha_pos : 0 < a) (ha_lt : a < 1) (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    C.F a x < x := by
  calc C.F a x < C.F 1 x := C.F_strictMono_left x hx_pos hx_le ha_lt
    _ = x := C.F_one_left x

/-- Iterates converge to 0 as n → ∞. -/
lemma iterate_tendsto_zero (a : ℝ) (ha_pos : 0 < a) (ha_lt : a < 1) :
    Filter.Tendsto (C.iterate · a) Filter.atTop (nhds 0) := by
  -- The sequence is strictly decreasing and bounded below by 0, so converges to infimum
  have hdecr : Antitone (C.iterate · a) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step h ih =>
      calc C.iterate (Nat.succ _) a
          ≤ C.iterate _ a := le_of_lt (C.iterate_strictAnti a ha_pos ha_lt _)
        _ ≤ C.iterate m a := ih
  have hbdd : BddBelow (Set.range (C.iterate · a)) := ⟨0, by
    intro x ⟨n, hn⟩; rw [← hn]; exact le_of_lt (C.iterate_mem_Ioc a ha_pos ha_lt n).1⟩
  -- Limit L exists
  set L := ⨅ n, C.iterate n a with hL_def
  have hconv := tendsto_atTop_ciInf hdecr hbdd
  -- Show L = 0 by contradiction: if L > 0, then F(a, L) < L contradicts being infimum
  by_contra hne
  -- hne : ¬(Filter.Tendsto (C.iterate · a) Filter.atTop (nhds 0))
  -- We know it converges to L, so this means L ≠ 0
  have hL_nonneg : L ≥ 0 := le_ciInf (fun n => le_of_lt (C.iterate_mem_Ioc a ha_pos ha_lt n).1)
  have hL_ne_zero : L ≠ 0 := by
    intro heq
    have hconv' : Filter.Tendsto (C.iterate · a) Filter.atTop (nhds 0) := by
      have : (⨅ x, C.iterate x a) = 0 := by rw [← hL_def]; exact heq
      rw [this] at hconv
      exact hconv
    exact hne hconv'
  have hL_pos : L > 0 := lt_of_le_of_ne hL_nonneg (Ne.symm hL_ne_zero)
  -- F(a, L) < L
  have hFL_lt_L : C.F a L < L := by
    have hL_le_one : L ≤ 1 := ciInf_le_of_le hbdd 0 (by simp [iterate_zero])
    exact C.F_lt_right a L ha_pos ha_lt hL_pos hL_le_one
  -- But iterate (n+1) a = F(a, iterate n a) → F(a, L) as n → ∞
  have hconv_succ : Filter.Tendsto (fun n => C.iterate (n + 1) a) Filter.atTop (nhds L) := by
    exact hconv.comp (Filter.tendsto_add_atTop_nat 1)
  -- Also iterate (n+1) a = F(a, iterate n a) → F(a, L) by continuity
  have hF_cont : Continuous (fun x => C.F a x) := by
    have : (fun x => C.F a x) = Function.uncurry C.F ∘ (fun x => (a, x)) := by ext; simp
    rw [this]
    apply Continuous.comp C.F_continuous
    exact continuous_prodMk.mpr ⟨continuous_const, continuous_id⟩
  have hconv_F : Filter.Tendsto (fun n => C.F a (C.iterate n a)) Filter.atTop (nhds (C.F a L)) := by
    exact (hF_cont.tendsto L).comp hconv
  -- So F(a, L) = L, contradicting F(a, L) < L
  have : C.F a L = L := tendsto_nhds_unique hconv_F hconv_succ
  linarith

/-- The diagonal function F(x,x) is continuous. -/
lemma diagonal_continuous : Continuous (fun x => C.F x x) := by
  have h : (fun x => C.F x x) = Function.uncurry C.F ∘ (fun x => (x, x)) := by ext; simp
  rw [h]
  exact C.F_continuous.comp (continuous_id.prodMk continuous_id)

/-- F(x,x) < x for x ∈ (0,1). This follows from F(x,x) < F(1,x) = x. -/
lemma diagonal_lt (x : ℝ) (hx_pos : 0 < x) (hx_lt : x < 1) : C.F x x < x := by
  calc C.F x x < C.F 1 x := C.F_strictMono_left x hx_pos (le_of_lt hx_lt) hx_lt
    _ = x := C.F_one_left x

/-- F(x,x) is strictly increasing in x on (0,1]. -/
lemma diagonal_strictMono : StrictMonoOn (fun x => C.F x x) (Set.Ioc 0 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioc] at hx hy
  -- F(x,x) < F(x,y) < F(y,y) using both monotonicity axioms
  have h1 : C.F x x < C.F x y := C.F_strictMono_right x hx.1 hx.2 hxy
  have h2 : C.F x y < C.F y y := C.F_strictMono_left y hy.1 hy.2 hxy
  exact lt_trans h1 h2

/-- F(x,x) tends to 0 as x → 0+. -/
lemma diagonal_tendsto_zero :
    Filter.Tendsto (fun x => C.F x x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- F(x,x) < x for x ∈ (0,1), and x → 0, so F(x,x) → 0 by squeeze
  have hF_lt : ∀ x, 0 < x → x < 1 → C.F x x < x := fun x hx hxlt => C.diagonal_lt x hx hxlt
  have hF_pos : ∀ x, 0 < x → x ≤ 1 → 0 < C.F x x := fun x hx hxle => (C.F_range x x hx hxle hx hxle).1
  -- Use squeeze: 0 ≤ F(x,x) ≤ x and x → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
  · -- Lower bound: constant 0 tends to 0
    exact tendsto_const_nhds
  · -- Upper bound: id tends to 0 from the right
    -- nhdsWithin 0 (Ioi 0) ≤ nhds 0, and id : nhds 0 → nhds 0
    exact Filter.Tendsto.mono_left (f := id) Filter.tendsto_id nhdsWithin_le_nhds
  · -- Eventually 0 ≤ F(x,x) for x ∈ (0,1)
    -- We work on Ioo 0 1 where F is well-defined
    have h1_mem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Ioo (-1) 1, isOpen_Ioo, ?_, ?_⟩
      · simp only [Set.mem_Ioo]; norm_num
      · intro x hx
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi] at hx
        exact ⟨hx.2, hx.1.2⟩
    filter_upwards [h1_mem] with x hx
    simp only [Set.mem_Ioo] at hx
    exact le_of_lt (hF_pos x hx.1 (le_of_lt hx.2))
  · -- Eventually F(x,x) ≤ x for x ∈ (0,1)
    have h1_mem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Ioo (-1) 1, isOpen_Ioo, ?_, ?_⟩
      · simp only [Set.mem_Ioo]; norm_num
      · intro x hx
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi] at hx
        exact ⟨hx.2, hx.1.2⟩
    filter_upwards [h1_mem] with x hx
    simp only [Set.mem_Ioo] at hx
    exact le_of_lt (hF_lt x hx.1 hx.2)

/-- **Square Root Lemma**: For any b ∈ (0,1), there exists y ∈ (0,1) such that F(y,y) = b.

This is the key lemma for extending Θ to dyadic rationals. -/
lemma exists_sqrt (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    ∃ y, 0 < y ∧ y < 1 ∧ C.F y y = b := by
  -- F(x,x) is continuous, F(1,1) = 1, F(x,x) → 0 as x → 0+
  -- By IVT, for any b ∈ (0,1), ∃ y ∈ (0,1) with F(y,y) = b
  have hF_one : C.F 1 1 = 1 := C.F_one_right 1
  have hcont : Continuous (fun x => C.F x x) := C.diagonal_continuous
  -- Step 1: Find ε > 0 such that F(ε, ε) < b
  -- F(x,x) → 0 as x → 0+, so there exists x with 0 < x and F(x,x) < b
  have htendsto := C.diagonal_tendsto_zero
  -- Use Metric.tendsto_nhds to extract the ball condition
  rw [Metric.tendsto_nhds] at htendsto
  -- Get δ > 0 such that 0 < x < δ implies |F(x,x) - 0| < b
  have hev := htendsto b hb_pos
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ_pos, hδ⟩ := hev
  -- Take ε = min (δ/2) (1/2)
  set ε := min (δ/2) (1/2) with hε_def
  have hε_pos : 0 < ε := by positivity
  have hε_lt_δ : ε < δ := calc ε ≤ δ/2 := min_le_left _ _
    _ < δ := by linarith
  have hε_le_half : ε ≤ 1/2 := min_le_right _ _
  have hε_lt_one : ε < 1 := lt_of_le_of_lt hε_le_half (by norm_num)
  -- ε satisfies dist ε 0 < δ
  have hε_dist : dist ε 0 < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hε_pos]
    exact hε_lt_δ
  -- So by hδ, since ε ∈ Ioi 0, we have dist (F ε ε) 0 < b
  have hFε_dist : dist (C.F ε ε) 0 < b := hδ hε_dist hε_pos
  have hFε_pos : 0 < C.F ε ε := (C.F_range ε ε hε_pos (le_of_lt hε_lt_one) hε_pos (le_of_lt hε_lt_one)).1
  have hFε_lt_b : C.F ε ε < b := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hFε_pos] at hFε_dist
    exact hFε_dist
  -- Step 2: Apply IVT on [ε, 1]
  -- F(ε, ε) < b < 1 = F(1, 1), so ∃ y ∈ (ε, 1) with F(y, y) = b
  have hcont_on : ContinuousOn (fun x => C.F x x) (Set.Icc ε 1) := hcont.continuousOn
  have hεle1 : ε ≤ 1 := le_of_lt hε_lt_one
  have hb_between : b ∈ Set.Ioo (C.F ε ε) (C.F 1 1) := by
    simp only [Set.mem_Ioo, hF_one]
    exact ⟨hFε_lt_b, hb_lt⟩
  -- IVT: intermediate_value_Ioo gives y ∈ (ε, 1) with F(y,y) = b
  obtain ⟨y, hy_mem, hy_eq⟩ := intermediate_value_Ioo hεle1 hcont_on hb_between
  use y
  simp only [Set.mem_Ioo] at hy_mem
  exact ⟨lt_trans hε_pos hy_mem.1, hy_mem.2, hy_eq⟩

/-- **Unique Square Root**: For any b ∈ (0,1), there exists a UNIQUE y ∈ (0,1) such that F(y,y) = b. -/
lemma exists_unique_sqrt (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    ∃! y, 0 < y ∧ y < 1 ∧ C.F y y = b := by
  obtain ⟨y, hy_pos, hy_lt, hy_eq⟩ := C.exists_sqrt b hb_pos hb_lt
  use y
  refine ⟨⟨hy_pos, hy_lt, hy_eq⟩, ?_⟩
  intro z ⟨hz_pos, hz_lt, hz_eq⟩
  -- F(y,y) = b = F(z,z), and F is strictly increasing on (0,1], so y = z
  by_contra hne
  -- Ne.lt_or_gt hne gives: z < y ∨ y < z (since hne : ¬z = y)
  rcases Ne.lt_or_gt hne with h | h
  · -- z < y, so F(z,z) < F(y,y), contradiction
    have hlt : C.F z z < C.F y y := C.diagonal_strictMono ⟨hz_pos, le_of_lt hz_lt⟩ ⟨hy_pos, le_of_lt hy_lt⟩ h
    rw [hz_eq, hy_eq] at hlt
    exact lt_irrefl b hlt
  · -- y < z, so F(y,y) < F(z,z), contradiction
    have hlt : C.F y y < C.F z z := C.diagonal_strictMono ⟨hy_pos, le_of_lt hy_lt⟩ ⟨hz_pos, le_of_lt hz_lt⟩ h
    rw [hy_eq, hz_eq] at hlt
    exact lt_irrefl b hlt

/-- The unique square root function: sqrt_F b is the unique y ∈ (0,1) with F(y,y) = b. -/
noncomputable def sqrt_F (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) : ℝ :=
  (C.exists_unique_sqrt b hb_pos hb_lt).choose

lemma sqrt_F_spec (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    0 < C.sqrt_F b hb_pos hb_lt ∧
    C.sqrt_F b hb_pos hb_lt < 1 ∧
    C.F (C.sqrt_F b hb_pos hb_lt) (C.sqrt_F b hb_pos hb_lt) = b :=
  (C.exists_unique_sqrt b hb_pos hb_lt).choose_spec.1

/-!
### Helper Lemmas for Iteration

We use the existing `iterate` function which defines x^n = F(x, F(x, ...F(x, 1)...))
-/

/-- F preserves positivity. -/
lemma F_pos (x y : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) (hy_pos : 0 < y) (hy_le : y ≤ 1) :
    0 < C.F x y :=
  (C.F_range x y hx_pos hx_le hy_pos hy_le).1

/-- F is monotone in the right argument. -/
lemma F_mono_right (x : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) {y z : ℝ}
    (_hy_pos : 0 < y) (_hy_le : y ≤ 1) (_hz_pos : 0 < z) (_hz_le : z ≤ 1) (h : y ≤ z) :
    C.F x y ≤ C.F x z := by
  by_cases heq : y = z
  · rw [heq]
  · have : y < z := lt_of_le_of_ne h heq
    exact le_of_lt ((C.F_strictMono_right x hx_pos hx_le) this)

/-- iterate at 1 gives 1. -/
lemma iterate_at_one (n : ℕ) : C.iterate n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc C.iterate (n + 1) 1 = C.F 1 (C.iterate n 1) := rfl
      _ = C.F 1 1 := by rw [ih]
      _ = 1 := C.F_one_right 1

/-- iterate maps (0,1] to (0,1]. Uses the existing iterate_mem_Ioc for strict inequality case. -/
lemma iterate_le_one (n : ℕ) (x : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    C.iterate n x ≤ 1 := by
  by_cases hx_lt : x < 1
  · exact (C.iterate_mem_Ioc x hx_pos hx_lt n).2
  · push_neg at hx_lt
    have hx_eq : x = 1 := le_antisymm hx_le hx_lt
    rw [hx_eq, C.iterate_at_one]

/-- iterate 2 gives the diagonal F(x,x). -/
lemma iterate_two (x : ℝ) : C.iterate 2 x = C.F x x := by
  calc C.iterate 2 x = C.F x (C.iterate 1 x) := rfl
    _ = C.F x x := by rw [iterate_one]

/-- iterate is continuous. -/
lemma iterate_continuous (n : ℕ) : Continuous (C.iterate n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have h : C.iterate (n + 1) = (fun x => C.F x (C.iterate n x)) := by
      ext x; rfl
    rw [h]
    have hcomp : (fun x => C.F x (C.iterate n x)) =
                 Function.uncurry C.F ∘ (fun x => (x, C.iterate n x)) := by ext; simp
    rw [hcomp]
    exact C.F_continuous.comp (continuous_id.prodMk ih)

/-- iterate is strictly monotone on (0,1] for n ≥ 1. -/
lemma iterate_strictMono_on (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (C.iterate n) (Set.Ioc 0 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro x hx y hy hxy
    cases n with
    | zero =>
      rw [iterate_one, iterate_one]
      exact hxy
    | succ n =>
      -- Need: F(x, iterate (n+1) x) < F(y, iterate (n+1) y)
      have hn1 : 1 ≤ n + 1 := by omega
      have hiter_x_lt_y : C.iterate (n+1) x < C.iterate (n+1) y := ih hn1 hx hy hxy
      -- Need y < 1 to use iterate_mem_Ioc, or handle y = 1 case
      by_cases hy_eq : y = 1
      · -- y = 1 case: show F(x, iter (n+1) x) < F(1, iter (n+1) 1)
        have hx_lt : x < 1 := by rw [hy_eq] at hxy; exact hxy
        have hiter_x_lt : C.iterate (n+1) x < C.iterate (n+1) 1 := by rw [← hy_eq]; exact hiter_x_lt_y
        rw [C.iterate_at_one] at hiter_x_lt
        have hiter_x_pos : 0 < C.iterate (n+1) x := (C.iterate_mem_Ioc x hx.1 hx_lt (n+1)).1
        have hiter_x_le : C.iterate (n+1) x ≤ 1 := C.iterate_le_one (n+1) x hx.1 hx.2
        -- F(x, iter_x) < F(x, 1) = x < 1 = F(1, 1) = F(y, iter y)
        calc C.F x (C.iterate (n+1) x)
            < C.F x 1 := C.F_strictMono_right x hx.1 hx.2 hiter_x_lt
          _ = x := C.F_one_right x
          _ < 1 := hx_lt
          _ = C.F 1 1 := (C.F_one_right 1).symm
          _ = C.F y (C.iterate (n+1) y) := by rw [hy_eq, C.iterate_at_one]
      · -- y < 1 case
        have hy_lt : y < 1 := lt_of_le_of_ne hy.2 hy_eq
        calc C.F x (C.iterate (n+1) x)
            < C.F x (C.iterate (n+1) y) := C.F_strictMono_right x hx.1 hx.2 hiter_x_lt_y
          _ < C.F y (C.iterate (n+1) y) := by
              have hmem := C.iterate_mem_Ioc y hy.1 hy_lt (n+1)
              exact C.F_strictMono_left (C.iterate (n+1) y) hmem.1 hmem.2 hxy

/-!
## §3.5: nth Roots Following Ling (1965)

Following Ling's Section 4, we define nth roots and prove the key lemmas needed
for the representation theorem. The main construction:

**Notation** (Ling's convention, adapted):
- sₙ(x) = x^n = iterate n x (n-fold application of F)
- rₙ(x) = min{y : sₙ(y) = x} (nth root)
- g*(m/n) = sₘ(rₙ(c)) for fixed base point c

**Key lemmas from Ling Section 4**:
- Lemma 1: {x^n} is nondecreasing (for x > identity)
- Lemma 2: Archimedean property
- Lemma 3: lim x^n = annihilator
- Lemma 4-5: Endpoint properties
- Lemma 6-7: Order properties
- Lemma 8-14: nth root properties
-/

/-- For each n ≥ 2 and b ∈ (0,1), there exists y ∈ (0,1) with iterate n y = b.
This is existence of nth roots by IVT. -/
lemma exists_nth_root (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    ∃ y, 0 < y ∧ y < 1 ∧ C.iterate n y = b := by
  -- iterate n 1 = 1 > b, and iterate n tends to 0 as x → 0+
  -- By IVT, there exists y with iterate n y = b
  have h_at_1 : C.iterate n 1 = 1 := C.iterate_at_one n
  -- Find ε > 0 with iterate n ε < b (using diagonal tends to 0)
  have h_small : ∃ ε, 0 < ε ∧ ε < 1 ∧ C.iterate n ε < b := by
    -- For n ≥ 2: iterate n ε ≤ iterate 2 ε = F(ε, ε), and F(ε,ε) → 0 as ε → 0+
    have h_diag_tends := C.diagonal_tendsto_zero
    -- Use Metric.tendsto_nhds to get δ-ball condition
    rw [Metric.tendsto_nhds] at h_diag_tends
    have hev := h_diag_tends b hb_pos
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ_pos, hδ⟩ := hev
    use min (δ/2) (1/2)
    refine ⟨by positivity, by linarith [min_le_right (δ/2) (1/2)], ?_⟩
    have hε_pos : 0 < min (δ/2) (1/2) := by positivity
    have hε_lt : min (δ/2) (1/2) < 1 := by linarith [min_le_right (δ/2) (1/2)]
    -- iterate n ε ≤ F(ε, ε) for n ≥ 2
    have h_iter_le_diag : C.iterate n (min (δ/2) (1/2)) ≤ C.F (min (δ/2) (1/2)) (min (δ/2) (1/2)) := by
      have h2 : C.iterate 2 (min (δ/2) (1/2)) = C.F (min (δ/2) (1/2)) (min (δ/2) (1/2)) := C.iterate_two _
      cases n with
      | zero => omega
      | succ n' =>
        cases n' with
        | zero => omega
        | succ n'' =>
          -- For n ≥ 2, iterate is decreasing, so iterate n ≤ iterate 2
          have hanti : ∀ k, C.iterate (k + 1) (min (δ/2) (1/2)) ≤
                           C.iterate k (min (δ/2) (1/2)) := by
            intro k
            exact le_of_lt (C.iterate_strictAnti (min (δ/2) (1/2)) hε_pos hε_lt k)
          -- By induction: iterate (n''+2) ≤ iterate 2
          have : ∀ m, C.iterate (m + 2) (min (δ/2) (1/2)) ≤ C.iterate 2 (min (δ/2) (1/2)) := by
            intro m
            induction m with
            | zero => exact le_refl _
            | succ m ihm =>
              calc C.iterate (m + 1 + 2) (min (δ/2) (1/2))
                  ≤ C.iterate (m + 2) (min (δ/2) (1/2)) := hanti (m + 2)
                _ ≤ C.iterate 2 (min (δ/2) (1/2)) := ihm
          rw [← h2]
          exact this n''
    -- F(ε, ε) < b by the tendsto property
    have hdiag_lt : C.F (min (δ/2) (1/2)) (min (δ/2) (1/2)) < b := by
      have hdist : dist (min (δ/2) (1/2)) 0 < δ := by
        simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hε_pos]
        calc min (δ/2) (1/2) ≤ δ/2 := min_le_left _ _
          _ < δ := by linarith
      have hε_in : min (δ/2) (1/2) ∈ Set.Ioi (0:ℝ) := hε_pos
      have := hδ hdist hε_in
      simp only [dist_zero_right, Real.norm_eq_abs] at this
      have hFpos : 0 < C.F (min (δ/2) (1/2)) (min (δ/2) (1/2)) := by
        exact (C.F_range _ _ hε_pos (le_of_lt hε_lt) hε_pos (le_of_lt hε_lt)).1
      rwa [abs_of_pos hFpos] at this
    exact lt_of_le_of_lt h_iter_le_diag hdiag_lt
  obtain ⟨ε, hε_pos, hε_lt, hiter_ε⟩ := h_small
  -- Now apply IVT on [ε, 1]
  have hεle1 : ε ≤ 1 := le_of_lt hε_lt
  have hcont : ContinuousOn (C.iterate n) (Set.Icc ε 1) := (C.iterate_continuous n).continuousOn
  have hb_mem : b ∈ Set.Ioo (C.iterate n ε) (C.iterate n 1) := by
    simp only [Set.mem_Ioo, h_at_1]
    exact ⟨hiter_ε, hb_lt⟩
  obtain ⟨y, hy_mem, hy_eq⟩ := intermediate_value_Ioo hεle1 hcont hb_mem
  exact ⟨y, lt_of_lt_of_le hε_pos (le_of_lt hy_mem.1), hy_mem.2, hy_eq⟩

/-- nth roots are unique by strict monotonicity. -/
lemma exists_unique_nth_root (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    ∃! y, 0 < y ∧ y < 1 ∧ C.iterate n y = b := by
  obtain ⟨y, hy_pos, hy_lt, hy_eq⟩ := C.exists_nth_root n hn b hb_pos hb_lt
  refine ⟨y, ⟨hy_pos, hy_lt, hy_eq⟩, ?_⟩
  intro z ⟨hz_pos, hz_lt, hz_eq⟩
  by_contra hne
  rcases Ne.lt_or_gt hne with h | h
  · -- z < y, so iterate n z < iterate n y, contradiction
    have hlt : C.iterate n z < C.iterate n y := by
      apply C.iterate_strictMono_on n (by omega)
      · exact ⟨hz_pos, le_of_lt hz_lt⟩
      · exact ⟨hy_pos, le_of_lt hy_lt⟩
      · exact h
    rw [hz_eq, hy_eq] at hlt
    exact lt_irrefl b hlt
  · -- y < z, so iterate n y < iterate n z, contradiction
    have hlt : C.iterate n y < C.iterate n z := by
      apply C.iterate_strictMono_on n (by omega)
      · exact ⟨hy_pos, le_of_lt hy_lt⟩
      · exact ⟨hz_pos, le_of_lt hz_lt⟩
      · exact h
    rw [hy_eq, hz_eq] at hlt
    exact lt_irrefl b hlt

/-- The unique nth root function rₙ(b) = min{y : yⁿ = b}.
Following Ling (1965), Definition 4.15. -/
noncomputable def nth_root (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) : ℝ :=
  (C.exists_unique_nth_root n hn b hb_pos hb_lt).choose

/-- The nth root satisfies the defining property. -/
lemma nth_root_spec (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    0 < C.nth_root n hn b hb_pos hb_lt ∧
    C.nth_root n hn b hb_pos hb_lt < 1 ∧
    C.iterate n (C.nth_root n hn b hb_pos hb_lt) = b :=
  (C.exists_unique_nth_root n hn b hb_pos hb_lt).choose_spec.1

/-- **Ling's Lemma 12**: The nth root is strictly increasing in n.
For c ∈ (0,1): r_n(c) < r_{n+1}(c) for all n ≥ 2.

Proof: We have iterate n (r_n) = c and iterate (n+1) (r_{n+1}) = c.
Since r_n < 1, we get iterate (n+1) (r_n) = F(r_n, iterate n r_n) = F(r_n, c) < F(1, c) = c.
So iterate (n+1) r_n < c = iterate (n+1) r_{n+1}.
By strict monotonicity of iterate (n+1), we get r_n < r_{n+1}. -/
lemma nth_root_lt_succ (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    C.nth_root n hn b hb_pos hb_lt < C.nth_root (n + 1) (by omega : 2 ≤ n + 1) b hb_pos hb_lt := by
  -- Get properties of both roots
  have hn1 : 2 ≤ n + 1 := by omega
  set r_n := C.nth_root n hn b hb_pos hb_lt with hr_n
  set r_n1 := C.nth_root (n + 1) hn1 b hb_pos hb_lt with hr_n1
  have hr_n_spec := C.nth_root_spec n hn b hb_pos hb_lt
  have hr_n1_spec := C.nth_root_spec (n + 1) hn1 b hb_pos hb_lt
  -- r_n ∈ (0, 1) and iterate n r_n = b
  have hr_n_pos : 0 < r_n := hr_n_spec.1
  have hr_n_lt : r_n < 1 := hr_n_spec.2.1
  have hr_n_eq : C.iterate n r_n = b := hr_n_spec.2.2
  -- r_{n+1} ∈ (0, 1) and iterate (n+1) r_{n+1} = b
  have hr_n1_pos : 0 < r_n1 := hr_n1_spec.1
  have hr_n1_lt : r_n1 < 1 := hr_n1_spec.2.1
  have hr_n1_eq : C.iterate (n + 1) r_n1 = b := hr_n1_spec.2.2
  -- Key: iterate (n+1) r_n < b
  have h_iter_rn_lt : C.iterate (n + 1) r_n < b := by
    calc C.iterate (n + 1) r_n
        = C.F r_n (C.iterate n r_n) := rfl
      _ = C.F r_n b := by rw [hr_n_eq]
      _ < C.F 1 b := C.F_strictMono_left b hb_pos (le_of_lt hb_lt) hr_n_lt
      _ = b := C.F_one_left b
  -- iterate (n+1) r_n < b = iterate (n+1) r_{n+1}
  -- By strict monotonicity of iterate (n+1), r_n < r_{n+1}
  have h_mono := C.iterate_strictMono_on (n + 1) (by omega : 1 ≤ n + 1)
  -- Both roots are in (0, 1]
  have hr_n_mem : r_n ∈ Set.Ioc 0 1 := ⟨hr_n_pos, le_of_lt hr_n_lt⟩
  have hr_n1_mem : r_n1 ∈ Set.Ioc 0 1 := ⟨hr_n1_pos, le_of_lt hr_n1_lt⟩
  -- Use strict monotonicity: iterate (n+1) r_n < iterate (n+1) r_{n+1} implies r_n < r_{n+1}
  -- (by contrapositive)
  by_contra h_not_lt
  push_neg at h_not_lt
  rcases le_or_gt r_n1 r_n with h_le | h_gt
  · -- r_{n+1} ≤ r_n case
    rcases lt_or_eq_of_le h_le with h_strict | h_eq
    · -- r_{n+1} < r_n leads to contradiction
      have h_iter_lt := h_mono hr_n1_mem hr_n_mem h_strict
      rw [hr_n1_eq] at h_iter_lt
      linarith
    · -- r_n = r_{n+1} leads to contradiction (iterate (n+1) r_n < b = iterate (n+1) r_n1)
      have h_eq' : C.iterate (n + 1) r_n = C.iterate (n + 1) r_n1 := by rw [h_eq]
      rw [hr_n1_eq] at h_eq'
      linarith
  · -- r_n < r_{n+1}: this IS what we want to prove, contradiction with h_not_lt
    linarith

/-- **Ling's Lemma 13**: The nth root converges to 1 as n → ∞.
For any c ∈ (0,1): lim_{n→∞} r_n(c) = 1.

Proof: The sequence {r_n(c)} is increasing (by Lemma 12) and bounded above by 1,
so it converges to some limit L ≤ 1. If L < 1, then:
- Choose K such that iterate K (L) < b/2 (possible by iterate_tendsto_zero)
- For large n, r_n is close to L, so iterate K (r_n) < b by continuity
- But iterate n (r_n) = b and iterate n (r_n) < iterate K (r_n) for n > K
  (iterates are decreasing in n for fixed argument < 1)
- This gives b < b, contradiction. Hence L = 1. -/
lemma nth_root_tendsto_one (b : ℝ) (hb_pos : 0 < b) (hb_lt : b < 1) :
    Filter.Tendsto (fun n => if hn : 2 ≤ n then C.nth_root n hn b hb_pos hb_lt else 0)
                   Filter.atTop (nhds 1) := by
  -- Define the sequence
  let r : ℕ → ℝ := fun n => if hn : 2 ≤ n then C.nth_root n hn b hb_pos hb_lt else 0
  -- r_n < 1 and r_n > 0 for all n ≥ 2
  have hr_lt_one : ∀ n, 2 ≤ n → r n < 1 := fun n hn => by
    simp only [r, dif_pos hn]; exact (C.nth_root_spec n hn b hb_pos hb_lt).2.1
  have hr_pos : ∀ n, 2 ≤ n → 0 < r n := fun n hn => by
    simp only [r, dif_pos hn]; exact (C.nth_root_spec n hn b hb_pos hb_lt).1
  -- iterate n (r_n) = b for all n ≥ 2
  have hr_eq : ∀ n, 2 ≤ n → C.iterate n (r n) = b := fun n hn => by
    simp only [r, dif_pos hn]; exact (C.nth_root_spec n hn b hb_pos hb_lt).2.2
  -- Sequence is increasing (Lemma 12)
  have hr_increasing : ∀ n, 2 ≤ n → r n < r (n + 1) := fun n hn => by
    have hn1 : 2 ≤ n + 1 := by omega
    simp only [r, dif_pos hn, dif_pos hn1]
    exact C.nth_root_lt_succ n hn b hb_pos hb_lt
  -- Bounded monotone sequence converges
  have hbdd : BddAbove (Set.range (fun n => r (n + 2))) := ⟨1, by
    intro x ⟨n, hn⟩; rw [← hn]; exact le_of_lt (hr_lt_one (n + 2) (by omega))⟩
  have hmono : Monotone (fun n => r (n + 2)) := fun m n hmn => by
    -- Show r (m + 2) ≤ r (n + 2) when m ≤ n by induction on n - m
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    subst hd
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : r (m + 2) ≤ r ((m + d) + 2) := ih (Nat.le_add_right m d)
      calc r (m + 2) ≤ r ((m + d) + 2) := h1
        _ ≤ r ((m + d) + 3) := le_of_lt (hr_increasing ((m + d) + 2) (by omega))
  -- Get the limit L
  have hL := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, r (n + 2) with L_def
  have hL_le_one : L ≤ 1 := ciSup_le fun n => le_of_lt (hr_lt_one (n + 2) (by omega))
  have hL_ge_r2 : L ≥ r 2 := le_ciSup_of_le hbdd 0 (le_refl (r (0 + 2)))
  have hL_pos : 0 < L := lt_of_lt_of_le (hr_pos 2 (by omega)) hL_ge_r2
  -- We prove L = 1, then derive the goal
  suffices hL_eq_one : L = 1 by
    -- The shifted sequence r(n+2) → L = 1
    -- We need to show the original r → 1
    rw [hL_eq_one] at hL
    -- For n ≥ 2: r n = (fun k => r (k + 2)) (n - 2)
    -- Use composition with the shifting function
    have hsub_tendsto : Filter.Tendsto (fun n => n - 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.sub_le_sub_right h 2)
        (fun b => ⟨b + 2, by omega⟩)
    apply (hL.comp hsub_tendsto).congr'
    -- Eventually r n = r ((n - 2) + 2)
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    simp only [Function.comp_apply, Nat.sub_add_cancel hn, r, dif_pos hn]
  -- Show L = 1 by contradiction
  by_contra hL_ne_one
  have hL_lt_one : L < 1 := lt_of_le_of_ne hL_le_one hL_ne_one
  -- Key: For L < 1, iterate K (L) can be made < b/2 for large K
  have h_iter_L_tends : Filter.Tendsto (C.iterate · L) Filter.atTop (nhds 0) :=
    C.iterate_tendsto_zero L hL_pos hL_lt_one
  -- Get K such that iterate K (L) < b/2
  rw [Metric.tendsto_atTop] at h_iter_L_tends
  obtain ⟨K, hK⟩ := h_iter_L_tends (b/2) (by linarith)
  -- For large n, r_n is close to L, so iterate K (r_n) is close to iterate K (L)
  -- Use continuity of iterate K
  have hcont_K : Continuous (C.iterate K) := C.iterate_continuous K
  have hcont_K_at_L : ContinuousAt (C.iterate K) L := hcont_K.continuousAt
  rw [Metric.continuousAt_iff] at hcont_K_at_L
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont_K_at_L (b/4) (by linarith)
  -- Get N such that |r_{N+2} - L| < δ
  have hL_tendsto : Filter.Tendsto (fun n => r (n + 2)) Filter.atTop (nhds L) := hL
  rw [Metric.tendsto_atTop] at hL_tendsto
  obtain ⟨N, hN⟩ := hL_tendsto δ hδ_pos
  -- Take n = max(N + 2, K + 3) so n ≥ 2, n > K, and r_n is close to L
  let n := max (N + 2) (K + 3)
  have hn_ge_2 : 2 ≤ n := Nat.le_trans (by omega : 2 ≤ N + 2) (Nat.le_max_left (N + 2) (K + 3))
  have hn_gt_K : K < n := Nat.lt_of_lt_of_le (by omega : K < K + 3) (Nat.le_max_right (N + 2) (K + 3))
  have hN_le : N ≤ n - 2 := Nat.le_sub_of_add_le (Nat.le_max_left (N + 2) (K + 3))
  -- |r_n - L| < δ
  have hr_n_close : dist (r n) L < δ := by
    have h := hN (n - 2) hN_le
    have h_simp : n - 2 + 2 = n := Nat.sub_add_cancel hn_ge_2
    simp only [h_simp] at h
    exact h
  -- |iterate K (r_n) - iterate K (L)| < b/4
  have h_iter_close : dist (C.iterate K (r n)) (C.iterate K L) < b / 4 := hδ hr_n_close
  -- iterate K (L) < b/2 (since |iterate K (L) - 0| < b/2)
  have h_iter_L_small : C.iterate K L < b / 2 := by
    have hK' := hK K (le_refl K)
    simp only [dist_zero_right, Real.norm_eq_abs] at hK'
    have h_iter_pos : 0 < C.iterate K L := (C.iterate_mem_Ioc L hL_pos hL_lt_one K).1
    rwa [abs_of_pos h_iter_pos] at hK'
  -- iterate K (r_n) < b/2 + b/4 = 3b/4
  have h_iter_rn_small : C.iterate K (r n) < 3 * b / 4 := by
    have h1 : |C.iterate K (r n) - C.iterate K L| < b / 4 := by
      rw [Real.dist_eq] at h_iter_close; exact h_iter_close
    have h2 : C.iterate K (r n) < C.iterate K L + b / 4 := by linarith [abs_sub_lt_iff.mp h1]
    linarith
  -- iterate n (r_n) < iterate K (r_n) for n > K (iterates decrease)
  have h_iter_decreasing : C.iterate n (r n) < C.iterate K (r n) := by
    have hr_n_pos : 0 < r n := hr_pos n hn_ge_2
    have hr_n_lt : r n < 1 := hr_lt_one n hn_ge_2
    -- iterate is strictly anti in first argument for fixed second argument < 1
    have hanti : ∀ m, C.iterate (m + 1) (r n) < C.iterate m (r n) :=
      C.iterate_strictAnti (r n) hr_n_pos hr_n_lt
    -- By induction: iterate n (r n) ≤ iterate (K+1) (r n) < iterate K (r n) when n > K
    have h_le : ∀ m, m ≤ n - (K + 1) → C.iterate n (r n) ≤ C.iterate (n - m) (r n) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        calc C.iterate n (r n)
            ≤ C.iterate (n - m) (r n) := ih (by omega)
          _ ≤ C.iterate (n - m - 1) (r n) := by
              have hmk : n - m - 1 + 1 = n - m := by omega
              rw [← hmk]
              exact le_of_lt (hanti (n - m - 1))
    have h := h_le (n - (K + 1)) (by omega)
    have h_eq : n - (n - (K + 1)) = K + 1 := by omega
    rw [h_eq] at h
    exact lt_of_le_of_lt h (hanti K)
  -- But iterate n (r_n) = b, so b < 3b/4
  have h_eq_b : C.iterate n (r n) = b := hr_eq n hn_ge_2
  rw [h_eq_b] at h_iter_decreasing
  linarith

/-!
### Aczél's Construction Following Ling (1965)

Following Ling's Section 4 (pages 198-203), we prove the representation theorem
using an elementary construction:

1. **Base point**: Fix c ∈ (0,1)
2. **Define g***: g*(m/n) = sₘ(rₙ(c)) = iterate m (nth_root n c)
3. **Key lemma**: sₘ rₙ = s_{im} r_{in} ensures well-definedness
4. **Four propositions**: g* is nondecreasing, strictly monotone, additive, continuous
5. **Extension**: Extend g* to reals by continuity

This provides a constructive proof of Aczél's theorem.
-/

/-- Helper: 2 ≤ i * n when 1 ≤ i and 2 ≤ n. -/
private lemma le_two_i_mul_n (i n : ℕ) (hi : 1 ≤ i) (hn : 2 ≤ n) : 2 ≤ i * n := by
  calc 2 ≤ n := hn
    _ = 1 * n := (Nat.one_mul n).symm
    _ ≤ i * n := Nat.mul_le_mul_right n hi

/-- Power of power: iterate n (iterate i a) = iterate (n * i) a.
This is the fundamental property (a^i)^n = a^{in} for the semigroup operation. -/
lemma iterate_mul (a : ℝ) (n i : ℕ) : C.iterate n (C.iterate i a) = C.iterate (n * i) a := by
  induction n with
  | zero => simp [iterate_zero]
  | succ n ih =>
    calc C.iterate (n + 1) (C.iterate i a)
        = C.F (C.iterate i a) (C.iterate n (C.iterate i a)) := rfl
      _ = C.F (C.iterate i a) (C.iterate (n * i) a) := by rw [ih]
      _ = C.iterate (i + n * i) a := C.iterate_add a i (n * i)
      _ = C.iterate ((n + 1) * i) a := by ring_nf

/-- The ith iterate of the (i*n)th root equals the nth root.
This is the key sub-lemma for Lemma 14. -/
lemma iterate_i_nth_root_eq (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) :
    C.iterate i (C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt) =
    C.nth_root n hn c hc_pos hc_lt := by
  -- Let r_{in} = nth_root (i*n) c and r_n = nth_root n c
  -- We show iterate i r_{in} = r_n by uniqueness of nth roots
  set r_in := C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt with hr_in
  set r_n := C.nth_root n hn c hc_pos hc_lt with hr_n
  set y := C.iterate i r_in with hy_def
  -- r_in satisfies: iterate (i*n) r_in = c
  have hr_in_spec := C.nth_root_spec (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt
  -- r_n satisfies: iterate n r_n = c
  have hr_n_spec := C.nth_root_spec n hn c hc_pos hc_lt
  -- y = iterate i r_in is positive and < 1
  have hy_pos : 0 < y := (C.iterate_mem_Ioc r_in hr_in_spec.1 hr_in_spec.2.1 i).1
  -- For i ≥ 1 and r_in < 1: iterate i r_in ≤ iterate 1 r_in = r_in < 1
  have hy_lt' : y < 1 := by
    cases Nat.lt_or_eq_of_le hi with
    | inl h_gt =>
      -- i ≥ 2, so iterate i r_in < iterate 1 r_in = r_in < 1
      have h_anti : Antitone (C.iterate · r_in) := by
        intro m n hmn
        induction hmn with
        | refl => exact le_refl _
        | step _ ih =>
          exact le_trans (le_of_lt (C.iterate_strictAnti r_in hr_in_spec.1 hr_in_spec.2.1 _)) ih
      calc y = C.iterate i r_in := rfl
        _ ≤ C.iterate 1 r_in := h_anti (Nat.one_le_of_lt h_gt)
        _ = r_in := C.iterate_one r_in
        _ < 1 := hr_in_spec.2.1
    | inr h_eq =>
      -- i = 1, so y = iterate 1 r_in = r_in < 1
      calc y = C.iterate i r_in := rfl
        _ = C.iterate 1 r_in := by rw [h_eq]
        _ = r_in := C.iterate_one r_in
        _ < 1 := hr_in_spec.2.1
  -- iterate n y = iterate n (iterate i r_in) = iterate (n * i) r_in = iterate (i * n) r_in = c
  have hy_spec : C.iterate n y = c := by
    calc C.iterate n y
        = C.iterate n (C.iterate i r_in) := rfl
      _ = C.iterate (n * i) r_in := C.iterate_mul r_in n i
      _ = C.iterate (i * n) r_in := by ring_nf
      _ = c := hr_in_spec.2.2
  -- By uniqueness of nth roots, y = r_n
  have huniq := C.exists_unique_nth_root n hn c hc_pos hc_lt
  have hy_props : 0 < y ∧ y < 1 ∧ C.iterate n y = c := ⟨hy_pos, hy_lt', hy_spec⟩
  exact huniq.unique hy_props hr_n_spec

/-- Key lemma: iterate m (nth_root n x) is independent of scaling.
This is Ling's Lemma 14 (4.19): sₘ rₙ = s_{im} r_{in}.
Proof: If rₙ(x) = y, then yⁿ = x. We need (r_{in}(x))^{im} = x.
Since r_{in}(x)^{in} = x, we have (r_{in}(x)^i)^n = x.
So r_{in}(x)^i = rₙ(x) = y, hence sₘ(rₙ(x)) = y^m = (r_{in}(x)^i)^m = (r_{in}(x))^{im} = s_{im}(r_{in}(x)). -/
lemma iterate_nth_root_scale (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (m n i : ℕ) (hn : 2 ≤ n) (_hm : 1 ≤ m) (hi : 1 ≤ i) :
    C.iterate m (C.nth_root n hn c hc_pos hc_lt) =
    C.iterate (i * m) (C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt) := by
  -- By iterate_i_nth_root_eq: nth_root n c = iterate i (nth_root (i*n) c)
  have h_key := C.iterate_i_nth_root_eq c hc_pos hc_lt n i hn hi
  calc C.iterate m (C.nth_root n hn c hc_pos hc_lt)
      = C.iterate m (C.iterate i (C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt)) := by
          rw [h_key]
    _ = C.iterate (m * i) (C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt) :=
          C.iterate_mul _ m i
    _ = C.iterate (i * m) (C.nth_root (i * n) (le_two_i_mul_n i n hi hn) c hc_pos hc_lt) := by
          ring_nf

/-- Define g* on positive rationals: g*(m/n) = iterate m (nth_root n c) for base point c.
Following Ling's construction at the bottom of page 201. -/
noncomputable def g_star (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) (m n : ℕ)
    (_hm : 1 ≤ m) (hn : 2 ≤ n) : ℝ :=
  C.iterate m (C.nth_root n hn c hc_pos hc_lt)

/-- g* is anti-monotone (decreasing): larger exponent gives smaller value.
For c ∈ (0,1), c^{m/n} is decreasing in m/n. -/
lemma g_star_antitone (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (m₁ n₁ m₂ n₂ : ℕ) (hm₁ : 1 ≤ m₁) (hn₁ : 2 ≤ n₁) (hm₂ : 1 ≤ m₂) (hn₂ : 2 ≤ n₂)
    (h : (m₁ : ℚ) / n₁ ≤ (m₂ : ℚ) / n₂) :
    C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ ≤ C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ := by
  -- Strategy: bring to common denominator, then use that iterate is antitone
  unfold g_star
  have hn₁' : 1 ≤ n₁ := Nat.one_le_of_lt hn₁
  have hn₂' : 1 ≤ n₂ := Nat.one_le_of_lt hn₂
  -- Scale both to common denominator n₁ * n₂
  have h1 := C.iterate_nth_root_scale c hc_pos hc_lt m₁ n₁ n₂ hn₁ hm₁ hn₂'
  have h2 := C.iterate_nth_root_scale c hc_pos hc_lt m₂ n₂ n₁ hn₂ hm₂ hn₁'
  rw [h1, h2]
  -- Rewrite n₂ * n₁ = n₁ * n₂
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  have h_root_eq : C.nth_root (n₂ * n₁) (le_two_i_mul_n n₂ n₁ hn₂' hn₁) c hc_pos hc_lt =
                   C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt := by
    simp only [hcomm]
  rw [h_root_eq]
  -- Now need: iterate (n₁ * m₂) r ≤ iterate (n₂ * m₁) r where r = nth_root (n₁ * n₂) c
  -- From h: m₁/n₁ ≤ m₂/n₂, so m₁ * n₂ ≤ m₂ * n₁
  have h_cross : m₁ * n₂ ≤ m₂ * n₁ := by
    have hn₁_pos : (0 : ℚ) < n₁ := by positivity
    have hn₂_pos : (0 : ℚ) < n₂ := by positivity
    -- div_le_div_iff₀: a / b ≤ c / d ↔ a * d ≤ c * b
    have hq := (div_le_div_iff₀ hn₁_pos hn₂_pos).mp h
    -- hq : (m₁ : ℚ) * n₂ ≤ m₂ * n₁
    exact_mod_cast hq
  -- iterate is antitone: more iterations gives smaller results
  set r := C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt with hr_def
  have hr_spec := C.nth_root_spec (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt
  have h_anti : Antitone (C.iterate · r) := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | step _ ih =>
      exact le_trans (le_of_lt (C.iterate_strictAnti r hr_spec.1 hr_spec.2.1 _)) ih
  -- n₂ * m₁ = m₁ * n₂ and n₁ * m₂ = m₂ * n₁ (by commutativity)
  simp only [Nat.mul_comm n₂ m₁, Nat.mul_comm n₁ m₂]
  exact h_anti h_cross

/-- g* is strictly anti-monotone: larger exponent gives strictly smaller value. -/
lemma g_star_strictAnti (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (m₁ n₁ m₂ n₂ : ℕ) (hm₁ : 1 ≤ m₁) (hn₁ : 2 ≤ n₁) (hm₂ : 1 ≤ m₂) (hn₂ : 2 ≤ n₂)
    (h : (m₁ : ℚ) / n₁ < (m₂ : ℚ) / n₂) :
    C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ < C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ := by
  -- Strategy: bring to common denominator and use strict antitone of iterates.
  unfold g_star
  have hn₁' : 1 ≤ n₁ := Nat.one_le_of_lt hn₁
  have hn₂' : 1 ≤ n₂ := Nat.one_le_of_lt hn₂
  have h1 := C.iterate_nth_root_scale c hc_pos hc_lt m₁ n₁ n₂ hn₁ hm₁ hn₂'
  have h2 := C.iterate_nth_root_scale c hc_pos hc_lt m₂ n₂ n₁ hn₂ hm₂ hn₁'
  rw [h1, h2]
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  have h_root_eq :
      C.nth_root (n₂ * n₁) (le_two_i_mul_n n₂ n₁ hn₂' hn₁) c hc_pos hc_lt =
        C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt := by
    simp only [hcomm]
  rw [h_root_eq]
  -- From h: m₁/n₁ < m₂/n₂, so m₁ * n₂ < m₂ * n₁.
  have h_cross : m₁ * n₂ < m₂ * n₁ := by
    have hn₁_pos : (0 : ℚ) < n₁ := by positivity
    have hn₂_pos : (0 : ℚ) < n₂ := by positivity
    have hq := (div_lt_div_iff₀ hn₁_pos hn₂_pos).mp h
    exact_mod_cast hq
  -- iterate is strictly antitone in the exponent.
  set r := C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt with hr_def
  have hr_spec := C.nth_root_spec (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt
  have h_anti : StrictAnti (fun k => C.iterate k r) :=
    strictAnti_nat_of_succ_lt (C.iterate_strictAnti r hr_spec.1 hr_spec.2.1)
  have h_cross' : n₂ * m₁ < n₁ * m₂ := by
    simpa [Nat.mul_comm n₂ m₁, Nat.mul_comm n₁ m₂] using h_cross
  simpa [Nat.mul_comm n₂ m₁, Nat.mul_comm n₁ m₂] using h_anti h_cross'

/-- Helper: m₁ * n₂ + m₂ * n₁ ≥ 1 when m₁, m₂ ≥ 1 and n₁, n₂ ≥ 2. -/
private lemma sum_prod_ge_one (m₁ n₁ m₂ n₂ : ℕ) (hm₁ : 1 ≤ m₁) (hn₂ : 2 ≤ n₂) :
    1 ≤ m₁ * n₂ + m₂ * n₁ := by
  have h1 : 1 ≤ m₁ * n₂ := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ m₁ * n₂ := Nat.mul_le_mul hm₁ (Nat.one_le_of_lt hn₂)
  omega

/-- Helper: n₁ * n₂ ≥ 2 when n₁, n₂ ≥ 2. -/
private lemma prod_ge_two (n₁ n₂ : ℕ) (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) : 2 ≤ n₁ * n₂ := by
  calc 2 = 1 * 2 := by ring
    _ ≤ n₁ * n₂ := Nat.mul_le_mul (Nat.one_le_of_lt hn₁) hn₂

/-- g* satisfies the functional equation: g*(x) · g*(y) = g*(x + y).
Ling's Proposition (3). -/
lemma g_star_additive (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (m₁ n₁ m₂ n₂ : ℕ) (hm₁ : 1 ≤ m₁) (hn₁ : 2 ≤ n₁) (hm₂ : 1 ≤ m₂) (hn₂ : 2 ≤ n₂) :
    C.F (C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁) (C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂) =
    C.g_star c hc_pos hc_lt (m₁ * n₂ + m₂ * n₁) (n₁ * n₂) (sum_prod_ge_one m₁ n₁ m₂ n₂ hm₁ hn₂) (prod_ge_two n₁ n₂ hn₁ hn₂) := by
  -- g*(m₁/n₁) = iterate m₁ (nth_root n₁ c)
  -- By iterate_nth_root_scale with i = n₂:
  --   = iterate (n₂ * m₁) (nth_root (n₂ * n₁) c)
  -- Similarly for g*(m₂/n₂) with i = n₁:
  --   = iterate (n₁ * m₂) (nth_root (n₁ * n₂) c)
  -- Then F(iterate a r, iterate b r) = iterate (a + b) r by iterate_add
  unfold g_star
  -- Need: 1 ≤ n₂ and 1 ≤ n₁ for iterate_nth_root_scale
  have hn₂' : 1 ≤ n₂ := Nat.one_le_of_lt hn₂
  have hn₁' : 1 ≤ n₁ := Nat.one_le_of_lt hn₁
  -- Scale first term by n₂
  have h1 := C.iterate_nth_root_scale c hc_pos hc_lt m₁ n₁ n₂ hn₁ hm₁ hn₂'
  -- Scale second term by n₁
  have h2 := C.iterate_nth_root_scale c hc_pos hc_lt m₂ n₂ n₁ hn₂ hm₂ hn₁'
  -- Rewrite LHS using these scalings
  rw [h1, h2]
  -- Now both use nth_root with denominator n₂ * n₁ and n₁ * n₂ respectively
  -- These are equal (by commutativity of multiplication)
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  -- Use that nth_root only depends on the value, not the proof
  have h_root_eq : C.nth_root (n₂ * n₁) (le_two_i_mul_n n₂ n₁ hn₂' hn₁) c hc_pos hc_lt =
                   C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt := by
    simp only [hcomm]
  rw [h_root_eq]
  -- Now both sides have nth_root (n₁ * n₂) c
  -- Use iterate_add: F(iterate a x, iterate b x) = iterate (a + b) x
  have h_add := C.iterate_add (C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt)
                              (n₂ * m₁) (n₁ * m₂)
  rw [h_add]
  -- Need to show: iterate ((n₂ * m₁) + (n₁ * m₂)) (...) = iterate (m₁ * n₂ + m₂ * n₁) (...)
  -- (n₂ * m₁) + (n₁ * m₂) = m₁ * n₂ + m₂ * n₁ by ring
  simp only [Nat.mul_comm n₂ m₁, Nat.mul_comm n₁ m₂]

/-- Key lemma: g* approaches 1 for small positive rationals.
This is essential for proving continuity. When m/n → 0+, g*(m/n) → 1.

**Proof Strategy** (Ling 1965, Section 4):
For m/n < 1/N with N large:
- m/n < 1/N implies n > mN ≥ N (since m ≥ 1)
- For n ≥ N, nth_root_n(c) is close to 1 (by nth_root_tendsto_one)
- g*(m/n) = iterate_m(nth_root_n(c)) is close to 1 because:
  - iterate_m is continuous at 1 with iterate_m(1) = 1
  - For r close to 1, iterate_m(r) is close to 1

The subtlety is that the continuity modulus of iterate_m depends on m. However,
since m < n/N and nth_root_n(c) → 1 uniformly as n → ∞, the composition
iterate_m(nth_root_n(c)) → 1 as m/n → 0.

This is a classical real analysis result using uniform continuity of F on
compact sets and the telescoping sum: 1 - iterate_m(r) = Σᵢ [iterate_i(r) - iterate_{i+1}(r)]. -/
lemma g_star_tendsto_one (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ ε > 0, ∃ N : ℕ, N ≥ 2 ∧ ∀ m n : ℕ, (hm : 1 ≤ m) → (hn : 2 ≤ n) →
    (m : ℚ) / n < 1 / N →
    |C.g_star c hc_pos hc_lt m n hm hn - 1| < ε := by
  intro ε hε
  -- It suffices to control the special values `g*(1/N) = nth_root N c`, then use antitonicity.
  have hroot := C.nth_root_tendsto_one c hc_pos hc_lt
  rw [Metric.tendsto_atTop] at hroot
  obtain ⟨N0, hN0⟩ := hroot ε hε
  let N : ℕ := max 2 N0
  refine ⟨N, le_max_left _ _, ?_⟩
  intro m n hm hn hmn
  have hN_ge_2 : 2 ≤ N := le_max_left 2 N0
  have hN_ge_N0 : N0 ≤ N := le_max_right 2 N0
  -- `g*(1/N) = nth_root N c` is close to 1.
  have hN_close : |C.nth_root N hN_ge_2 c hc_pos hc_lt - 1| < ε := by
    have := hN0 N hN_ge_N0
    -- unfold the `if` in `nth_root_tendsto_one` at `N ≥ 2`
    simpa [N, hN_ge_2] using this
  -- `g* (1/N) ≤ g*(m/n)` whenever `m/n < 1/N` (antitonicity).
  have hg_lower : C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2
      ≤ C.g_star c hc_pos hc_lt m n hm hn := by
    have hle : (m : ℚ) / n ≤ 1 / N := le_of_lt hmn
    -- Apply `g_star_antitone` with `(m₁,n₁)=(m,n)` and `(m₂,n₂)=(1,N)`.
    simpa using
      (C.g_star_antitone c hc_pos hc_lt m n 1 N hm hn (by decide : 1 ≤ (1:ℕ)) hN_ge_2 hle)
  -- Both `g*(m/n)` and `g*(1/N)` lie in (0,1], so `|g - 1| = 1 - g`.
  have hg_m_le_one : C.g_star c hc_pos hc_lt m n hm hn ≤ 1 := by
    -- `nth_root n c < 1`, so iterates stay ≤ 1.
    have hr_spec := C.nth_root_spec n hn c hc_pos hc_lt
    exact (C.iterate_mem_Ioc _ hr_spec.1 hr_spec.2.1 m).2
  have hg_N_le_one : C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 ≤ 1 := by
    unfold g_star
    -- `iterate 1` is the identity, so this is just `nth_root N c < 1`.
    have hr_spec := C.nth_root_spec N hN_ge_2 c hc_pos hc_lt
    simpa [C.iterate_one] using (le_of_lt hr_spec.2.1)
  have hg_N_eq_root :
      C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 = C.nth_root N hN_ge_2 c hc_pos hc_lt := by
    simp [g_star, C.iterate_one]
  -- Finish by bounding `1 - g*(m/n)` by `1 - g*(1/N)`.
  have h_sub : 1 - C.g_star c hc_pos hc_lt m n hm hn
      ≤ 1 - C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 := by
    linarith
  have h_abs_m :
      |C.g_star c hc_pos hc_lt m n hm hn - 1| = 1 - C.g_star c hc_pos hc_lt m n hm hn := by
    have hnonpos : C.g_star c hc_pos hc_lt m n hm hn - 1 ≤ 0 := by linarith
    calc
      |C.g_star c hc_pos hc_lt m n hm hn - 1|
          = -(C.g_star c hc_pos hc_lt m n hm hn - 1) := abs_of_nonpos hnonpos
      _ = 1 - C.g_star c hc_pos hc_lt m n hm hn := by ring
  have h_abs_N :
      |C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1|
        = 1 - C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 := by
    have hnonpos :
        C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1 ≤ 0 := by
      linarith
    calc
      |C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1|
          = -(C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1) :=
            abs_of_nonpos hnonpos
      _ = 1 - C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 := by ring
  -- Convert the bound `hN_close` to the corresponding `g*` form.
  have hN_close' :
      |C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1| < ε := by
    simpa [hg_N_eq_root] using hN_close
  -- Combine.
  calc
    |C.g_star c hc_pos hc_lt m n hm hn - 1|
        = 1 - C.g_star c hc_pos hc_lt m n hm hn := h_abs_m
    _ ≤ 1 - C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 := h_sub
    _ = |C.g_star c hc_pos hc_lt 1 N (by decide : 1 ≤ (1:ℕ)) hN_ge_2 - 1| := by
          symm; exact h_abs_N
    _ < ε := hN_close'

/-- g* is continuous. Ling's Proposition (4).

**Proof Strategy**: The continuity of g* follows from:
1. g* is monotone (antitone) - proven in `g_star_antitone`
2. g* satisfies the functional equation g*(r+s) = F(g*(r), g*(s)) - proven in `g_star_additive`
3. A monotone function satisfying a functional equation cannot have jump discontinuities
4. Therefore g* is continuous

The detailed argument: suppose g* has a jump at some rational r. Then there exist
rationals p < r < q arbitrarily close to r such that g*(p) - g*(q) ≥ some ε > 0.
But by additivity, g*(q) = F(g*(p), g*(q-p)), and as q-p → 0, F(g*(p), g*(q-p)) → F(g*(p), 1) = g*(p).
This contradicts the assumption of a jump.

For the formal proof, we use that iterate and nth_root are both continuous (iterate by
induction on continuity of F, nth_root by IVT and the implicit function theorem style argument).
Since g*(m/n) = iterate m (nth_root n c), and both components vary continuously in their
parameters, g* is continuous. -/
lemma g_star_continuous (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ m₁ n₁ m₂ n₂ : ℕ, (hm₁ : 1 ≤ m₁) → (hn₁ : 2 ≤ n₁) →
    (hm₂ : 1 ≤ m₂) → (hn₂ : 2 ≤ n₂) →
    |((m₁ : ℚ) / n₁) - ((m₂ : ℚ) / n₂)| < δ →
    |C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ - C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂| < ε := by
  intro ε hε
  -- Uniform continuity of `F` on the compact square `[0,1]×[0,1]`.
  let f : ℝ × ℝ → ℝ := fun p => C.F p.1 p.2
  let K : Set (ℝ × ℝ) := (Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)
  have hf_uc : UniformContinuousOn f K := by
    have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc)
    exact hK.uniformContinuousOn_of_continuous (C.F_continuous.continuousOn)
  rcases Metric.uniformContinuousOn_iff.1 hf_uc ε hε with ⟨δF, hδF_pos, hδF⟩
  -- If a positive rational `r` is small, then `g*(r)` is close to `1` (Lemma `g_star_tendsto_one`).
  obtain ⟨N, hN_ge2, hN_small⟩ :=
    C.g_star_tendsto_one c hc_pos hc_lt (δF / 2) (by linarith)
  refine ⟨(1 : ℚ) / N, ?_, ?_⟩
  · -- positivity of δ
    have hN_pos : (0 : ℚ) < N := by
      have : (0 : ℕ) < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hN_ge2
      exact_mod_cast this
    exact one_div_pos.mpr hN_pos
  intro m₁ n₁ m₂ n₂ hm₁ hn₁ hm₂ hn₂ hdist
  set r₁ : ℚ := (m₁ : ℚ) / n₁
  set r₂ : ℚ := (m₂ : ℚ) / n₂
  -- If the rationals coincide, the values coincide by antitonicity, hence the difference is 0.
  by_cases hEq : r₁ = r₂
  · have hle : r₁ ≤ r₂ := le_of_eq hEq
    have hge : r₂ ≤ r₁ := le_of_eq hEq.symm
    have h12 :
        C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ ≤ C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ := by
      simpa [r₁, r₂] using C.g_star_antitone c hc_pos hc_lt m₁ n₁ m₂ n₂ hm₁ hn₁ hm₂ hn₂ hle
    have h21 :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ ≤ C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ := by
      simpa [r₁, r₂] using C.g_star_antitone c hc_pos hc_lt m₂ n₂ m₁ n₁ hm₂ hn₂ hm₁ hn₁ hge
    have hg_eq :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ = C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ :=
      le_antisymm h21 h12
    simpa [hg_eq] using hε
  -- Otherwise, compare after scaling to a common denominator and apply uniform continuity of `F`.
  have h_main :
      ∀ {m₁ n₁ m₂ n₂ : ℕ} (hm₁ : 1 ≤ m₁) (hn₁ : 2 ≤ n₁) (hm₂ : 1 ≤ m₂) (hn₂ : 2 ≤ n₂),
        let r₁ : ℚ := (m₁ : ℚ) / n₁
        let r₂ : ℚ := (m₂ : ℚ) / n₂
        r₁ < r₂ →
        |r₁ - r₂| < (1 : ℚ) / N →
        |C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ - C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂| < ε := by
    intro m₁ n₁ m₂ n₂ hm₁ hn₁ hm₂ hn₂
    intro r₁ r₂ hlt hdist
    -- Common denominator D = n₁*n₂, with scaled numerators.
    set D : ℕ := n₁ * n₂
    set M₁ : ℕ := m₁ * n₂
    set M₂ : ℕ := m₂ * n₁
    have hD_ge2 : 2 ≤ D := prod_ge_two n₁ n₂ hn₁ hn₂
    have hn₁' : 1 ≤ n₁ := Nat.one_le_of_lt hn₁
    have hn₂' : 1 ≤ n₂ := Nat.one_le_of_lt hn₂
    -- Scale g*(m₁/n₁) and g*(m₂/n₂) to the common denominator.
    have hscale₁ := C.iterate_nth_root_scale c hc_pos hc_lt m₁ n₁ n₂ hn₁ hm₁ hn₂'
    have hscale₂ := C.iterate_nth_root_scale c hc_pos hc_lt m₂ n₂ n₁ hn₂ hm₂ hn₁'
    -- Rewrite both at denominator D = n₁*n₂.
    have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
    have hroot_eq :
        C.nth_root (n₂ * n₁) (le_two_i_mul_n n₂ n₁ hn₂' hn₁) c hc_pos hc_lt
          = C.nth_root D hD_ge2 c hc_pos hc_lt := by
      simp [D, hcomm]
    have hroot_eq' :
        C.nth_root (n₁ * n₂) (le_two_i_mul_n n₁ n₂ hn₁' hn₂) c hc_pos hc_lt
          = C.nth_root D hD_ge2 c hc_pos hc_lt := by
      simp [D]
    have hg₁ :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁ = C.iterate M₁ (C.nth_root D hD_ge2 c hc_pos hc_lt) := by
      unfold g_star
      -- `hscale₁` already gives the scaled form; just rewrite the denominator/root.
      simpa [M₁, D, Nat.mul_comm m₁ n₂, hroot_eq] using hscale₁
    have hg₂ :
        C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ = C.iterate M₂ (C.nth_root D hD_ge2 c hc_pos hc_lt) := by
      unfold g_star
      simpa [M₂, D, Nat.mul_comm m₂ n₁, hroot_eq'] using hscale₂
    -- Difference in the scaled exponents.
    have hM : M₁ < M₂ := by
      -- From r₁ < r₂, cross-multiply.
      have hn₁_pos : (0 : ℚ) < n₁ := by positivity
      have hn₂_pos : (0 : ℚ) < n₂ := by positivity
      have hcross := (div_lt_div_iff₀ hn₁_pos hn₂_pos).1 (by simpa [r₁, r₂] using hlt)
      -- hcross : (m₁ : ℚ) * n₂ < m₂ * n₁
      exact_mod_cast hcross
    set d : ℕ := M₂ - M₁
    have hd_pos : 1 ≤ d := by
      have : 0 < d := Nat.sub_pos_of_lt hM
      exact Nat.succ_le_iff.2 this
    -- `d/D = r₂ - r₁`, hence `d/D < 1/N` from the δ-assumption.
    have hdiff_lt : (d : ℚ) / D < 1 / N := by
      have h_abs : |r₁ - r₂| = r₂ - r₁ := by
        have hnonpos : r₁ - r₂ ≤ 0 := sub_nonpos.2 (le_of_lt hlt)
        calc
          |r₁ - r₂| = -(r₁ - r₂) := abs_of_nonpos hnonpos
          _ = r₂ - r₁ := by ring
      have h_sub : r₂ - r₁ < 1 / N := by
        have := hdist
        simpa [h_abs] using this
      -- Rewrite r₂ - r₁ with common denominator D.
      have hn₁0 : (n₁ : ℚ) ≠ 0 := by positivity
      have hn₂0 : (n₂ : ℚ) ≠ 0 := by positivity
      have hsub' : r₂ - r₁ = (d : ℚ) / D := by
        -- Expand and clear denominators.
        have hM1_le_M2 : M₁ ≤ M₂ := Nat.le_of_lt hM
        -- Cast `Nat.sub` to `ℚ`.
        have hd_cast : (d : ℚ) = (M₂ : ℚ) - M₁ := by
          simpa [d] using (Nat.cast_sub hM1_le_M2 : ((M₂ - M₁ : ℕ) : ℚ) = (M₂ : ℚ) - M₁)
        -- Now compute.
        -- r₂ - r₁ = m₂/n₂ - m₁/n₁ = (m₂*n₁ - m₁*n₂) / (n₁*n₂) = (M₂ - M₁)/D = d/D.
        -- We stay in `ℚ` and use `field_simp`.
        have : r₂ - r₁ = ((M₂ : ℚ) - M₁) / D := by
          -- Expand r₁,r₂ and clear denominators.
          -- `field_simp` needs nonzero denominators.
          -- Note: `D = n₁*n₂ ≠ 0`.
          have hD0 : (D : ℚ) ≠ 0 := by
            have : (0 : ℕ) < D := lt_of_lt_of_le (by decide : (0:ℕ) < 2) hD_ge2
            exact_mod_cast (Nat.ne_of_gt this)
          -- Use the definitions of r₁,r₂ and of D,M₁,M₂.
          -- `ring`/`field_simp` can handle the arithmetic in `ℚ`.
          have : (m₂ : ℚ) / n₂ - (m₁ : ℚ) / n₁ = ((m₂ : ℚ) * n₁ - (m₁ : ℚ) * n₂) / ((n₂ : ℚ) * n₁) := by
            field_simp [hn₁0, hn₂0]
          -- Align with `D = n₁*n₂` and `M₁,M₂`.
          -- Note `n₂*n₁ = D` in `ℚ` by commutativity.
          simpa [r₁, r₂, D, M₁, M₂, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using this
        -- Substitute `d`.
        simpa [hd_cast, div_eq_mul_inv] using this
      -- Finish.
      simpa [hsub'] using h_sub
    -- Now `g*(d/D)` is close to 1 (within δF/2).
    have hd_small_real :
        |C.g_star c hc_pos hc_lt d D hd_pos hD_ge2 - 1| < δF / 2 := by
      exact hN_small d D hd_pos hD_ge2 hdiff_lt
    have hd_small : dist (C.g_star c hc_pos hc_lt d D hd_pos hD_ge2) 1 < δF := by
      have : dist (C.g_star c hc_pos hc_lt d D hd_pos hD_ge2) 1 < δF / 2 := by
        simpa [Real.dist_eq] using hd_small_real
      exact lt_of_lt_of_le this (by linarith)
    -- Apply uniform continuity of `F` to `(a,x)` and `(1,x)`, where `a = g*(d/D)`.
    set a : ℝ := C.g_star c hc_pos hc_lt d D hd_pos hD_ge2
    set x : ℝ := C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁
    have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := by
      have hr_spec := C.nth_root_spec D hD_ge2 c hc_pos hc_lt
      have hmem := C.iterate_mem_Ioc _ hr_spec.1 hr_spec.2.1 d
      exact ⟨le_of_lt hmem.1, hmem.2⟩
    have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := by
      have hr_spec := C.nth_root_spec n₁ hn₁ c hc_pos hc_lt
      have hmem := C.iterate_mem_Ioc _ hr_spec.1 hr_spec.2.1 m₁
      exact ⟨le_of_lt hmem.1, hmem.2⟩
    have h1x_mem : ((1 : ℝ), x) ∈ K := by
      refine ⟨?_, hx_mem⟩
      exact ⟨by linarith, by linarith⟩
    have hax_mem : (a, x) ∈ K := by
      exact ⟨ha_mem, hx_mem⟩
    have hdist_pair : dist (a, x) ((1 : ℝ), x) < δF := by
      have hx0 : dist x x < δF := by simpa using (show (0 : ℝ) < δF from hδF_pos)
      have hmax : max (dist a 1) (dist x x) < δF := (max_lt_iff).2 ⟨hd_small, hx0⟩
      simpa [Prod.dist_eq] using hmax
    have hF_close : dist (f (a, x)) (f (1, x)) < ε :=
      hδF (a, x) hax_mem (1, x) h1x_mem hdist_pair
    -- Identify the two `g*` values with the `F`-expressions.
    have hx_eq : x = C.iterate M₁ (C.nth_root D hD_ge2 c hc_pos hc_lt) := by
      simp [x, hg₁]
    have ha_eq : a = C.iterate d (C.nth_root D hD_ge2 c hc_pos hc_lt) := by
      simp [a, g_star]
    have hg₂_eq :
        C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ =
          C.F a x := by
      -- Rewrite both sides to the common-denominator iterates.
      -- First rewrite `x` and `a` to the common-denominator iterates.
      rw [hg₂, ha_eq]
      -- Replace `x` using `hg₁`.
      -- (`x` was defined as `g*(m₁/n₁)`.)
      simp [x, hg₁]
      -- Goal: iterate M₂ r = F (iterate d r) (iterate M₁ r)
      have hM1_le_M2 : M₁ ≤ M₂ := Nat.le_of_lt hM
      have hDM : d + M₁ = M₂ := by
        simp [d, Nat.sub_add_cancel hM1_le_M2]
      -- `iterate_add` gives `F (iterate d r) (iterate M₁ r) = iterate (d+M₁) r`.
      have hiter :
          C.F (C.iterate d (C.nth_root D hD_ge2 c hc_pos hc_lt))
              (C.iterate M₁ (C.nth_root D hD_ge2 c hc_pos hc_lt))
            = C.iterate M₂ (C.nth_root D hD_ge2 c hc_pos hc_lt) := by
        simp [C.iterate_add, hDM]
      exact hiter.symm
    -- Conclude.
    have : |C.F a x - C.F 1 x| < ε := by
      simpa [f, Real.dist_eq] using hF_close
    -- Rewrite back to the original `g*` values.
    simpa [hg₂_eq, x, C.F_one_left, abs_sub_comm] using this
  have hlt_or_gt : r₁ < r₂ ∨ r₂ < r₁ := lt_or_gt_of_ne hEq
  cases hlt_or_gt with
  | inl hlt =>
    exact h_main hm₁ hn₁ hm₂ hn₂ (by simpa [r₁, r₂] using hlt) (by simpa [r₁, r₂] using hdist)
  | inr hgt =>
    -- Swap and use symmetry of `abs (· - ·)`.
    have hdist' : |r₂ - r₁| < (1 : ℚ) / N := by simpa [abs_sub_comm, r₁, r₂] using hdist
    have h' :
        |C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ - C.g_star c hc_pos hc_lt m₁ n₁ hm₁ hn₁| < ε :=
      h_main hm₂ hn₂ hm₁ hn₁ (by simpa [r₁, r₂] using hgt) hdist'
    simpa [abs_sub_comm] using h'

/-!
### Aczél's Theorem - Full Proof via Extension

With g* defined and its properties established, we extend to all of (0,1]
by density of rationals, constructing the additive representation Θ.

**Key Insight**: g* is a decreasing function from ℚ⁺ to (0,1] satisfying F(g*(r), g*(s)) = g*(r+s).
We construct Θ as the (generalized) inverse of g*, giving Θ(F(x,y)) = Θ(x) + Θ(y).
-/

/-- The set of positive rationals m/n (with m ≥ 1, n ≥ 2) such that g*(m,n) ≤ x.
This set is used to define Θ(x) as the infimum of rationals r where g*(r) ≤ x.

Since g* is antitone (decreasing), if g*(r₁) ≤ x then g*(r₂) ≤ x for all r₂ ≥ r₁.
Therefore this set is an upward-closed interval, and its infimum gives an increasing function. -/
def g_star_lower_set (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) (x : ℝ) : Set ℝ :=
  { r : ℝ | ∃ (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n),
      r = (m : ℝ) / n ∧ C.g_star c hc_pos hc_lt m n hm hn ≤ x }

/-- The additive representation Θ, defined as the negated generalized inverse of g*.

For x ∈ (0,1], we define:
  Θ(x) = - inf { r ∈ ℚ⁺ : g*(r) ≤ x }

**Key insight**: g* is antitone (decreasing), so the naive inverse Θ₀(x) = inf{r : g*(r) ≤ x}
would also be decreasing. Since we need Θ to be *increasing* (StrictMonoOn), we negate:
Θ(x) = -Θ₀(x).

**Intuition**: g* maps positive rationals to (0,1] such that F(g*(r), g*(s)) = g*(r+s).
If we define Θ₀ as the inverse of g*, then Θ₀(F(g*(r), g*(s))) = r+s = Θ₀(g*(r)) + Θ₀(g*(s)).
Negating preserves additivity: Θ(F(x,y)) = -Θ₀(F(x,y)) = -(Θ₀(x) + Θ₀(y)) = Θ(x) + Θ(y).

**Example**: For F(x,y) = x·y with g*(r) = c^r, we get Θ(x) = -log_c(x) = log(x)/(-log c) = log(x),
which is the standard additive representation.

**Definition**: For x ∈ (0,1], Θ(x) = - sInf { r = m/n : g*(m,n) ≤ x } -/
noncomputable def Theta_extension (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then
    - sInf (C.g_star_lower_set c hc_pos hc_lt x)
  else 0

/-- For any x ∈ (0,1], the lower set is bounded below.

**Proof**: Since g*(1/2) is in (0,1) and finite, the set { r : g*(r) ≤ x } contains
no negative rationals (g* is only defined for m ≥ 1, n ≥ 2, so r ≥ 1/2). -/
lemma g_star_lower_set_bddBelow (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) (x : ℝ)
    (_hx_pos : 0 < x) (_hx_le : x ≤ 1) :
    BddBelow (C.g_star_lower_set c hc_pos hc_lt x) := by
  -- All elements of g_star_lower_set are of the form m/n with m ≥ 1, n ≥ 2
  -- Therefore they are all ≥ 0, so the set is bounded below by 0
  use 0
  intro r hr
  unfold g_star_lower_set at hr
  obtain ⟨m, n, hm, hn, rfl, _⟩ := hr
  -- r = m / n with m ≥ 1, n ≥ 2
  have hm_pos : 0 < (m : ℝ) := by positivity
  have hn_pos : 0 < (n : ℝ) := by positivity
  exact div_nonneg (le_of_lt hm_pos) (le_of_lt hn_pos)

/-- For any x ∈ (0,1], the lower set is non-empty.

**Proof**: Since g*(m/n) → 0 as m/n → ∞, for any x > 0, there exists a large enough
rational r with g*(r) < x, hence g*(r) ≤ x. -/
lemma g_star_lower_set_nonempty (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) (x : ℝ)
    (hx_pos : 0 < x) (_hx_le : x ≤ 1) :
    (C.g_star_lower_set c hc_pos hc_lt x).Nonempty := by
  -- Fix n = 2 and use that iterate m (nth_root 2 c) → 0 as m → ∞
  have hn : (2 : ℕ) ≤ 2 := le_refl 2
  set r := C.nth_root 2 hn c hc_pos hc_lt with hr_def
  have hr_spec := C.nth_root_spec 2 hn c hc_pos hc_lt
  -- iterate m r → 0 as m → ∞
  have h_conv := C.iterate_tendsto_zero r hr_spec.1 hr_spec.2.1
  -- So there exists m such that iterate m r < x
  rw [Metric.tendsto_atTop] at h_conv
  have hx_pos' := hx_pos
  obtain ⟨N, hN⟩ := h_conv x hx_pos'
  -- For m = N+1, we have iterate m r < x
  have hm : 1 ≤ N + 1 := Nat.le_add_left 1 N
  have hdist := hN (N + 1) (Nat.le_succ N)
  simp at hdist
  have hiter_pos := (C.iterate_mem_Ioc r hr_spec.1 hr_spec.2.1 (N + 1)).1
  rw [abs_of_pos hiter_pos] at hdist
  -- Now (N+1)/2 is in the lower set
  use (N + 1 : ℝ) / 2
  unfold g_star_lower_set
  use N + 1, 2, hm, hn
  constructor
  · norm_cast
  · unfold g_star
    exact le_of_lt hdist

/-- Θ is strictly monotone on (0,1): if x < y then Θ(x) < Θ(y).

**Proof Strategy**: Θ(x) = - inf { r : g*(r) ≤ x }. Since g* is antitone (decreasing):
- For x < y, we have { r : g*(r) ≤ x } ⊆ { r : g*(r) ≤ y }
- Subset inclusion means inf{...x...} ≥ inf{...y...}
- Negating flips the inequality: -inf{...x...} ≤ -inf{...y...}
- Wait, that gives Θ(x) ≤ Θ(y), but we need strict inequality

Actually, we need to use that g* has dense range (or at least that for x < y, there exists
a rational r with g*(r) strictly between x and y). This gives us inf{...x...} > inf{...y...},
hence Θ(x) < Θ(y). -/
lemma Theta_extension_strictMono (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    StrictMonoOn (C.Theta_extension c hc_pos hc_lt) (Set.Ioc 0 1) := by
  intro x hx y hy hxy
  unfold Theta_extension
  simp only [hx.1, hx.2, hy.1, hy.2, and_self, ite_true]
  -- Goal: - sInf {...x...} < - sInf {...y...}
  -- Equivalently: sInf {...y...} < sInf {...x...}
  classical
  set Sx : Set ℝ := C.g_star_lower_set c hc_pos hc_lt x
  set Sy : Set ℝ := C.g_star_lower_set c hc_pos hc_lt y
  have hSx_ne : Sx.Nonempty :=
    C.g_star_lower_set_nonempty c hc_pos hc_lt x hx.1 hx.2
  have hSy_ne : Sy.Nonempty :=
    C.g_star_lower_set_nonempty c hc_pos hc_lt y hy.1 hy.2
  have hSx_bdd : BddBelow Sx :=
    C.g_star_lower_set_bddBelow c hc_pos hc_lt x hx.1 hx.2
  have hSy_bdd : BddBelow Sy :=
    C.g_star_lower_set_bddBelow c hc_pos hc_lt y hy.1 hy.2

  have hsub : Sx ⊆ Sy := by
    intro r hr
    rcases hr with ⟨m, n, hm, hn, rfl, hgm_le⟩
    exact ⟨m, n, hm, hn, rfl, le_trans hgm_le (le_of_lt hxy)⟩

  -- Non-strict inequality comes from set inclusion.
  have hle_csInf : sInf Sy ≤ sInf Sx :=
    csInf_le_csInf (s := Sx) (t := Sy) hSy_bdd hSx_ne hsub

  -- We now show strictness by stepping just below `sInf Sx` while keeping `g*` within `y`.
  have hx_lt_one : x < 1 := lt_of_lt_of_le hxy hy.2
  have hεpos : 0 < y - x := sub_pos.mpr hxy
  obtain ⟨δ, hδpos, hδ⟩ := C.g_star_continuous c hc_pos hc_lt (y - x) hεpos

  -- A positive lower bound on `sInf Sx`, obtained from `g* r → 1` as `r → 0+`.
  have hε0pos : 0 < (1 - x) / 2 := by nlinarith
  obtain ⟨N0, hN0_ge2, hN0_small⟩ := C.g_star_tendsto_one c hc_pos hc_lt ((1 - x) / 2) hε0pos
  have h_oneDivN0_le_csInf : (1 : ℝ) / N0 ≤ sInf Sx := by
    apply le_csInf hSx_ne
    intro r hr
    rcases hr with ⟨m, n, hm, hn, rfl, hgm_le_x⟩
    have hroot_spec := C.nth_root_spec n hn c hc_pos hc_lt
    have hgm_le1 : C.g_star c hc_pos hc_lt m n hm hn ≤ 1 := by
      unfold g_star
      exact (C.iterate_mem_Ioc (C.nth_root n hn c hc_pos hc_lt) hroot_spec.1 hroot_spec.2.1 m).2
    have hnot_lt : ¬ ((m : ℚ) / n < (1 : ℚ) / N0) := by
      intro hlt
      have habs : |C.g_star c hc_pos hc_lt m n hm hn - 1| < (1 - x) / 2 :=
        hN0_small m n hm hn hlt
      have hnonpos : C.g_star c hc_pos hc_lt m n hm hn - 1 ≤ 0 := by linarith
      have habs' :
          |C.g_star c hc_pos hc_lt m n hm hn - 1| = 1 - C.g_star c hc_pos hc_lt m n hm hn := by
        calc
          |C.g_star c hc_pos hc_lt m n hm hn - 1|
              = -(C.g_star c hc_pos hc_lt m n hm hn - 1) := abs_of_nonpos hnonpos
          _ = 1 - C.g_star c hc_pos hc_lt m n hm hn := by ring
      have h1m_lt : 1 - C.g_star c hc_pos hc_lt m n hm hn < (1 - x) / 2 := by
        simpa [habs'] using habs
      have hx_lt_gm : x < C.g_star c hc_pos hc_lt m n hm hn := by
        nlinarith [hx_lt_one, h1m_lt]
      exact (not_lt_of_ge hgm_le_x) hx_lt_gm
    have hle_rat : (1 : ℚ) / N0 ≤ (m : ℚ) / n := le_of_not_gt hnot_lt
    have hle_rat' : ((1 : ℚ) / N0 : ℝ) ≤ ((m : ℚ) / n : ℝ) := by
      exact_mod_cast hle_rat
    simpa using hle_rat'

  -- Choose `N` large enough so that `1/N < δ` and also `1/N < 1/N0`.
  obtain ⟨nδ, hnδ⟩ := exists_nat_one_div_lt hδpos
  let Nδ : ℕ := nδ + 1
  have h_oneDivNδ_lt_δ : (1 : ℚ) / Nδ < δ := by simpa [Nδ] using hnδ
  let N : ℕ := max Nδ (N0 + 1)
  have hN_ge_Nδ : Nδ ≤ N := le_max_left _ _
  have hN_gt_N0 : N0 < N := lt_of_lt_of_le (Nat.lt_succ_self N0) (le_max_right _ _)
  have hN_pos_nat : 0 < N := lt_of_lt_of_le (Nat.succ_pos nδ) hN_ge_Nδ
  have h_oneDivN_lt_δ : (1 : ℚ) / N < δ := by
    have hNδ_pos : (0 : ℚ) < (Nδ : ℚ) := by exact_mod_cast Nat.succ_pos nδ
    have hcast : (Nδ : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN_ge_Nδ
    have h_oneDiv_le : (1 : ℚ) / N ≤ (1 : ℚ) / Nδ := by
      simpa using (one_div_le_one_div_of_le hNδ_pos hcast)
    exact lt_of_le_of_lt h_oneDiv_le h_oneDivNδ_lt_δ
  have h_oneDivN_lt_oneDivN0 : (1 : ℝ) / N < (1 : ℝ) / N0 := by
    have hN0_pos : 0 < (N0 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hN0_ge2)
    have hN0_lt_N : (N0 : ℝ) < N := by exact_mod_cast hN_gt_N0
    exact one_div_lt_one_div_of_lt hN0_pos hN0_lt_N
  have h_oneDivN_lt_csInf : (1 : ℝ) / N < sInf Sx :=
    lt_of_lt_of_le h_oneDivN_lt_oneDivN0 h_oneDivN0_le_csInf

  -- Pick an element of `Sx` within `1/N` of `sInf Sx`, then step down by `1/N`.
  have hcsInf_lt : sInf Sx < sInf Sx + (1 : ℝ) / N :=
    lt_add_of_pos_right _ (one_div_pos.mpr (by exact_mod_cast hN_pos_nat))
  rcases exists_lt_of_csInf_lt hSx_ne hcsInf_lt with ⟨r₂, hr₂_mem, hr₂_lt⟩
  have hcsInf_le_r₂ : sInf Sx ≤ r₂ := csInf_le hSx_bdd hr₂_mem
  rcases hr₂_mem with ⟨m₂, n₂, hm₂, hn₂, hr₂_eq, hg₂_le_x⟩
  -- Define the stepped-down rational.
  let m₁ : ℕ := m₂ * N - n₂
  let n₁ : ℕ := n₂ * N
  have hn₂_posQ : (0 : ℚ) < n₂ := by positivity
  have hN_posQ : (0 : ℚ) < N := by exact_mod_cast hN_pos_nat
  have hrat_oneDiv_lt : (1 : ℚ) / N < (m₂ : ℚ) / n₂ := by
    have hreal_oneDiv_lt : (1 : ℝ) / N < (m₂ : ℝ) / n₂ := by
      -- `1/N < sInf Sx ≤ r₂ = m₂/n₂`
      have h1 : (1 : ℝ) / N < r₂ := lt_of_lt_of_le h_oneDivN_lt_csInf hcsInf_le_r₂
      simpa [hr₂_eq] using h1
    refine (Rat.cast_lt (K := ℝ)).1 ?_
    simpa [Rat.cast_div] using hreal_oneDiv_lt
  have hmul_lt : (n₂ : ℚ) < (m₂ : ℚ) * N := by
    have := (div_lt_div_iff₀ hN_posQ hn₂_posQ).1 hrat_oneDiv_lt
    -- `1 * n₂ < m₂ * N`
    simpa [one_mul, mul_assoc, mul_comm, mul_left_comm] using this
  have hmul_lt_nat : n₂ < m₂ * N := by exact_mod_cast hmul_lt
  have hm₁_pos : 1 ≤ m₁ := by
    have : 0 < m₁ := Nat.sub_pos_of_lt hmul_lt_nat
    exact Nat.succ_le_iff.2 this
  have hn₁_ge2 : 2 ≤ n₁ := by
    have hN_pos : 0 < N := hN_pos_nat
    have hmul : n₂ ≤ n₂ * N := Nat.le_mul_of_pos_right _ hN_pos
    simpa [n₁] using le_trans hn₂ hmul

  have hr₁_def : ((m₁ : ℝ) / n₁) = r₂ - (1 : ℝ) / N := by
    -- Compute in ℝ: (m₂*N - n₂)/(n₂*N) = m₂/n₂ - 1/N
    have hn₂_pos : 0 < n₂ := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn₂
    have hn₂0 : (n₂ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₂_pos)
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN_pos_nat)
    -- `r₂ = m₂/n₂`
    subst hr₂_eq
    have hmul_le_nat : n₂ ≤ m₂ * N := le_of_lt hmul_lt_nat
    simp [m₁, n₁, Nat.cast_sub hmul_le_nat] at *
    field_simp [hn₂0, hN0]

  have hr₁_lt_csInf : (m₁ : ℝ) / n₁ < sInf Sx := by
    -- from `r₂ < sInf Sx + 1/N`
    have : r₂ - (1 : ℝ) / N < sInf Sx :=
      (sub_lt_iff_lt_add).2 (by simpa using hr₂_lt)
    simpa [hr₁_def] using this

  -- Show `m₁/n₁ ∈ Sy` using continuity of `g*` and the slack `y-x`.
  have hdist_rat : |((m₁ : ℚ) / n₁) - ((m₂ : ℚ) / n₂)| < δ := by
    -- The difference is exactly `1/N`.
    have hn₂0Q : (n₂ : ℚ) ≠ 0 := by positivity
    have hN0Q : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN_pos_nat)
    have hcalc :
        ((m₁ : ℚ) / n₁) - ((m₂ : ℚ) / n₂) = - (1 : ℚ) / N := by
      have hmul_le_nat : n₂ ≤ m₂ * N := le_of_lt hmul_lt_nat
      simp [m₁, n₁, Nat.cast_sub hmul_le_nat] at *
      field_simp [hn₂0Q, hN0Q]
      ring_nf
    have habs : |((m₁ : ℚ) / n₁) - ((m₂ : ℚ) / n₂)| = (1 : ℚ) / N := by
      have hpos : 0 < (1 : ℚ) / N := one_div_pos.2 hN_posQ
      have habs_pos : |(1 : ℚ) / N| = (1 : ℚ) / N := abs_of_pos hpos
      calc
        |((m₁ : ℚ) / n₁) - ((m₂ : ℚ) / n₂)|
            = |-(1 : ℚ) / N| := by simp [hcalc]
        _ = |(1 : ℚ) / N| := by
          simp [neg_div]
        _ = (1 : ℚ) / N := habs_pos
    -- Use `1/N < δ`.
    simpa [habs] using h_oneDivN_lt_δ
  have hdiff_g :
      |C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 -
          C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂| < y - x :=
    hδ m₁ n₁ m₂ n₂ hm₁_pos hn₁_ge2 hm₂ hn₂ hdist_rat
  have hg₁_le_y : C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 ≤ y := by
    have hsub' :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 -
            C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ < y - x :=
      lt_of_le_of_lt (le_abs_self _) hdiff_g
    have hlt :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 <
          C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ + (y - x) := by linarith
    have hle :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 ≤
          C.g_star c hc_pos hc_lt m₂ n₂ hm₂ hn₂ + (y - x) := le_of_lt hlt
    have hle' :
        C.g_star c hc_pos hc_lt m₁ n₁ hm₁_pos hn₁_ge2 ≤ x + (y - x) :=
      le_trans hle (add_le_add_right hg₂_le_x _)
    simpa [add_sub_cancel] using hle'

  have hr₁_mem_Sy : ((m₁ : ℝ) / n₁) ∈ Sy := by
    refine ⟨m₁, n₁, hm₁_pos, hn₁_ge2, rfl, hg₁_le_y⟩

  -- Thus `sInf Sy < sInf Sx`.
  have hlt_csInf : sInf Sy < sInf Sx := by
    have : ∃ r ∈ Sy, r < sInf Sx := ⟨(m₁ : ℝ) / n₁, hr₁_mem_Sy, hr₁_lt_csInf⟩
    exact (csInf_lt_iff hSy_bdd hSy_ne).2 this

  -- Negation flips the inequality back to the desired strict monotonicity statement.
  exact neg_lt_neg hlt_csInf

/-- Θ is nonpositive on (0,1]. -/
lemma Theta_extension_le_zero (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 1) :
    C.Theta_extension c hc_pos hc_lt x ≤ 0 := by
  classical
  unfold Theta_extension
  have hx' : 0 < x ∧ x ≤ 1 := hx
  simp [hx'.1, hx'.2]
  set Sx : Set ℝ := C.g_star_lower_set c hc_pos hc_lt x
  have hSx_ne : Sx.Nonempty :=
    C.g_star_lower_set_nonempty c hc_pos hc_lt x hx'.1 hx'.2
  have h0 : ∀ r ∈ Sx, 0 ≤ r := by
    intro r hr
    rcases hr with ⟨m, n, _hm, _hn, rfl, _⟩
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hn_pos : 0 < (n : ℝ) := by positivity
    exact div_nonneg (le_of_lt hm_pos) (le_of_lt hn_pos)
  have hsInf_ge : 0 ≤ sInf Sx := le_csInf hSx_ne h0
  linarith

/-- Θ inverts g* on rational grid points. -/
lemma Theta_extension_g_star (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    C.Theta_extension c hc_pos hc_lt (C.g_star c hc_pos hc_lt m n hm hn) =
      - (m : ℝ) / n := by
  classical
  set x : ℝ := C.g_star c hc_pos hc_lt m n hm hn
  have hr_spec := C.nth_root_spec n hn c hc_pos hc_lt
  have hx_mem :=
    C.iterate_mem_Ioc (C.nth_root n hn c hc_pos hc_lt) hr_spec.1 hr_spec.2.1 m
  have hx_pos : 0 < x := by
    simpa [x, g_star] using hx_mem.1
  have hx_le : x ≤ 1 := by
    simpa [x, g_star] using hx_mem.2
  unfold Theta_extension
  simp [hx_pos, hx_le]
  set Sx : Set ℝ := C.g_star_lower_set c hc_pos hc_lt x
  have hSx_ne : Sx.Nonempty :=
    C.g_star_lower_set_nonempty c hc_pos hc_lt x hx_pos hx_le
  have hSx_bdd : BddBelow Sx :=
    C.g_star_lower_set_bddBelow c hc_pos hc_lt x hx_pos hx_le
  have hmem : (m : ℝ) / n ∈ Sx := by
    refine ⟨m, n, hm, hn, rfl, ?_⟩
    simp [x]
  have hle : sInf Sx ≤ (m : ℝ) / n := csInf_le hSx_bdd hmem
  have hlb : (m : ℝ) / n ≤ sInf Sx := by
    apply le_csInf hSx_ne
    intro r hr
    rcases hr with ⟨m', n', hm', hn', rfl, hgm_le⟩
    by_contra hlt
    have hlt_real : (m' : ℝ) / n' < (m : ℝ) / n := lt_of_not_ge hlt
    have hlt_rat : (m' : ℚ) / n' < (m : ℚ) / n := by
      refine (Rat.cast_lt (K := ℝ)).1 ?_
      simpa [Rat.cast_div] using hlt_real
    have hgt :
        C.g_star c hc_pos hc_lt m n hm hn <
          C.g_star c hc_pos hc_lt m' n' hm' hn' := by
      exact C.g_star_strictAnti c hc_pos hc_lt m' n' m n hm' hn' hm hn hlt_rat
    exact (not_lt_of_ge hgm_le) hgt
  have hEq : sInf Sx = (m : ℝ) / n := le_antisymm hle hlb
  simp [Sx, hEq, neg_div]

/-- Any positive rational can be written as `m/n` with `n ≥ 2`, as a real equality. -/
lemma rat_pos_exists_mn_real (q : ℚ) (hq : 0 < q) :
    ∃ m n : ℕ, 1 ≤ m ∧ 2 ≤ n ∧ ((q : ℝ) = (m : ℝ) / n) := by
  classical
  let m0 : ℕ := q.num.natAbs
  let n0 : ℕ := q.den
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hnum_nonneg : 0 ≤ q.num := le_of_lt hnum_pos
  have hq_cast : (q : ℝ) = (m0 : ℝ) / n0 := by
    have hq_cast' : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      simpa using (Rat.cast_def (K := ℝ) q)
    have hnum_eq : (m0 : ℝ) = (q.num : ℝ) := by
      have hnum_eq_z : (m0 : ℤ) = q.num := by
        simpa [m0] using (Int.natAbs_of_nonneg hnum_nonneg)
      exact_mod_cast hnum_eq_z
    simpa [m0, n0, hnum_eq] using hq_cast'
  have hm0_pos : 0 < m0 := by
    have hnum_ne : q.num ≠ 0 := ne_of_gt hnum_pos
    simpa [m0] using (Int.natAbs_pos.mpr hnum_ne)
  let m : ℕ := 2 * m0
  let n : ℕ := 2 * n0
  have hm_pos : 0 < m := by
    exact Nat.mul_pos (by decide : 0 < 2) hm0_pos
  have hm : 1 ≤ m := Nat.succ_le_iff.mpr hm_pos
  have hn0 : 1 ≤ n0 := Nat.succ_le_iff.mpr q.den_pos
  have hn : 2 ≤ n := by
    simpa [n] using (Nat.mul_le_mul_left 2 hn0)
  have hq_cast' : (m0 : ℝ) / n0 = (m : ℝ) / n := by
    have h :=
      (mul_div_mul_left (a := (m0 : ℝ)) (b := (n0 : ℝ)) (c := (2 : ℝ)) (by norm_num))
    simpa [m, n, mul_comm, mul_left_comm, mul_assoc] using h.symm
  refine ⟨m, n, hm, hn, ?_⟩
  exact hq_cast.trans hq_cast'

/-- Negative rationals are in the image of Θ on `(0,1]`. -/
lemma Theta_extension_neg_rat (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1)
    {q : ℚ} (hq : (q : ℝ) < 0) :
    ∃ x ∈ Set.Ioc (0 : ℝ) 1, C.Theta_extension c hc_pos hc_lt x = (q : ℝ) := by
  have hq_neg : (q : ℚ) < 0 := by
    exact (Rat.cast_lt (K := ℝ)).1 (by simpa using hq)
  have hq_pos : 0 < -q := by linarith
  rcases rat_pos_exists_mn_real (-q) hq_pos with ⟨m, n, hm, hn, hq_eq⟩
  have hq_eq' : (q : ℝ) = - (m : ℝ) / n := by
    have hq_eq'' : -(q : ℝ) = (m : ℝ) / n := by
      simpa using hq_eq
    have hq_eq''' := congrArg (fun t => -t) hq_eq''
    simpa [neg_div] using hq_eq'''
  refine ⟨C.g_star c hc_pos hc_lt m n hm hn, ?_, ?_⟩
  · have hr_spec := C.nth_root_spec n hn c hc_pos hc_lt
    have hmem :=
      C.iterate_mem_Ioc (C.nth_root n hn c hc_pos hc_lt) hr_spec.1 hr_spec.2.1 m
    simpa [g_star] using hmem
  · have htheta := C.Theta_extension_g_star c hc_pos hc_lt m n hm hn
    simpa [hq_eq'] using htheta

/-- Θ is continuous on (0,1].

**Proof Strategy**: Θ is monotone (strictly antitone) and defined as a supremum over a dense set.
Monotone functions are continuous iff they have no jump discontinuities. The density of rationals
ensures no jumps exist. -/
lemma Theta_extension_continuousOn (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ContinuousOn (C.Theta_extension c hc_pos hc_lt) (Set.Ioc 0 1) := by
  classical
  let Θ : ℝ → ℝ := C.Theta_extension c hc_pos hc_lt
  have hmono : StrictMonoOn Θ (Set.Ioc (0 : ℝ) 1) := by
    simpa [Θ] using C.Theta_extension_strictMono c hc_pos hc_lt
  intro x hx
  by_cases hx1 : x = 1
  · subst hx1
    have hs : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[≤] (1 : ℝ) := by
      exact Ioc_mem_nhdsLE (by norm_num : (0 : ℝ) < 1)
    have hθ1_le : Θ 1 ≤ 0 := by
      simpa [Θ] using C.Theta_extension_le_zero c hc_pos hc_lt (by simp)
    have hfs_l :
        ∀ b < Θ 1, ∃ c ∈ Set.Ioc (0 : ℝ) 1, Θ c ∈ Set.Ico b (Θ 1) := by
      intro b hb
      rcases exists_rat_btwn hb with ⟨q, hq⟩
      have hq_neg : (q : ℝ) < 0 := lt_of_lt_of_le hq.2 hθ1_le
      rcases C.Theta_extension_neg_rat c hc_pos hc_lt hq_neg with ⟨c', hc'_mem, hc'_eq⟩
      refine ⟨c', hc'_mem, ?_⟩
      have : (q : ℝ) ∈ Set.Ico b (Θ 1) := ⟨hq.1.le, hq.2⟩
      simpa [Θ, hc'_eq] using this
    have hcont := hmono.continuousWithinAt_left_of_exists_between hs hfs_l
    simpa [Θ] using hcont
  · have hx_lt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hs : Set.Ioc (0 : ℝ) 1 ∈ 𝓝 x := Ioc_mem_nhds hx.1 hx_lt
    have hθ1_le : Θ 1 ≤ 0 := by
      simpa [Θ] using C.Theta_extension_le_zero c hc_pos hc_lt (by simp)
    have hθx_lt : Θ x < 0 := by
      have h1_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by simp
      have hlt := hmono hx h1_mem hx_lt
      exact lt_of_lt_of_le hlt hθ1_le
    have hfs_l :
        ∀ b < Θ x, ∃ c ∈ Set.Ioc (0 : ℝ) 1, Θ c ∈ Set.Ico b (Θ x) := by
      intro b hb
      rcases exists_rat_btwn hb with ⟨q, hq⟩
      have hq_neg : (q : ℝ) < 0 := lt_trans hq.2 hθx_lt
      rcases C.Theta_extension_neg_rat c hc_pos hc_lt hq_neg with ⟨c', hc'_mem, hc'_eq⟩
      refine ⟨c', hc'_mem, ?_⟩
      have : (q : ℝ) ∈ Set.Ico b (Θ x) := ⟨hq.1.le, hq.2⟩
      simpa [Θ, hc'_eq] using this
    have hfs_r :
        ∀ b > Θ x, ∃ c ∈ Set.Ioc (0 : ℝ) 1, Θ c ∈ Set.Ioc (Θ x) b := by
      intro b hb
      have hmin : Θ x < min b (0 : ℝ) := (lt_min_iff).2 ⟨hb, hθx_lt⟩
      rcases exists_rat_btwn hmin with ⟨q, hq⟩
      have hq_neg : (q : ℝ) < 0 := lt_of_lt_of_le hq.2 (min_le_right _ _)
      rcases C.Theta_extension_neg_rat c hc_pos hc_lt hq_neg with ⟨c', hc'_mem, hc'_eq⟩
      refine ⟨c', hc'_mem, ?_⟩
      have hq_le_b : (q : ℝ) ≤ b := by
        exact le_trans (le_of_lt hq.2) (min_le_left _ _)
      have : (q : ℝ) ∈ Set.Ioc (Θ x) b := ⟨hq.1, hq_le_b⟩
      simpa [Θ, hc'_eq] using this
    have hcont := hmono.continuousAt_of_exists_between hs hfs_l hfs_r
    exact hcont.continuousWithinAt

/-- Θ maps `1` to `0`. -/
lemma Theta_extension_one (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    C.Theta_extension c hc_pos hc_lt (1 : ℝ) = 0 := by
  classical
  unfold Theta_extension
  simp
  set S : Set ℝ := C.g_star_lower_set c hc_pos hc_lt (1 : ℝ)
  have hS_ne : S.Nonempty :=
    C.g_star_lower_set_nonempty c hc_pos hc_lt 1 (by norm_num) (by norm_num)
  have hS_bdd : BddBelow S :=
    C.g_star_lower_set_bddBelow c hc_pos hc_lt 1 (by norm_num) (by norm_num)
  have hS_ge : 0 ≤ sInf S := by
    apply le_csInf hS_ne
    intro r hr
    rcases hr with ⟨m, n, _hm, _hn, rfl, _⟩
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hn_pos : 0 < (n : ℝ) := by positivity
    exact div_nonneg (le_of_lt hm_pos) (le_of_lt hn_pos)
  have hS_le : sInf S ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < sInf S := lt_of_not_ge hpos
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos'
    let n : ℕ := max (N + 1) 2
    have hn_ge2 : 2 ≤ n := le_max_right _ _
    have hN1_le : (N + 1 : ℕ) ≤ n := le_max_left _ _
    have hdiv_le : (1 : ℝ) / n ≤ (1 : ℝ) / (N + 1) := by
      have hN1_pos : 0 < (N + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_pos N)
      have hN1_le' : (N + 1 : ℝ) ≤ n := by
        exact_mod_cast hN1_le
      exact one_div_le_one_div_of_le hN1_pos hN1_le'
    have hdiv_lt : (1 : ℝ) / n < sInf S := by
      exact lt_of_le_of_lt hdiv_le (by simpa using hN)
    have hmem : (1 : ℝ) / n ∈ S := by
      have hm : 1 ≤ (1 : ℕ) := by decide
      have hr_spec := C.nth_root_spec n hn_ge2 c hc_pos hc_lt
      have hmem_iter :=
        C.iterate_mem_Ioc (C.nth_root n hn_ge2 c hc_pos hc_lt) hr_spec.1 hr_spec.2.1 1
      have hle : C.g_star c hc_pos hc_lt 1 n hm hn_ge2 ≤ 1 := by
        simpa [g_star] using hmem_iter.2
      refine ⟨1, n, hm, hn_ge2, ?_, hle⟩
      simp
    have hle_inf : sInf S ≤ (1 : ℝ) / n := csInf_le hS_bdd hmem
    exact (not_lt_of_ge hle_inf) hdiv_lt
  have hEq : sInf S = 0 := le_antisymm hS_le hS_ge
  simp [S, hEq]

/-- Θ satisfies the additive property: Θ(F(x,y)) = Θ(x) + Θ(y).

**Proof Strategy**:
1. By density, approximate x, y by rational sequences r_n → x, s_n → y where g*(r_n) → x, g*(s_n) → y
2. By definition of Θ as inverse of g*: Θ(g*(r_n)) = r_n and Θ(g*(s_n)) = s_n
3. By g_star_additive: F(g*(r_n), g*(s_n)) = g*(r_n + s_n)
4. By continuity of F: F(g*(r_n), g*(s_n)) → F(x,y)
5. By continuity of Θ: Θ(F(g*(r_n), g*(s_n))) → Θ(F(x,y))
6. But Θ(F(g*(r_n), g*(s_n))) = Θ(g*(r_n + s_n)) = r_n + s_n → Θ(x) + Θ(y)
7. Therefore: Θ(F(x,y)) = Θ(x) + Θ(y) -/
lemma Theta_extension_additive (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 →
    C.Theta_extension c hc_pos hc_lt (C.F x y) =
    C.Theta_extension c hc_pos hc_lt x + C.Theta_extension c hc_pos hc_lt y := by
  intro x y hx_pos hx_le hy_pos hy_le
  classical
  let Θ : ℝ → ℝ := C.Theta_extension c hc_pos hc_lt
  have hmono : StrictMonoOn Θ (Set.Ioc (0 : ℝ) 1) := by
    simpa [Θ] using C.Theta_extension_strictMono c hc_pos hc_lt
  have hθ1 : Θ 1 = 0 := by
    simpa [Θ] using C.Theta_extension_one c hc_pos hc_lt
  by_cases hx1 : x = 1
  · subst hx1
    simp [Θ, hθ1, C.F_one_left]
  by_cases hy1 : y = 1
  · subst hy1
    simp [Θ, hθ1, C.F_one_right]
  have hx_lt : x < 1 := lt_of_le_of_ne hx_le hx1
  have hy_lt : y < 1 := lt_of_le_of_ne hy_le hy1
  have hx_mem : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hx_pos, hx_le⟩
  have hy_mem : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy_pos, hy_le⟩
  have hθx_lt : Θ x < 0 := by
    have h1_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by simp
    have hlt := hmono hx_mem h1_mem hx_lt
    simpa [hθ1] using hlt
  have hθy_lt : Θ y < 0 := by
    have h1_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by simp
    have hlt := hmono hy_mem h1_mem hy_lt
    simpa [hθ1] using hlt
  have g_star_mem :
      ∀ m n (hm : 1 ≤ m) (hn : 2 ≤ n),
        C.g_star c hc_pos hc_lt m n hm hn ∈ Set.Ioc (0 : ℝ) 1 := by
    intro m n hm hn
    have hr_spec := C.nth_root_spec n hn c hc_pos hc_lt
    have hmem :=
      C.iterate_mem_Ioc (C.nth_root n hn c hc_pos hc_lt) hr_spec.1 hr_spec.2.1 m
    simpa [g_star] using hmem
  have theta_F_gstar :
      ∀ m1 n1 (hm1 : 1 ≤ m1) (hn1 : 2 ≤ n1) m2 n2 (hm2 : 1 ≤ m2) (hn2 : 2 ≤ n2),
        Θ (C.F (C.g_star c hc_pos hc_lt m1 n1 hm1 hn1)
                 (C.g_star c hc_pos hc_lt m2 n2 hm2 hn2)) =
          - (m1 : ℝ) / n1 - (m2 : ℝ) / n2 := by
    intro m1 n1 hm1 hn1 m2 n2 hm2 hn2
    have hF :=
      C.g_star_additive c hc_pos hc_lt m1 n1 m2 n2 hm1 hn1 hm2 hn2
    have hθ_sum :=
      C.Theta_extension_g_star c hc_pos hc_lt
        (m1 * n2 + m2 * n1) (n1 * n2)
        (sum_prod_ge_one m1 n1 m2 n2 hm1 hn2) (prod_ge_two n1 n2 hn1 hn2)
    have hθ_sum' :
        Θ (C.g_star c hc_pos hc_lt (m1 * n2 + m2 * n1) (n1 * n2)
            (sum_prod_ge_one m1 n1 m2 n2 hm1 hn2) (prod_ge_two n1 n2 hn1 hn2)) =
          - ((m1 : ℝ) * n2 + (m2 : ℝ) * n1) / (n1 * n2) := by
      simpa [Θ, Nat.cast_add, Nat.cast_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hθ_sum
    have hsum :
        - (m1 : ℝ) / n1 - (m2 : ℝ) / n2 =
          - ((m1 : ℝ) * n2 + (m2 : ℝ) * n1) / (n1 * n2) := by
      have hn1' : (n1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn1))
      have hn2' : (n2 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2))
      field_simp [hn1', hn2']
      ring
    calc
      Θ (C.F (C.g_star c hc_pos hc_lt m1 n1 hm1 hn1)
            (C.g_star c hc_pos hc_lt m2 n2 hm2 hn2))
          =
          Θ (C.g_star c hc_pos hc_lt (m1 * n2 + m2 * n1) (n1 * n2)
            (sum_prod_ge_one m1 n1 m2 n2 hm1 hn2) (prod_ge_two n1 n2 hn1 hn2)) := by
            simp [Θ, hF]
      _ = - ((m1 : ℝ) * n2 + (m2 : ℝ) * n1) / (n1 * n2) := hθ_sum'
      _ = - (m1 : ℝ) / n1 - (m2 : ℝ) / n2 := by simp [hsum]
  let a : ℝ := Θ x
  let b : ℝ := Θ y
  have h_upper : Θ (C.F x y) ≤ a + b := by
    by_contra hgt
    have hgt' : a + b < Θ (C.F x y) := lt_of_not_ge hgt
    set ε : ℝ := Θ (C.F x y) - (a + b) with hε_def
    have hε_pos : 0 < ε := by linarith
    have hx_interval : a < min (a + ε / 4) 0 := by
      refine (lt_min_iff).2 ?_
      refine ⟨?_, ?_⟩
      · linarith
      · simpa [a] using hθx_lt
    rcases exists_rat_btwn hx_interval with ⟨r, hr⟩
    have hr_neg : (r : ℝ) < 0 := lt_of_lt_of_le hr.2 (min_le_right _ _)
    have hr_pos : 0 < -r := by
      have hr_neg_q : (r : ℚ) < 0 :=
        (Rat.cast_lt (K := ℝ)).1 (by simpa using hr_neg)
      linarith
    rcases rat_pos_exists_mn_real (-r) hr_pos with ⟨m1, n1, hm1, hn1, hr_eq⟩
    set xr : ℝ := C.g_star c hc_pos hc_lt m1 n1 hm1 hn1
    have hxr_mem : xr ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [xr] using g_star_mem m1 n1 hm1 hn1
    have hr_eq' : (r : ℝ) = - (m1 : ℝ) / n1 := by
      have hr_eq'' : -(r : ℝ) = (m1 : ℝ) / n1 := by
        simpa using hr_eq
      have hr_eq''' := congrArg (fun t => -t) hr_eq''
      simpa [neg_div] using hr_eq'''
    have hθ_xr : Θ xr = (r : ℝ) := by
      have htheta := C.Theta_extension_g_star c hc_pos hc_lt m1 n1 hm1 hn1
      simpa [Θ, xr, hr_eq'] using htheta
    have hy_interval : b < min (b + ε / 4) 0 := by
      refine (lt_min_iff).2 ?_
      refine ⟨?_, ?_⟩
      · linarith
      · simpa [b] using hθy_lt
    rcases exists_rat_btwn hy_interval with ⟨s, hs⟩
    have hs_neg : (s : ℝ) < 0 := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hs_pos : 0 < -s := by
      have hs_neg_q : (s : ℚ) < 0 :=
        (Rat.cast_lt (K := ℝ)).1 (by simpa using hs_neg)
      linarith
    rcases rat_pos_exists_mn_real (-s) hs_pos with ⟨m2, n2, hm2, hn2, hs_eq⟩
    set ys : ℝ := C.g_star c hc_pos hc_lt m2 n2 hm2 hn2
    have hys_mem : ys ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [ys] using g_star_mem m2 n2 hm2 hn2
    have hs_eq' : (s : ℝ) = - (m2 : ℝ) / n2 := by
      have hs_eq'' : -(s : ℝ) = (m2 : ℝ) / n2 := by
        simpa using hs_eq
      have hs_eq''' := congrArg (fun t => -t) hs_eq''
      simpa [neg_div] using hs_eq'''
    have hθ_ys : Θ ys = (s : ℝ) := by
      have htheta := C.Theta_extension_g_star c hc_pos hc_lt m2 n2 hm2 hn2
      simpa [Θ, ys, hs_eq'] using htheta
    have hx_lt_xr : x < xr := by
      have : Θ x < Θ xr := by simpa [a, hθ_xr] using hr.1
      exact (hmono.lt_iff_lt hx_mem hxr_mem).1 this
    have hy_lt_ys : y < ys := by
      have : Θ y < Θ ys := by simpa [b, hθ_ys] using hs.1
      exact (hmono.lt_iff_lt hy_mem hys_mem).1 this
    have hFx_lt : C.F x y < C.F xr ys := by
      have h1 : C.F x y < C.F xr y := (C.F_strictMono_left y hy_pos hy_le) hx_lt_xr
      have h2 : C.F xr y < C.F xr ys :=
        (C.F_strictMono_right xr hxr_mem.1 hxr_mem.2) hy_lt_ys
      exact lt_trans h1 h2
    have hFxy_mem : C.F x y ∈ Set.Ioc (0 : ℝ) 1 := by
      rcases C.F_range x y hx_pos hx_le hy_pos hy_le with ⟨hpos, hle⟩
      exact ⟨hpos, hle⟩
    have hFxr_mem : C.F xr ys ∈ Set.Ioc (0 : ℝ) 1 := by
      rcases C.F_range xr ys hxr_mem.1 hxr_mem.2 hys_mem.1 hys_mem.2 with ⟨hpos, hle⟩
      exact ⟨hpos, hle⟩
    have hθ_lt : Θ (C.F x y) < Θ (C.F xr ys) :=
      (hmono.lt_iff_lt hFxy_mem hFxr_mem).2 hFx_lt
    have hθ_F_eq : Θ (C.F xr ys) = (r : ℝ) + (s : ℝ) := by
      have hθ_F_gstar := theta_F_gstar m1 n1 hm1 hn1 m2 n2 hm2 hn2
      simpa [Θ, xr, ys, hr_eq', hs_eq', sub_eq_add_neg, neg_div, add_comm, add_left_comm, add_assoc]
        using hθ_F_gstar
    have hθ_lt' : Θ (C.F x y) < (r : ℝ) + (s : ℝ) := by
      simpa [hθ_F_eq] using hθ_lt
    have hr_lt : (r : ℝ) < a + ε / 4 := lt_of_lt_of_le hr.2 (min_le_left _ _)
    have hs_lt : (s : ℝ) < b + ε / 4 := lt_of_lt_of_le hs.2 (min_le_left _ _)
    have ht : Θ (C.F x y) = a + b + ε := by
      linarith [hε_def]
    have hsum_lt : (r : ℝ) + (s : ℝ) < Θ (C.F x y) := by
      linarith [hr_lt, hs_lt, ht]
    linarith [hθ_lt', hsum_lt]
  have h_lower : a + b ≤ Θ (C.F x y) := by
    by_contra hlt
    have hlt' : Θ (C.F x y) < a + b := lt_of_not_ge hlt
    set ε : ℝ := (a + b) - Θ (C.F x y) with hε_def
    have hε_pos : 0 < ε := by linarith
    have hx_interval : a - ε / 4 < a := by linarith
    rcases exists_rat_btwn hx_interval with ⟨r, hr⟩
    have hr_neg : (r : ℝ) < 0 := lt_trans hr.2 hθx_lt
    have hr_pos : 0 < -r := by
      have hr_neg_q : (r : ℚ) < 0 :=
        (Rat.cast_lt (K := ℝ)).1 (by simpa using hr_neg)
      linarith
    rcases rat_pos_exists_mn_real (-r) hr_pos with ⟨m1, n1, hm1, hn1, hr_eq⟩
    set xr : ℝ := C.g_star c hc_pos hc_lt m1 n1 hm1 hn1
    have hxr_mem : xr ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [xr] using g_star_mem m1 n1 hm1 hn1
    have hr_eq' : (r : ℝ) = - (m1 : ℝ) / n1 := by
      have hr_eq'' : -(r : ℝ) = (m1 : ℝ) / n1 := by
        simpa using hr_eq
      have hr_eq''' := congrArg (fun t => -t) hr_eq''
      simpa [neg_div] using hr_eq'''
    have hθ_xr : Θ xr = (r : ℝ) := by
      have htheta := C.Theta_extension_g_star c hc_pos hc_lt m1 n1 hm1 hn1
      simpa [Θ, xr, hr_eq'] using htheta
    have hy_interval : b - ε / 4 < b := by linarith
    rcases exists_rat_btwn hy_interval with ⟨s, hs⟩
    have hs_neg : (s : ℝ) < 0 := lt_trans hs.2 hθy_lt
    have hs_pos : 0 < -s := by
      have hs_neg_q : (s : ℚ) < 0 :=
        (Rat.cast_lt (K := ℝ)).1 (by simpa using hs_neg)
      linarith
    rcases rat_pos_exists_mn_real (-s) hs_pos with ⟨m2, n2, hm2, hn2, hs_eq⟩
    set ys : ℝ := C.g_star c hc_pos hc_lt m2 n2 hm2 hn2
    have hys_mem : ys ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [ys] using g_star_mem m2 n2 hm2 hn2
    have hs_eq' : (s : ℝ) = - (m2 : ℝ) / n2 := by
      have hs_eq'' : -(s : ℝ) = (m2 : ℝ) / n2 := by
        simpa using hs_eq
      have hs_eq''' := congrArg (fun t => -t) hs_eq''
      simpa [neg_div] using hs_eq'''
    have hθ_ys : Θ ys = (s : ℝ) := by
      have htheta := C.Theta_extension_g_star c hc_pos hc_lt m2 n2 hm2 hn2
      simpa [Θ, ys, hs_eq'] using htheta
    have hx_gt_xr : xr < x := by
      have : Θ xr < Θ x := by simpa [a, hθ_xr] using hr.2
      exact (hmono.lt_iff_lt hxr_mem hx_mem).1 this
    have hy_gt_ys : ys < y := by
      have : Θ ys < Θ y := by simpa [b, hθ_ys] using hs.2
      exact (hmono.lt_iff_lt hys_mem hy_mem).1 this
    have hFx_lt : C.F xr ys < C.F x y := by
      have h1 : C.F xr ys < C.F x ys := (C.F_strictMono_left ys hys_mem.1 hys_mem.2) hx_gt_xr
      have h2 : C.F x ys < C.F x y :=
        (C.F_strictMono_right x hx_pos hx_le) hy_gt_ys
      exact lt_trans h1 h2
    have hFxy_mem : C.F x y ∈ Set.Ioc (0 : ℝ) 1 := by
      rcases C.F_range x y hx_pos hx_le hy_pos hy_le with ⟨hpos, hle⟩
      exact ⟨hpos, hle⟩
    have hFxr_mem : C.F xr ys ∈ Set.Ioc (0 : ℝ) 1 := by
      rcases C.F_range xr ys hxr_mem.1 hxr_mem.2 hys_mem.1 hys_mem.2 with ⟨hpos, hle⟩
      exact ⟨hpos, hle⟩
    have hθ_lt : Θ (C.F xr ys) < Θ (C.F x y) :=
      (hmono.lt_iff_lt hFxr_mem hFxy_mem).2 hFx_lt
    have hθ_F_eq : Θ (C.F xr ys) = (r : ℝ) + (s : ℝ) := by
      have hθ_F_gstar := theta_F_gstar m1 n1 hm1 hn1 m2 n2 hm2 hn2
      simpa [Θ, xr, ys, hr_eq', hs_eq', sub_eq_add_neg, neg_div, add_comm, add_left_comm, add_assoc]
        using hθ_F_gstar
    have hθ_lt' : (r : ℝ) + (s : ℝ) < Θ (C.F x y) := by
      simpa [hθ_F_eq] using hθ_lt
    have hr_gt : a - ε / 4 < (r : ℝ) := hr.1
    have hs_gt : b - ε / 4 < (s : ℝ) := hs.1
    have ht : Θ (C.F x y) = a + b - ε := by
      linarith [hε_def]
    have hsum_gt : Θ (C.F x y) < (r : ℝ) + (s : ℝ) := by
      linarith [hr_gt, hs_gt, ht]
    linarith [hθ_lt', hsum_gt]
  exact le_antisymm h_upper h_lower

/-- **Aczél's Theorem** (Now Proven): For Cox axioms, there exists an additive representation.

This is the fundamental representation theorem that enables the entire Cox derivation.

**Mathematical Statement** (Aczél 1966, Chapter 6):
Given F : (0,1] × (0,1] → (0,1] satisfying:
- Associativity: F(F(x,y),z) = F(x,F(y,z))
- Strict monotonicity in each argument
- Continuity
- Identity: F(x,1) = x, F(1,y) = y

There exists a continuous, strictly monotone Θ : (0,1] → ℝ such that:
  Θ(F(x,y)) = Θ(x) + Θ(y)

**Our Proof Strategy**:
1. Construct g* on positive rationals via iteration and nth roots: g*(m/n) = iterate m (nth_root n c)
2. Prove g* satisfies: F(g*(r), g*(s)) = g*(r+s) [g_star_additive]
3. Prove g* is antitone (decreasing) [g_star_antitone]
4. Define Θ as the inverse of g*: Θ(x) = inf { r : g*(r) ≤ x }
5. Prove Θ is strictly increasing [Theta_extension_strictMono]
6. Prove Θ is continuous [Theta_extension_continuousOn]
7. Prove Θ is additive [Theta_extension_additive]

**Reference**: Aczél, J. "Lectures on Functional Equations and Their Applications" (1966),
Chapter 6, Section 2; Ling, C.H. "Representation of associative functions" (1965). -/
theorem aczel_representation_theorem :
  ∀ (C : CoxFullAxioms), ∃ Θ : ℝ → ℝ,
    StrictMonoOn Θ (Set.Ioc 0 1) ∧
    ContinuousOn Θ (Set.Ioc 0 1) ∧
    (∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → Θ (C.F x y) = Θ x + Θ y) := by
  intro C
  -- Fix a base point c ∈ (0,1)
  have ⟨c, hc_pos, hc_lt⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨(1:ℝ)/2, by norm_num, by norm_num⟩
  -- Use the Theta_extension constructed from g*
  use C.Theta_extension c hc_pos hc_lt
  refine ⟨C.Theta_extension_strictMono c hc_pos hc_lt, ?_, ?_⟩
  · -- Continuity on (0,1]
    exact C.Theta_extension_continuousOn c hc_pos hc_lt
  · -- Additivity
    intro x y hx_pos hx_le hy_pos hy_le
    exact C.Theta_extension_additive c hc_pos hc_lt x y hx_pos hx_le hy_pos hy_le

/-- Construct the additive representation from the Aczél theorem. -/
noncomputable def aczel_theorem (C : CoxFullAxioms) : AdditiveRepresentation C :=
  ⟨Classical.choose (aczel_representation_theorem C),
   (Classical.choose_spec (aczel_representation_theorem C)).1,
   (Classical.choose_spec (aczel_representation_theorem C)).2.1,
   (Classical.choose_spec (aczel_representation_theorem C)).2.2⟩

/-!
## §4: From Additive to Multiplicative Representation

Given an additive representation Θ, we construct a multiplicative representation
g = exp ∘ Θ. This gives:

  g(F(x,y)) = g(x) · g(y)

-/

/-- The multiplicative representation form.

If Θ(F(x,y)) = Θ(x) + Θ(y), then g = exp∘Θ satisfies g(F(x,y)) = g(x)·g(y).

Note: We use restricted domains since the Cox operation is only defined on (0,1]. -/
structure MultiplicativeRepresentation (C : CoxFullAxioms) where
  /-- The representation function g -/
  g : ℝ → ℝ
  /-- g is strictly positive on (0,1] -/
  g_pos : ∀ x, 0 < x → x ≤ 1 → 0 < g x
  /-- g is strictly increasing on (0,1]. -/
  g_strictMonoOn : StrictMonoOn g (Set.Ioc 0 1)
  /-- g is continuous on (0,1]. -/
  g_continuousOn : ContinuousOn g (Set.Ioc 0 1)
  /-- g represents F multiplicatively: g(F(x,y)) = g(x) · g(y) for x, y ∈ (0,1] -/
  g_multiplicative : ∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → g (C.F x y) = g x * g y

/-- Construct multiplicative representation from additive representation via exp. -/
noncomputable def multiplicativeRep_of_additiveRep (C : CoxFullAxioms)
    (hΘ : AdditiveRepresentation C) : MultiplicativeRepresentation C where
  g := fun x => Real.exp (hΘ.Θ x)
  g_pos := fun x _ _ => Real.exp_pos _
  g_strictMonoOn := fun x hx y hy hxy =>
    Real.exp_lt_exp.mpr (hΘ.Θ_strictMonoOn hx hy hxy)
  g_continuousOn := by
    -- exp ∘ Θ is continuous on (0, ∞)
    -- exp is continuous everywhere, so exp ∘ Θ is continuous where Θ is continuous
    have hexp : Continuous Real.exp := Real.continuous_exp
    exact hexp.comp_continuousOn hΘ.Θ_continuousOn
  g_multiplicative := fun x y hx_pos hx_le hy_pos hy_le => by
    rw [hΘ.Θ_additive x y hx_pos hx_le hy_pos hy_le, Real.exp_add]

/-!
## §5: Multiplicative Representation Implies Product Rule

From the multiplicative representation g(F(x,y)) = g(x)·g(y), we derive
that F must be the product rule (up to reparametrization).

The key insight: if we define p(x) = g(x)/g(1), then:
- p(1) = 1 (normalized)
- p(F(x,y)) = p(x)·p(y)

So in the "p-scale", F IS multiplication!
-/

/-- The normalized multiplicative representation satisfies p(1) = 1. -/
noncomputable def normalizedMultRep (C : CoxFullAxioms) (hM : MultiplicativeRepresentation C) :
    ℝ → ℝ :=
  fun x => hM.g x / hM.g 1

/-- The normalized representation satisfies p(1) = 1. -/
theorem normalizedMultRep_one (C : CoxFullAxioms) (hM : MultiplicativeRepresentation C) :
    normalizedMultRep C hM 1 = 1 := by
  simp only [normalizedMultRep]
  have h1 : hM.g 1 ≠ 0 := ne_of_gt (hM.g_pos 1 one_pos le_rfl)
  field_simp

/-- From the identity property F(x,1) = x and multiplicativity, g(1) = 1. -/
theorem g_one_eq_one (C : CoxFullAxioms) (hM : MultiplicativeRepresentation C) : hM.g 1 = 1 := by
  -- F(1,1) = 1 (identity property)
  have h1 : C.F 1 1 = 1 := C.F_one_right 1
  -- g(F(1,1)) = g(1) * g(1) (multiplicativity)
  have h2 : hM.g (C.F 1 1) = hM.g 1 * hM.g 1 := hM.g_multiplicative 1 1 one_pos le_rfl one_pos le_rfl
  -- So g(1) = g(1) * g(1)
  rw [h1] at h2
  -- g(1) * g(1) = g(1) means g(1) = 1 (since g(1) > 0)
  have h3 : hM.g 1 > 0 := hM.g_pos 1 one_pos le_rfl
  have h4 : hM.g 1 * hM.g 1 = hM.g 1 := h2.symm
  -- From g(1)² = g(1), we get g(1)(g(1) - 1) = 0
  -- Since g(1) > 0, we have g(1) ≠ 0, so g(1) - 1 = 0
  have h5 : hM.g 1 - 1 = 0 := by
    have : hM.g 1 ≠ 0 := ne_of_gt h3
    field_simp at h4
    linarith
  linarith

/-- The normalized representation still satisfies the multiplicative property for x, y ∈ (0,1]. -/
theorem normalizedMultRep_mul (C : CoxFullAxioms) (hM : MultiplicativeRepresentation C)
    (x y : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) (hy_pos : 0 < y) (hy_le : y ≤ 1) :
    normalizedMultRep C hM (C.F x y) = normalizedMultRep C hM x * normalizedMultRep C hM y := by
  unfold normalizedMultRep
  have h1 : hM.g 1 ≠ 0 := ne_of_gt (hM.g_pos 1 one_pos le_rfl)
  have h2 : hM.g 1 = 1 := g_one_eq_one C hM
  rw [hM.g_multiplicative x y hx_pos hx_le hy_pos hy_le, h2]
  ring

/-- **Cox's Product Rule Theorem**: In the normalized scale p, the conjunction F
becomes multiplication: p(F(x,y)) = p(x) · p(y) for x, y ∈ (0,1].

Equivalently, F(x,y) = p⁻¹(p(x) · p(y)) where p is the reparametrization.

This is Cox's main result: the product rule is FORCED by the axioms! -/
theorem productRule_in_normalized_scale (C : CoxFullAxioms) (hM : MultiplicativeRepresentation C)
    (x y : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) (hy_pos : 0 < y) (hy_le : y ≤ 1) :
    normalizedMultRep C hM (C.F x y) = normalizedMultRep C hM x * normalizedMultRep C hM y :=
  normalizedMultRep_mul C hM x y hx_pos hx_le hy_pos hy_le

/-!
## §6: The Standard Product Rule

If F is already in "standard form" (i.e., no reparametrization needed), then
F(x,y) = x·y directly.

Cox shows that by choosing the right parametrization of plausibility, we can
always achieve this standard form.
-/

/-- A conjunction rule is in standard form if it equals multiplication. -/
def IsStandardProductRule (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, F x y = x * y

/-- The standard product rule F(x,y) = x·y satisfies all of Cox's axioms. -/
def standard_productRule_satisfies_cox : CoxFullAxioms where
  F := fun x y => x * y
  F_range := fun x y hx hxle hy hyle => by
    constructor
    · exact mul_pos hx hy
    · calc x * y ≤ 1 * y := by apply mul_le_mul_of_nonneg_right hxle (le_of_lt hy)
        _ = y := one_mul y
        _ ≤ 1 := hyle
  F_assoc := fun x y z => by ring
  F_one_right := fun x => by ring
  F_one_left := fun y => by ring
  F_strictMono_left := fun z hz _ => strictMono_mul_right_of_pos hz
  F_strictMono_right := fun z hz _ => strictMono_mul_left_of_pos hz
  F_continuous := continuous_mul

/-- For the standard product rule, the identity IS the multiplicative representation. -/
def standard_productRule_multRep : MultiplicativeRepresentation standard_productRule_satisfies_cox where
  g := id
  g_pos := fun _ hx _ => hx
  g_strictMonoOn := fun _ _ _ _ hxy => hxy
  g_continuousOn := continuous_id.continuousOn
  g_multiplicative := fun _ _ _ _ _ _ => rfl

/-- For the standard product rule F(x,y) = x*y, log provides the additive representation.

This demonstrates that the Aczél theorem is satisfiable, and shows the concrete form of Θ
when F is standard multiplication. -/
noncomputable def standard_productRule_additiveRep : AdditiveRepresentation standard_productRule_satisfies_cox where
  Θ := Real.log
  Θ_strictMonoOn := by
    intro x hx y hy hxy
    exact Real.strictMonoOn_log hx.1 hy.1 hxy
  Θ_continuousOn :=
    Real.continuousOn_log.mono (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx.1))
  Θ_additive := fun x y hx_pos _ hy_pos _ => by
    simp only [standard_productRule_satisfies_cox]
    exact Real.log_mul (ne_of_gt hx_pos) (ne_of_gt hy_pos)

end CoxFullAxioms

/-!
## §7: Main Theorem - Cox's Derivation of the Product Rule

We now state the complete Cox theorem: any conjunction function satisfying
Cox's axioms is equivalent to the standard product rule.
-/

/-- **Cox's Theorem (Product Rule)**:

Any conjunction function F satisfying:
1. Associativity: F(F(x,y),z) = F(x,F(y,z))
2. Identity: F(1,y) = y, F(x,1) = x
3. Monotonicity: F is strictly increasing in each argument
4. Continuity: F is continuous

admits a reparametrization p such that p(F(x,y)) = p(x)·p(y) for x, y ∈ (0,1].

In other words, F IS multiplication in the right coordinate system.

This is the foundational result that justifies using multiplication
for combining probabilities. -/
theorem cox_productRule (C : CoxFullAxioms) :
    ∃ p : ℝ → ℝ, StrictMonoOn p (Set.Ioc 0 1) ∧ ContinuousOn p (Set.Ioc 0 1) ∧
      (∀ x y, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → p (C.F x y) = p x * p y) ∧ p 1 = 1 := by
  -- Get the additive representation from Aczél's theorem
  let hΘ := CoxFullAxioms.aczel_theorem C
  -- Convert to multiplicative representation via exp
  let hM := CoxFullAxioms.multiplicativeRep_of_additiveRep C hΘ
  -- Use the normalized multiplicative representation
  use CoxFullAxioms.normalizedMultRep C hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- StrictMonoOn (0,1]
    intro x hx y hy hxy
    unfold CoxFullAxioms.normalizedMultRep
    have h1 : 0 < hM.g 1 := hM.g_pos 1 one_pos le_rfl
    exact div_lt_div_of_pos_right (hM.g_strictMonoOn hx hy hxy) h1
  · -- ContinuousOn (0,1]
    unfold CoxFullAxioms.normalizedMultRep
    have h1 : hM.g 1 ≠ 0 := ne_of_gt (hM.g_pos 1 one_pos le_rfl)
    exact hM.g_continuousOn.div_const (hM.g 1)
  · -- Multiplicative property for x, y ∈ (0,1]
    exact fun x y hx_pos hx_le hy_pos hy_le =>
      CoxFullAxioms.normalizedMultRep_mul C hM x y hx_pos hx_le hy_pos hy_le
  · -- p(1) = 1
    exact CoxFullAxioms.normalizedMultRep_one C hM

/-!
## §8: Commutativity is Derived

A key insight: commutativity F(x,y) = F(y,x) is NOT assumed but DERIVED!

This follows from the multiplicative representation: since multiplication
on ℝ is commutative, and p is injective, F must be commutative.

Note: The same associativity functional equation appears in Knuth-Skilling's
work on ordered semigroups. Both derive commutativity as a theorem.
-/

/-- Cox's commutativity theorem: F(x,y) = F(y,x) is DERIVED from the axioms for x, y ∈ (0,1].

This follows immediately from the multiplicative representation:
p(F(x,y)) = p(x)·p(y) = p(y)·p(x) = p(F(y,x))
and since p is injective on (0,∞), F(x,y) = F(y,x). -/
theorem cox_commutativity (C : CoxFullAxioms)
    (x y : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) (hy_pos : 0 < y) (hy_le : y ≤ 1) :
    C.F x y = C.F y x := by
  obtain ⟨p, hp_mono, _, hp_mul, _⟩ := cox_productRule C
  -- F(x,y) and F(y,x) are in (0,1]
  have hFxy := C.F_range x y hx_pos hx_le hy_pos hy_le
  have hFyx := C.F_range y x hy_pos hy_le hx_pos hx_le
  have h1 : p (C.F x y) = p x * p y := hp_mul x y hx_pos hx_le hy_pos hy_le
  have h2 : p (C.F y x) = p y * p x := hp_mul y x hy_pos hy_le hx_pos hx_le
  have h3 : p x * p y = p y * p x := mul_comm (p x) (p y)
  have h4 : p (C.F x y) = p (C.F y x) := by rw [h1, h3, ← h2]
  exact hp_mono.injOn ⟨hFxy.1, hFxy.2⟩ ⟨hFyx.1, hFyx.2⟩ h4

/-!
## §9: The Negation Rule Derivation

Cox also derives the negation rule G(x) = 1 - x from similar functional equation
analysis. The key equation is:

  G(G(x)) = x (involution)
  F(x, G(x)) + x·1 = x (when conditioning on certainty)

Combined with continuity and monotonicity, this forces G(x) = 1 - x.
-/

/-!
## §8: Cox's Negation Functional Equation

Following Cox (1961) Eq. (4.4), the product/negation interaction yields the
functional equation:

  z * G(G y / z) = y * G(G z / y)

for y, z > 0 (after regrading to the product-rule scale).
-/

/-- Cox's negation functional equation (Eq. 4.4). -/
def CoxNegationEquation (G : ℝ → ℝ) : Prop :=
  ∀ y z, 0 < y → 0 < z → z * G (G y / z) = y * G (G z / y)

lemma standard_negationRule_eq_4_4 (y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
    z * standardNegationRule (standardNegationRule y / z) =
      y * standardNegationRule (standardNegationRule z / y) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp [standardNegationRule]
  field_simp [hy0, hz0]
  ring

/-- Cox's negation axioms.

**Important**: The standalone involution axioms (G(G(x)) = x, strict anti-monotonicity, boundary
conditions) do NOT uniquely determine G(x) = 1 - x. For example, G(x) = √(1-x²) also satisfies
all those properties.

Cox's actual derivation uses the **interaction** between the product rule and negation rule, which
reduces to the functional equation Eq. (4.4) below. Under differentiability assumptions, Cox shows
that this forces the 1-parameter family:

  G(x) = (1 - x^r)^(1/r),   r > 0

and then a regraduation by x ↦ x^r yields the standard negation rule. -/
structure CoxNegationAxioms where
  /-- The negation function G(x) = p(¬A|B) when p(A|B) = x -/
  G : ℝ → ℝ
  /-- G maps [0,1] to [0,1] -/
  G_range : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ G x ∧ G x ≤ 1
  /-- G is strictly decreasing -/
  G_strictAnti : StrictAnti G
  /-- G is continuous -/
  G_continuous : Continuous G
  /-- G is twice continuously differentiable on (0,∞). -/
  G_contDiff : ContDiffOn ℝ 2 G (Set.Ioi 0)
  /-- G(0) = 1 (impossible becomes certain) -/
  G_zero : G 0 = 1
  /-- G(1) = 0 (certain becomes impossible) -/
  G_one : G 1 = 0
  /-- G is an involution: G(G(x)) = x -/
  G_involution : ∀ x, G (G x) = x
  /-- Cox's negation functional equation (Eq. 4.4). -/
  G_eq_4_4 : CoxNegationEquation G
  /-- G' never vanishes on (0,∞) (Cox divides by f'). -/
  G_deriv_ne_zero : ∀ x, 0 < x → deriv G x ≠ 0

/-- The standard negation rule G(x) = 1 - x satisfies Cox's negation axioms. -/
def standard_negationRule_satisfies_cox : CoxNegationAxioms where
  G := fun x => 1 - x
  G_range := fun x hx hxle => by constructor <;> linarith
  G_strictAnti := fun _ _ h => by linarith
  G_continuous := continuous_const.sub continuous_id
  G_contDiff := by
    -- Smoothness on (0,∞) is inherited from global smoothness.
    simpa using (contDiff_const.sub contDiff_id).contDiffOn
  G_zero := by norm_num
  G_one := by norm_num
  G_involution := fun x => by ring
  G_eq_4_4 := fun y z hy hz => standard_negationRule_eq_4_4 y z hy hz
  G_deriv_ne_zero := by
    intro x hx
    -- deriv (1 - x) = -1 ≠ 0
    have h : deriv (fun x : ℝ => 1 - x) x = (-1 : ℝ) := by
      simpa using (deriv_const_sub (f := fun x : ℝ => x) (c := (1 : ℝ)) (x := x))
    have hne : (deriv (fun x : ℝ => 1 - x) x) ≠ 0 := by
      simp [h]
    simpa using hne

namespace CoxNegationAxioms

variable (N : CoxNegationAxioms)

/-- The function g(x) = G(x) - x is continuous and strictly decreasing. -/
theorem g_continuous : Continuous (fun x => N.G x - x) :=
  N.G_continuous.sub continuous_id

theorem g_strictAnti : StrictAnti (fun x => N.G x - x) := fun x y hxy => by
  have h1 : N.G x > N.G y := N.G_strictAnti hxy
  linarith

/-- g(0) = 1 > 0 -/
theorem g_zero : N.G 0 - 0 = 1 := by simp [N.G_zero]

/-- g(1) = -1 < 0 -/
theorem g_one : N.G 1 - 1 = -1 := by simp [N.G_one]

/-- G has exactly one fixed point in (0,1), by IVT + strict anti-monotonicity. -/
theorem exists_unique_fixed_point : ∃! p, p ∈ Set.Ioo (0 : ℝ) 1 ∧ N.G p = p := by
  -- Existence: g(0) = 1 > 0, g(1) = -1 < 0, g continuous, so ∃ p with g(p) = 0
  have hg_cont : ContinuousOn (fun x => N.G x - x) (Set.Icc 0 1) :=
    N.g_continuous.continuousOn
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  -- 0 ∈ Ioo (g 1) (g 0) = Ioo (-1) 1
  have h0_in : (0 : ℝ) ∈ Set.Ioo (N.G 1 - 1) (N.G 0 - 0) := by
    simp only [N.g_zero, N.g_one, Set.mem_Ioo]
    constructor <;> norm_num
  -- intermediate_value_Ioo' gives us a point in Ioo 0 1 mapping to 0
  have hivt := intermediate_value_Ioo' hab hg_cont
  obtain ⟨p, hp_mem, hp_eq⟩ := hivt h0_in
  use p
  constructor
  · exact ⟨hp_mem, sub_eq_zero.mp hp_eq⟩
  -- Uniqueness: if G(q) = q and q ≠ p, then g(q) = 0 = g(p), contradicting strict anti
  intro q ⟨hq_mem, hq_fix⟩
  by_contra hne
  have hgp : N.G p - p = 0 := hp_eq
  have hgq : N.G q - q = 0 := sub_eq_zero.mpr hq_fix
  rcases Ne.lt_or_gt hne with hpq | hqp
  · have := N.g_strictAnti hpq
    linarith
  · have := N.g_strictAnti hqp
    linarith

/-
## Analytic consequences of Eq. (4.4)

We now follow Cox's differentiability-based derivation to solve the negation
functional equation and show that G must be a power-law regrading of the
standard negation rule.
-/

local notation "G" => N.G
local notation "G'" => deriv N.G
local notation "G''" => deriv (deriv N.G)

/-- G maps (0,1) into (0,1). -/
theorem G_mem_Ioo_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    G x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hlt0 : G 1 < G x := N.G_strictAnti hx1
  have hlt1 : G x < G 0 := N.G_strictAnti hx0
  have hpos : 0 < G x := by simpa [N.G_one] using hlt0
  have hlt : G x < 1 := by simpa [N.G_zero] using hlt1
  exact ⟨hpos, hlt⟩

theorem G_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < G x :=
  (N.G_mem_Ioo_of_mem_Ioo hx).1

theorem G_lt_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : G x < 1 :=
  (N.G_mem_Ioo_of_mem_Ioo hx).2

theorem G_ne_zero_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : G x ≠ 0 :=
  ne_of_gt (N.G_pos_of_mem_Ioo hx)

/-- Differentiability of G on (0,∞). -/
theorem G_differentiableAt {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ G x := by
  have hdiff : DifferentiableOn ℝ G (Set.Ioi 0) :=
    (N.G_contDiff.differentiableOn (by decide))
  have hxmem : Set.Ioi 0 ∈ 𝓝 x := (isOpen_Ioi.mem_nhds hx)
  exact hdiff.differentiableAt hxmem

/-- Differentiability of G' on (0,∞). -/
theorem G'_differentiableAt {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ G' x := by
  have hcont : ContDiffOn ℝ 1 G' (Set.Ioi 0) :=
    N.G_contDiff.deriv_of_isOpen (s₂ := Set.Ioi 0) (m := 1) (n := 2) isOpen_Ioi (by decide)
  have hdiff : DifferentiableOn ℝ G' (Set.Ioi 0) :=
    (hcont.differentiableOn (by decide))
  have hxmem : Set.Ioi 0 ∈ 𝓝 x := (isOpen_Ioi.mem_nhds hx)
  exact hdiff.differentiableAt hxmem

/-- G is strictly decreasing, hence its derivative is strictly negative on (0,∞). -/
theorem deriv_G_neg {x : ℝ} (hx : 0 < x) : G' x < 0 := by
  have hnonpos : G' x ≤ 0 := (Antitone.deriv_nonpos (N.G_strictAnti.antitone))
  exact lt_of_le_of_ne hnonpos (N.G_deriv_ne_zero x hx)

/-- Positivity of the denominator G x - x·G'(x). -/
theorem G_sub_x_deriv_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < G x - x * G' x := by
  have hGpos : 0 < G x := N.G_pos_of_mem_Ioo hx
  have hderivneg : G' x < 0 := N.deriv_G_neg hx.1
  have hxpos : 0 < x := hx.1
  have hpos : 0 < -x * G' x := by
    have : 0 < -G' x := by linarith
    nlinarith
  have hsum : 0 < G x + (-x * G' x) := add_pos hGpos hpos
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Existence of a preimage in (0,1) for any u ∈ (0,1). -/
theorem exists_preimage_Ioo {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ y, y ∈ Set.Ioo (0 : ℝ) 1 ∧ G y = u := by
  have hcont : ContinuousOn (fun x => G x - u) (Set.Icc 0 1) :=
    (N.G_continuous.sub continuous_const).continuousOn
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have h0_in : (0 : ℝ) ∈ Set.Ioo (G 1 - u) (G 0 - u) := by
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have h0_in' : (0 : ℝ) ∈ Set.Ioo (-u) (1 - u) := by
      constructor <;> linarith
    simpa [N.G_zero, N.G_one, Set.mem_Ioo] using h0_in'
  have hivt := intermediate_value_Ioo' hab hcont
  obtain ⟨y, hy_mem, hy_eq⟩ := hivt h0_in
  refine ⟨y, hy_mem, ?_⟩
  exact sub_eq_zero.mp hy_eq

/-- For fixed u ∈ (0,1), any v ∈ (0,1) is realized by some y,z with
    u = G y / z and v = G z / y. -/
theorem exists_yz_of_uv {u v : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ y z, y ∈ Set.Ioo (0 : ℝ) 1 ∧ z ∈ Set.Ioo (0 : ℝ) 1 ∧ u = G y / z ∧ v = G z / y := by
  obtain ⟨y0, hy0, hy0eq⟩ := N.exists_preimage_Ioo hu
  let vfun : ℝ → ℝ := fun y => G (G y / u) / y
  have hy0pos : 0 < y0 := hy0.1
  have hcont1 : ContinuousOn (fun y => G y / u) (Set.Icc y0 1) := by
    exact (N.G_continuous.div_const u).continuousOn
  have hcont2 : ContinuousOn (fun y => G (G y / u)) (Set.Icc y0 1) := by
    exact (N.G_continuous.comp (N.G_continuous.div_const u)).continuousOn
  have hcont : ContinuousOn vfun (Set.Icc y0 1) := by
    refine hcont2.div continuousOn_id ?_
    intro y hy
    have hy' : 0 < y := lt_of_lt_of_le hy0pos hy.1
    exact ne_of_gt hy'
  have hv0 : vfun y0 = 0 := by
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    simp [vfun, hy0eq, hu0, N.G_one]
  have hv1 : vfun 1 = 1 := by
    simp [vfun, N.G_one, N.G_zero]
  have hvIcc : v ∈ Set.Icc (vfun y0) (vfun 1) := by
    simpa [hv0, hv1] using ⟨hv.1.le, hv.2.le⟩
  have hy0le : y0 ≤ (1 : ℝ) := hy0.2.le
  have hmem := (intermediate_value_Icc hy0le hcont) hvIcc
  rcases hmem with ⟨y, hyIcc, hyEq⟩
  have hne_y0 : y ≠ y0 := by
    intro h
    subst h
    have hv0' : 0 = v := by simpa [hv0] using hyEq
    exact (ne_of_gt hv.1) hv0'.symm
  have hne_1 : y ≠ 1 := by
    intro h
    subst h
    have hv1' : 1 = v := by simpa [hv1] using hyEq
    exact (ne_of_lt hv.2) hv1'.symm
  have hyIoo : y ∈ Set.Ioo y0 1 := by
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hyIcc.1 hne_y0.symm
    · exact lt_of_le_of_ne hyIcc.2 hne_1
  have hyIoo01 : y ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_trans hy0.1 hyIoo.1, hyIoo.2⟩
  let z : ℝ := G y / u
  have hzpos : 0 < z := by
    have hGpos : 0 < G y := N.G_pos_of_mem_Ioo hyIoo01
    exact div_pos hGpos hu.1
  have hzlt1 : z < 1 := by
    have hygt : y0 < y := hyIoo.1
    have hGlt : G y < G y0 := N.G_strictAnti hygt
    have hGle : G y0 = u := hy0eq
    have hGlt' : G y < u := by simpa [hGle] using hGlt
    have hu0 : 0 < u := hu.1
    have hdiv : G y / u < 1 := by
      have : G y < u := hGlt'
      exact (div_lt_one hu0).2 this
    simpa [z] using hdiv
  refine ⟨y, z, hyIoo01, ⟨hzpos, hzlt1⟩, ?_, ?_⟩
  · have hu0 : u ≠ 0 := ne_of_gt hu.1
    have hGy0 : G y ≠ 0 := N.G_ne_zero_of_mem_Ioo hyIoo01
    have : G y / z = u := by
      calc
        G y / z = G y / (G y / u) := by simp [z]
        _ = u := by field_simp [hGy0, hu0]
    simp [this]
  · simpa [vfun, z] using hyEq.symm

/-- First derivative consequence of Eq. (4.4). -/
theorem deriv_eq4_4_y {y z : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    G' (G y / z) * G' y = G (G z / y) - (G z / y) * G' (G z / y) := by
  let f : ℝ → ℝ := fun y => z * G (G y / z)
  let g : ℝ → ℝ := fun y => y * G (G z / y)
  have hEqOn : Set.EqOn f g (Set.Ioi 0) := by
    intro y hy'
    exact N.G_eq_4_4 y z hy' hz.1
  have hEq : f =ᶠ[𝓝 y] g := by
    have hy' : y ∈ Set.Ioi 0 := hy.1
    have hnhds : ∀ᶠ x in 𝓝 y, x ∈ Set.Ioi 0 := (isOpen_Ioi.mem_nhds hy')
    exact hnhds.mono (by intro x hx; exact hEqOn hx)
  have hderiv : deriv f y = deriv g y := hEq.deriv_eq
  have hypos : 0 < y := hy.1
  have hzpos : 0 < z := hz.1
  have hGpos : 0 < G y := N.G_pos_of_mem_Ioo hy
  have hGzpos : 0 < G z := N.G_pos_of_mem_Ioo hz
  have hdiff_inner : DifferentiableAt ℝ (fun y => G y / z) y :=
    (N.G_differentiableAt hypos).div_const z
  have hdiff_outer : DifferentiableAt ℝ G (G y / z) := by
    have hpos : 0 < G y / z := div_pos hGpos hzpos
    exact N.G_differentiableAt hpos
  have hderiv_inner : deriv (fun y => G y / z) y = G' y / z := by
    exact (deriv_div_const (c := G) (d := z) (x := y))
  have hderiv_comp : deriv (fun y => G (G y / z)) y =
      G' (G y / z) * (G' y / z) := by
    simpa [Function.comp, hderiv_inner] using (deriv_comp y hdiff_outer hdiff_inner)
  have hderiv_f_simp : deriv f y = G' (G y / z) * G' y := by
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    calc
      deriv f y = z * (G' (G y / z) * (G' y / z)) := by
        simp [f, hderiv_comp, deriv_const_mul_field]
      _ = G' (G y / z) * G' y := by
        field_simp [hz0, mul_comm, mul_left_comm, mul_assoc]
  -- derivative of g
  have hdiff_inner' : DifferentiableAt ℝ (fun y => G z / y) y := by
    have hdiff_const : DifferentiableAt ℝ (fun y => G z) y := differentiableAt_const _
    have hdiff_id : DifferentiableAt ℝ (fun y => y) y := differentiableAt_id
    exact hdiff_const.div hdiff_id (ne_of_gt hypos)
  have hderiv_inner' : deriv (fun y => G z / y) y = -(G z) / y ^ 2 := by
    have hdiff_const : DifferentiableAt ℝ (fun y => G z) y := differentiableAt_const _
    have hdiff_id : DifferentiableAt ℝ (fun y => y) y := differentiableAt_id
    have hy0 : y ≠ 0 := ne_of_gt hypos
    simpa using (deriv_fun_div (hc := hdiff_const) (hd := hdiff_id) hy0)
  have hdiff_outer' : DifferentiableAt ℝ G (G z / y) := by
    have hpos : 0 < G z / y := div_pos hGzpos hypos
    exact N.G_differentiableAt hpos
  have hderiv_comp' : deriv (fun y => G (G z / y)) y =
      G' (G z / y) * (-(G z) / y ^ 2) := by
    simpa [Function.comp, hderiv_inner'] using (deriv_comp y hdiff_outer' hdiff_inner')
  have hderiv_g : deriv g y =
      G (G z / y) - (G z / y) * G' (G z / y) := by
    have hdiff1 : DifferentiableAt ℝ (fun y => y) y := differentiableAt_id
    have hdiff2 : DifferentiableAt ℝ (fun y => G (G z / y)) y := hdiff_outer'.comp y hdiff_inner'
    have hmul : deriv g y =
        G (G z / y) + y * (G' (G z / y) * (-(G z) / y ^ 2)) := by
      simpa [g, hderiv_comp'] using (deriv_mul hdiff1 hdiff2)
    have hy0 : y ≠ 0 := ne_of_gt hypos
    calc
      deriv g y = G (G z / y) + y * (G' (G z / y) * (-(G z) / y ^ 2)) := hmul
      _ = G (G z / y) + (- (G z / y) * G' (G z / y)) := by
        have hmul' :
            y * (G' (G z / y) * (-(G z) / y ^ 2)) = - (G z / y) * G' (G z / y) := by
          field_simp [hy0, mul_comm, mul_left_comm, mul_assoc]
        simp [hmul']
      _ = G (G z / y) - (G z / y) * G' (G z / y) := by ring
  -- conclude
  simpa [hderiv_f_simp, hderiv_g] using hderiv

/-- Second derivative consequence of Eq. (4.4). -/
theorem deriv_eq4_4_yz {y z : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    (G y / z) * G'' (G y / z) * (G' y / z) =
      (G z / y) * G'' (G z / y) * (G' z / y) := by
  let f : ℝ → ℝ := fun z => G' (G y / z) * G' y
  let g : ℝ → ℝ := fun z => G (G z / y) - (G z / y) * G' (G z / y)
  have hEqOn : Set.EqOn f g (Set.Ioo 0 1) := by
    intro z hz'
    exact N.deriv_eq4_4_y hy hz'
  have hEq : f =ᶠ[𝓝 z] g := by
    have hz' : z ∈ Set.Ioo 0 1 := hz
    have hnhds : ∀ᶠ x in 𝓝 z, x ∈ Set.Ioo 0 1 := (isOpen_Ioo.mem_nhds hz')
    exact hnhds.mono (by intro x hx; exact hEqOn hx)
  have hderiv : deriv f z = deriv g z := hEq.deriv_eq
  have hypos : 0 < y := hy.1
  have hzpos : 0 < z := hz.1
  have hGypos : 0 < G y := N.G_pos_of_mem_Ioo hy
  have hGzpos : 0 < G z := N.G_pos_of_mem_Ioo hz
  -- compute deriv f
  have hdiff_inner : DifferentiableAt ℝ (fun z => G y / z) z := by
    have hdiff_const : DifferentiableAt ℝ (fun z => G y) z := differentiableAt_const _
    have hdiff_id : DifferentiableAt ℝ (fun z => z) z := differentiableAt_id
    exact hdiff_const.div hdiff_id (ne_of_gt hzpos)
  have hdiff_outer : DifferentiableAt ℝ G' (G y / z) := by
    have hpos : 0 < G y / z := div_pos hGypos hzpos
    exact N.G'_differentiableAt hpos
  have hderiv_inner : deriv (fun z => G y / z) z = -(G y) / z ^ 2 := by
    have hdiff_const : DifferentiableAt ℝ (fun z => G y) z := differentiableAt_const _
    have hdiff_id : DifferentiableAt ℝ (fun z => z) z := differentiableAt_id
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    simpa using (deriv_fun_div (hc := hdiff_const) (hd := hdiff_id) hz0)
  have hderiv_comp : deriv (fun z => G' (G y / z)) z =
      G'' (G y / z) * (-(G y) / z ^ 2) := by
    simpa [Function.comp, hderiv_inner] using (deriv_comp z hdiff_outer hdiff_inner)
  have hderiv_f_simp : deriv f z = -(G y / z) * G'' (G y / z) * (G' y / z) := by
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    calc
      deriv f z = G'' (G y / z) * (-(G y) / z ^ 2) * G' y := by
        simp [f, hderiv_comp, mul_comm]
      _ = -(G y / z) * G'' (G y / z) * (G' y / z) := by
        field_simp [hz0, mul_comm, mul_left_comm, mul_assoc]
  -- compute deriv g
  have hdiff_inner' : DifferentiableAt ℝ (fun z => G z / y) z :=
    (N.G_differentiableAt hzpos).div_const y
  have hdiff_outer' : DifferentiableAt ℝ G (G z / y) := by
    have hpos : 0 < G z / y := div_pos hGzpos hypos
    exact N.G_differentiableAt hpos
  have hderiv_inner' : deriv (fun z => G z / y) z = G' z / y := by
    exact (deriv_div_const (c := G) (d := y) (x := z))
  have hderiv_comp' : deriv (fun z => G (G z / y)) z =
      G' (G z / y) * (G' z / y) := by
    simpa [Function.comp, hderiv_inner'] using (deriv_comp z hdiff_outer' hdiff_inner')
  have hdiff_outer'' : DifferentiableAt ℝ G' (G z / y) := by
    have hpos : 0 < G z / y := div_pos hGzpos hypos
    exact N.G'_differentiableAt hpos
  have hderiv_comp'' : deriv (fun z => G' (G z / y)) z =
      G'' (G z / y) * (G' z / y) := by
    simpa [Function.comp, hderiv_inner'] using (deriv_comp z hdiff_outer'' hdiff_inner')
  have hderiv_g_simp : deriv g z = -(G z / y) * G'' (G z / y) * (G' z / y) := by
    have hdiff1 : DifferentiableAt ℝ (fun z => G (G z / y)) z := hdiff_outer'.comp z hdiff_inner'
    have hdiff_d : DifferentiableAt ℝ (fun z => G' (G z / y)) z := by
      simpa [Function.comp] using (hdiff_outer''.comp z hdiff_inner')
    have hdiff2 : DifferentiableAt ℝ (fun z => (G z / y) * G' (G z / y)) z :=
      hdiff_inner'.mul hdiff_d
    have hderiv_prod : deriv (fun z => (G z / y) * G' (G z / y)) z =
        (G' z / y) * G' (G z / y) + (G z / y) * (G'' (G z / y) * (G' z / y)) := by
      have hderiv_c : deriv (fun z => G z / y) z = G' z / y := by
        exact (deriv_div_const (c := G) (d := y) (x := z))
      have hderiv_d : deriv (fun z => G' (G z / y)) z = G'' (G z / y) * (G' z / y) := hderiv_comp''
      simpa [hderiv_c, hderiv_d, mul_comm, mul_left_comm, mul_assoc] using
        (deriv_mul (c := fun z => G z / y) (d := fun z => G' (G z / y)) hdiff_inner' hdiff_d)
    have hderiv_g' : deriv g z =
        (G' (G z / y) * (G' z / y)) -
          ((G' z / y) * G' (G z / y) + (G z / y) * (G'' (G z / y) * (G' z / y))) := by
      simp [g, hderiv_comp', hderiv_prod, hdiff1, hdiff2]
    calc
      deriv g z =
          (G' (G z / y) * (G' z / y)) -
            ((G' z / y) * G' (G z / y) + (G z / y) * (G'' (G z / y) * (G' z / y))) := hderiv_g'
      _ = -(G z / y) * G'' (G z / y) * (G' z / y) := by ring
  -- conclude
  simpa [hderiv_f_simp, hderiv_g_simp] using hderiv

/-- The key functional equation implies a constant Φ on (0,1). -/
theorem phi_const :
    ∃ c : ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      (x * G'' x * G x) / (G' x * (G x - x * G' x)) = c := by
  classical
  -- Use the realizability lemma to show Φ(u) = Φ(v) for all u,v ∈ (0,1).
  have hphi_eq : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      (u * G'' u * G u) / (G' u * (G u - u * G' u)) =
        (v * G'' v * G v) / (G' v * (G v - v * G' v)) := by
    intro u hu v hv
    obtain ⟨y, z, hy, hz, huEq, hvEq⟩ := N.exists_yz_of_uv hu hv
    have h1 := N.deriv_eq4_4_y hy hz
    have h2 := N.deriv_eq4_4_y (y := z) (z := y) hz hy
    have h3 := N.deriv_eq4_4_yz hy hz
    -- Expand definitions
    have hypos : 0 < y := hy.1
    have hzpos : 0 < z := hz.1
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    have hv0 : v ≠ 0 := ne_of_gt hv.1
    -- Define u = G y / z and v = G z / y
    -- Use Eq. (4.4) to eliminate y and z and obtain Φ(u)=Φ(v)
    have hEq : (u * G'' u * G u) / (G' u * (G u - u * G' u)) =
        (v * G'' v * G v) / (G' v * (G v - v * G' v)) := by
      -- Rewrite u and v and simplify
      -- This is algebraic manipulation of h1, h2, h3 together with z * G u = y * G v.
      -- We use `field_simp` to clear denominators.
      have hdenu : G' u * (G u - u * G' u) ≠ 0 := by
        have h1' : G' u ≠ 0 := N.G_deriv_ne_zero u hu.1
        have h2' : 0 < G u - u * G' u := N.G_sub_x_deriv_pos hu
        exact mul_ne_zero h1' (ne_of_gt h2')
      have hdenv : G' v * (G v - v * G' v) ≠ 0 := by
        have h1' : G' v ≠ 0 := N.G_deriv_ne_zero v hv.1
        have h2' : 0 < G v - v * G' v := N.G_sub_x_deriv_pos hv
        exact mul_ne_zero h1' (ne_of_gt h2')
      -- Start from the second-derivative equation
      have h4 : (u * G'' u * G' y) / z = (v * G'' v * G' z) / y := by
        -- rewrite h3 using u,v
        simpa [huEq, hvEq, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h3
      have h1' : G' u * G' y = G v - v * G' v := by
        simpa [huEq, hvEq] using h1
      have h2' : G' v * G' z = G u - u * G' u := by
        simpa [huEq, hvEq] using h2
      have h1'' : G' y * G' u = G v - v * G' v := by
        simpa [mul_comm] using h1'
      have h2'' : G' z * G' v = G u - u * G' u := by
        simpa [mul_comm] using h2'
      have hG'u : G' u ≠ 0 := N.G_deriv_ne_zero u hu.1
      have hG'v : G' v ≠ 0 := N.G_deriv_ne_zero v hv.1
      have h5 : G' y = (G v - v * G' v) / G' u := by
        calc
          G' y = (G' y * G' u) / G' u := by field_simp [hG'u]
          _ = (G v - v * G' v) / G' u := by simp [h1'']
      have h6 : G' z = (G u - u * G' u) / G' v := by
        calc
          G' z = (G' z * G' v) / G' v := by field_simp [hG'v]
          _ = (G u - u * G' u) / G' v := by simp [h2'']
      -- Use Eq. (4.4) to relate y and z.
      have h4' : u * G'' u * (G v - v * G' v) / (G' u * z) =
          v * G'' v * (G u - u * G' u) / (G' v * y) := by
        -- substitute h5 and h6 into h4
        have hy0 : y ≠ 0 := ne_of_gt hypos
        have hz0 : z ≠ 0 := ne_of_gt hzpos
        have h4'' :
            u * G'' u * ((G v - v * G' v) / G' u) / z =
              v * G'' v * ((G u - u * G' u) / G' v) / y := by
          simpa [h5, h6] using h4
        -- clear denominators
        have h4''' := h4''
        field_simp [hG'u, hG'v, hy0, hz0] at h4'''
        field_simp [hG'u, hG'v, hy0, hz0]
        exact h4'''
      have hzy : z / y = G v / G u := by
        -- from Eq. (4.4)
        have h0 := N.G_eq_4_4 y z hypos hzpos
        -- rewrite u,v
        have h0' : z * G u = y * G v := by simpa [huEq, hvEq] using h0
        have hy0 : y ≠ 0 := ne_of_gt hypos
        have hGu0 : G u ≠ 0 := N.G_ne_zero_of_mem_Ioo hu
        calc
          z / y = (z * G u) / (y * G u) := by field_simp [hy0, hGu0]
          _ = (y * G v) / (y * G u) := by simp [h0']
          _ = G v / G u := by field_simp [hy0, hGu0]
      -- Finish the algebra
      have hfin : u * G'' u * G u / (G' u * (G u - u * G' u)) =
          v * G'' v * G v / (G' v * (G v - v * G' v)) := by
        -- eliminate y and z using hzy and rearrange
        have hy0 : y ≠ 0 := ne_of_gt hypos
        have hGu0 : G u ≠ 0 := N.G_ne_zero_of_mem_Ioo hu
        have hGv0 : G v ≠ 0 := N.G_ne_zero_of_mem_Ioo hv
        have hzy' : z = y * G v / G u := by
          have hzy' : z / y = G v / G u := hzy
          calc
            z = (z / y) * y := by field_simp [hy0]
            _ = (G v / G u) * y := by simp [hzy']
            _ = y * G v / G u := by ring
        have h4'' : u * G'' u * (G v - v * G' v) / (G' u * (y * G v / G u)) =
            v * G'' v * (G u - u * G' u) / (G' v * y) := by
          simpa [hzy'] using h4'
        -- clear denominators and rearrange
        have h4''' := h4''
        field_simp [hdenu, hdenv, hy0, hGu0, hGv0] at h4'''
        -- use cross-multiplication form
        apply (div_eq_div_iff hdenu hdenv).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using h4'''
      exact hfin
    simpa [huEq, hvEq] using hEq
  -- Choose c at x = 1/2
  refine ⟨( ( ( (1/2 : ℝ) * G'' (1/2) * G (1/2) ) / (G' (1/2) * (G (1/2) - (1/2) * G' (1/2))) ) ), ?_⟩
  intro x hx
  have hx0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  exact (hphi_eq (1/2) hx0 x hx).symm

/-- Cox's negation functional equation yields the power-family form
    `G(x)^r + x^r = 1` for some `r > 0`. -/
theorem negation_power_family :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, (G x) ^ r + x ^ r = 1 := by
  classical
  obtain ⟨c, hc⟩ := N.phi_const
  let r : ℝ := c + 1
  let H : ℝ → ℝ := fun x => (G x) ^ (r - 1) * G' x
  -- Rewrite the φ-constant equation.
  have hphi :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        x * G'' x * G x = (r - 1) * G' x * (G x - x * G' x) := by
    intro x hx
    have hden : G' x * (G x - x * G' x) ≠ 0 := by
      have h1 : G' x ≠ 0 := N.G_deriv_ne_zero x hx.1
      have h2 : 0 < G x - x * G' x := N.G_sub_x_deriv_pos hx
      exact mul_ne_zero h1 (ne_of_gt h2)
    have h := hc x hx
    have h' : x * G'' x * G x = c * (G' x * (G x - x * G' x)) := by
      exact (div_eq_iff hden).1 h
    have hr : r - 1 = c := by simp [r]
    simpa [hr, mul_comm, mul_left_comm, mul_assoc] using h'
  -- Differential equation for H.
  have hderiv_H : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv H x = (r - 1) * H x / x := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hGpos : 0 < G x := N.G_pos_of_mem_Ioo hx
    have hGne : G x ≠ 0 := ne_of_gt hGpos
    have hdiff_f : DifferentiableAt ℝ (fun x => G x ^ (r - 1)) x :=
      (N.G_differentiableAt hxpos).rpow_const (Or.inl hGne)
    have hdiff_g : DifferentiableAt ℝ G' x := N.G'_differentiableAt hxpos
    have hderiv_f : deriv (fun x => G x ^ (r - 1)) x =
        G' x * (r - 1) * G x ^ ((r - 1) - 1) := by
      simpa using (deriv_rpow_const (f := G) (x := x) (p := r - 1)
        (N.G_differentiableAt hxpos) (Or.inl hGne))
    have hr2 : (r - 1) - 1 = r - 2 := by ring
    have hderiv_H1 :
        deriv H x =
          (G' x * (r - 1) * G x ^ (r - 2)) * G' x + (G x ^ (r - 1)) * deriv (fun x => G' x) x := by
      simpa [H, hderiv_f, hr2] using
        (deriv_fun_mul (c := fun x => G x ^ (r - 1)) (d := fun x => G' x) hdiff_f hdiff_g)
    have hpow : G x ^ (r - 1) = G x ^ (r - 2) * G x := by
      have h := Real.rpow_add hGpos (r - 2) 1
      have hsum : (r - 2) + 1 = r - 1 := by ring
      simpa [hsum, Real.rpow_one] using h
    have hphi' :
        x * deriv (fun x => G' x) x * G x = (r - 1) * G' x * (G x - x * G' x) := by
      simpa using (hphi x hx)
    have hmul : x * deriv H x = (r - 1) * H x := by
      calc
        x * deriv H x
            = x * ((G' x * (r - 1) * G x ^ (r - 2)) * G' x +
                (G x ^ (r - 1)) * deriv (fun x => G' x) x) := by
                simp [hderiv_H1]
        _ = (r - 1) * G x ^ (r - 2) * (G' x)^2 * x + (G x ^ (r - 1)) * G'' x * x := by ring
        _ = (r - 1) * G x ^ (r - 2) * (G' x)^2 * x +
              (G x ^ (r - 2) * G x) * G'' x * x := by
              simp [hpow, mul_comm]
        _ = (r - 1) * G x ^ (r - 2) * (G' x)^2 * x +
              (G x ^ (r - 2)) * (x * G'' x * G x) := by ring
        _ = (r - 1) * G x ^ (r - 2) * (G' x)^2 * x +
              (G x ^ (r - 2)) * ((r - 1) * G' x * (G x - x * G' x)) := by
              simp [hphi']
        _ = (r - 1) * ((G x ^ (r - 2) * G' x) * G x) := by ring
        _ = (r - 1) * ((G x ^ (r - 2) * G x) * G' x) := by ring
        _ = (r - 1) * ((G x ^ (r - 1)) * G' x) := by
              simp [hpow]
        _ = (r - 1) * H x := by simp [H, mul_comm]
    apply (eq_div_iff hxne).2
    simpa [mul_comm] using hmul
  -- H(x) * x^(1-r) is constant on (0,1).
  have hH_const : ∃ k, ∀ x ∈ Set.Ioo (0 : ℝ) 1, H x * x ^ (1 - r) = k := by
    let K : ℝ → ℝ := fun x => H x * x ^ (1 - r)
    have hdiffK : DifferentiableOn ℝ K (Set.Ioo 0 1) := by
      intro x hx
      have hxpos : 0 < x := hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hGne : G x ≠ 0 := N.G_ne_zero_of_mem_Ioo hx
      have hdiffH : DifferentiableAt ℝ H x := by
        have hdiff_f : DifferentiableAt ℝ (fun x => G x ^ (r - 1)) x :=
          (N.G_differentiableAt hxpos).rpow_const (Or.inl hGne)
        have hdiff_g : DifferentiableAt ℝ G' x := N.G'_differentiableAt hxpos
        simpa [H] using hdiff_f.mul hdiff_g
      have hdiff_pow : DifferentiableAt ℝ (fun x => x ^ (1 - r)) x :=
        (differentiableAt_id).rpow_const (Or.inl hxne)
      exact (hdiffH.mul hdiff_pow).differentiableWithinAt
    have hderivK : (Set.Ioo (0 : ℝ) 1).EqOn (deriv K) 0 := by
      intro x hx
      have hxpos : 0 < x := hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hGne : G x ≠ 0 := N.G_ne_zero_of_mem_Ioo hx
      have hdiffH : DifferentiableAt ℝ H x := by
        have hdiff_f : DifferentiableAt ℝ (fun x => G x ^ (r - 1)) x :=
          (N.G_differentiableAt hxpos).rpow_const (Or.inl hGne)
        have hdiff_g : DifferentiableAt ℝ G' x := N.G'_differentiableAt hxpos
        simpa [H] using hdiff_f.mul hdiff_g
      have hdiff_pow : DifferentiableAt ℝ (fun x => x ^ (1 - r)) x :=
        (differentiableAt_id).rpow_const (Or.inl hxne)
      have hderiv_pow : deriv (fun x => x ^ (1 - r)) x = (1 - r) * x ^ (-r) := by
        simpa [sub_eq_add_neg] using
          (Real.deriv_rpow_const (x := x) (p := 1 - r) (Or.inl hxne))
      have hderivK' : deriv K x =
          (r - 1) * H x / x * x ^ (1 - r) + H x * ((1 - r) * x ^ (-r)) := by
        have hderivH := hderiv_H x hx
        simpa [K, hderivH, hderiv_pow] using
          (deriv_fun_mul (c := H) (d := fun x => x ^ (1 - r)) hdiffH hdiff_pow)
      have hxpow_div : x ^ (1 - r) / x = x ^ (-r) := by
        have := Real.rpow_sub_one hxne (1 - r)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
      have hderivK'' : deriv K x =
          (r - 1) * H x * x ^ (-r) + H x * (1 - r) * x ^ (-r) := by
        calc
          deriv K x
              = (r - 1) * H x / x * x ^ (1 - r) + H x * ((1 - r) * x ^ (-r)) := hderivK'
          _ = (r - 1) * H x * (x ^ (1 - r) / x) + H x * (1 - r) * x ^ (-r) := by
                simp [div_mul_eq_mul_div, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc]
          _ = (r - 1) * H x * x ^ (-r) + H x * (1 - r) * x ^ (-r) := by
                simp [hxpow_div]
      calc
        deriv K x = (r - 1) * H x * x ^ (-r) + H x * (1 - r) * x ^ (-r) := hderivK''
        _ = 0 := by ring
    have hs : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
    have hs' : IsPreconnected (Set.Ioo (0 : ℝ) 1) := isPreconnected_Ioo
    exact (IsOpen.exists_is_const_of_deriv_eq_zero hs hs' hdiffK hderivK)
  obtain ⟨k, hk⟩ := hH_const
  have hH_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, H x = k * x ^ (r - 1) := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hxpow : x ^ (1 - r) * x ^ (r - 1) = (1 : ℝ) := by
      have := Real.rpow_add hxpos (1 - r) (r - 1)
      have hsum : (1 - r) + (r - 1) = 0 := by ring
      calc
        x ^ (1 - r) * x ^ (r - 1) = x ^ ((1 - r) + (r - 1)) := by
          simpa using this.symm
        _ = x ^ (0 : ℝ) := by simp [hsum]
        _ = 1 := by simp [Real.rpow_zero]
    calc
      H x = H x * (x ^ (1 - r) * x ^ (r - 1)) := by simp [hxpow]
      _ = (H x * x ^ (1 - r)) * x ^ (r - 1) := by ring
      _ = k * x ^ (r - 1) := by simp [hk x hx]
  -- Express G' using k.
  have hG'_formula : ∀ x ∈ Set.Ioo (0 : ℝ) 1, G' x = k * x ^ (r - 1) / (G x) ^ (r - 1) := by
    intro x hx
    have hGpow_ne : (G x) ^ (r - 1) ≠ 0 := by
      have hGpos : 0 < G x := N.G_pos_of_mem_Ioo hx
      exact (Real.rpow_pos_of_pos hGpos _).ne'
    apply (eq_div_iff hGpow_ne).2
    have hH := hH_eq x hx
    simpa [H, mul_comm, mul_left_comm, mul_assoc] using hH
  -- Differentiate involution to get k² = 1.
  have hderiv_invol : ∀ x ∈ Set.Ioo (0 : ℝ) 1, G' (G x) * G' x = 1 := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hGpos : 0 < G x := N.G_pos_of_mem_Ioo hx
    have hdiff_inner : DifferentiableAt ℝ G x := N.G_differentiableAt hxpos
    have hdiff_outer : DifferentiableAt ℝ G (G x) := N.G_differentiableAt hGpos
    have hderiv_comp : deriv (fun x => G (G x)) x = G' (G x) * G' x := by
      simpa [Function.comp] using (deriv_comp x hdiff_outer hdiff_inner)
    have hfun : (fun x => G (G x)) = fun x => x := by
      funext x; simpa using N.G_involution x
    have hderiv_eq := congrArg (fun f => deriv f x) hfun
    have hderiv_id : deriv (fun x => x) x = 1 := by
      exact (deriv_id (x := x))
    have hderiv1 : deriv (fun x => G (G x)) x = 1 := by simpa [hderiv_id] using hderiv_eq
    simpa [hderiv_comp] using hderiv1
  have hprod_const : ∀ x ∈ Set.Ioo (0 : ℝ) 1, G' (G x) * G' x = k ^ 2 := by
    intro x hx
    have hxmem : G x ∈ Set.Ioo (0 : ℝ) 1 := N.G_mem_Ioo_of_mem_Ioo hx
    have h1 := hG'_formula x hx
    have h2 := hG'_formula (G x) hxmem
    have hxpow_ne : x ^ (r - 1) ≠ 0 := by
      exact (Real.rpow_pos_of_pos hx.1 _).ne'
    have hGpow_ne : (G x) ^ (r - 1) ≠ 0 := by
      exact (Real.rpow_pos_of_pos (N.G_pos_of_mem_Ioo hx) _).ne'
    calc
      G' (G x) * G' x =
          (k * (G x) ^ (r - 1) / x ^ (r - 1)) *
          (k * x ^ (r - 1) / (G x) ^ (r - 1)) := by
            simp [h1, h2, N.G_involution x, mul_comm, mul_left_comm, mul_div_assoc]
      _ = k ^ 2 := by
            field_simp [hxpow_ne, hGpow_ne, mul_comm, mul_left_comm, mul_assoc]
  have hk_sq : k ^ 2 = 1 := by
    have hx0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have h1 := hprod_const (1 / 2) hx0
    have h2 := hderiv_invol (1 / 2) hx0
    calc
      k ^ 2 = G' (G (1 / 2)) * G' (1 / 2) := by simpa using h1.symm
      _ = 1 := h2
  have hkneg : k < 0 := by
    have hx0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have hG'neg : G' (1 / 2) < 0 := N.deriv_G_neg (by norm_num)
    have hform := hG'_formula (1 / 2) hx0
    have ha : 0 < (1 / 2 : ℝ) ^ (r - 1) / (G (1 / 2)) ^ (r - 1) := by
      have hxpos : 0 < (1 / 2 : ℝ) := by norm_num
      have hGpos : 0 < G (1 / 2) := N.G_pos_of_mem_Ioo hx0
      have hxpow_pos : 0 < (1 / 2 : ℝ) ^ (r - 1) := Real.rpow_pos_of_pos hxpos _
      have hGpow_pos : 0 < (G (1 / 2)) ^ (r - 1) := Real.rpow_pos_of_pos hGpos _
      exact div_pos hxpow_pos hGpow_pos
    have hform' : G' (1 / 2) =
        k * ((1 / 2 : ℝ) ^ (r - 1) / (G (1 / 2)) ^ (r - 1)) := by
      simpa [mul_div_assoc] using hform
    have hG'neg' : k * ((1 / 2 : ℝ) ^ (r - 1) / (G (1 / 2)) ^ (r - 1)) < 0 := by
      have hG'neg' := hG'neg
      -- rewrite the derivative using the closed form
      rw [hform'] at hG'neg'
      exact hG'neg'
    have h' : ((1 / 2 : ℝ) ^ (r - 1) / (G (1 / 2)) ^ (r - 1)) * k <
        ((1 / 2 : ℝ) ^ (r - 1) / (G (1 / 2)) ^ (r - 1)) * 0 := by
      simpa [mul_comm] using hG'neg'
    exact (mul_lt_mul_iff_right₀ ha).1 h'
  have hkneg_eq : k = -1 := by
    have hk_or : k = 1 ∨ k = -1 := by
      exact (sq_eq_one_iff).1 (by simpa using hk_sq)
    cases hk_or with
    | inl hk1 => exact (False.elim (by linarith [hkneg]))
    | inr hk1 => exact hk1
  -- F(x) = G(x)^r + x^r is constant on (0,1).
  let F : ℝ → ℝ := fun x => (G x) ^ r + x ^ r
  have hderiv_F_zero : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv F x = 0 := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hGpos : 0 < G x := N.G_pos_of_mem_Ioo hx
    have hGne : G x ≠ 0 := ne_of_gt hGpos
    have hderiv_Gpow : deriv (fun x => G x ^ r) x = G' x * r * G x ^ (r - 1) := by
      simpa using (deriv_rpow_const (f := G) (x := x) (p := r)
        (N.G_differentiableAt hxpos) (Or.inl hGne))
    have hderiv_xpow : deriv (fun x => x ^ r) x = r * x ^ (r - 1) := by
      simpa using (Real.deriv_rpow_const (x := x) (p := r) (Or.inl hxne))
    have hdiffGpow : DifferentiableAt ℝ (fun x => G x ^ r) x :=
      (N.G_differentiableAt hxpos).rpow_const (Or.inl hGne)
    have hdiff_xpow : DifferentiableAt ℝ (fun x => x ^ r) x :=
      (differentiableAt_id).rpow_const (Or.inl hxne)
    have hH := hH_eq x hx
    calc
      deriv F x = deriv (fun x => G x ^ r) x + deriv (fun x => x ^ r) x := by
        simpa [F] using (deriv_add (f := fun x => G x ^ r) (g := fun x => x ^ r) hdiffGpow hdiff_xpow)
      _ = (G' x * r * G x ^ (r - 1)) + (r * x ^ (r - 1)) := by
        simp [hderiv_Gpow, hderiv_xpow]
      _ = r * (G x ^ (r - 1) * G' x) + r * x ^ (r - 1) := by ring
      _ = r * H x + r * x ^ (r - 1) := by simp [H, mul_comm]
      _ = r * (k * x ^ (r - 1)) + r * x ^ (r - 1) := by simp [hH]
      _ = 0 := by
        simp [hkneg_eq]
  have hF_const : ∃ C, ∀ x ∈ Set.Ioo (0 : ℝ) 1, F x = C := by
    have hdiffF : DifferentiableOn ℝ F (Set.Ioo 0 1) := by
      intro x hx
      have hxpos : 0 < x := hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hGne : G x ≠ 0 := N.G_ne_zero_of_mem_Ioo hx
      have hdiffGpow : DifferentiableAt ℝ (fun x => G x ^ r) x :=
        (N.G_differentiableAt hxpos).rpow_const (Or.inl hGne)
      have hdiff_xpow : DifferentiableAt ℝ (fun x => x ^ r) x :=
        (differentiableAt_id).rpow_const (Or.inl hxne)
      exact (hdiffGpow.add hdiff_xpow).differentiableWithinAt
    have hderiv_eq : (Set.Ioo (0 : ℝ) 1).EqOn (deriv F) 0 := by
      intro x hx
      simp [hderiv_F_zero x hx]
    have hs : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
    have hs' : IsPreconnected (Set.Ioo (0 : ℝ) 1) := isPreconnected_Ioo
    exact (IsOpen.exists_is_const_of_deriv_eq_zero hs hs' hdiffF hderiv_eq)
  obtain ⟨C, hC⟩ := hF_const
  have hCpos : 0 < C := by
    have hx0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have hCeq := hC (1 / 2) hx0
    have hGpos : 0 < G (1 / 2) := N.G_pos_of_mem_Ioo hx0
    have hxpos : 0 < (1 / 2 : ℝ) := by norm_num
    have hGpow : 0 < (G (1 / 2)) ^ r := Real.rpow_pos_of_pos hGpos _
    have hxpow : 0 < (1 / 2 : ℝ) ^ r := Real.rpow_pos_of_pos hxpos _
    linarith [hCeq, hGpow, hxpow]
  -- Exclude r = 0.
  have hr_ne : r ≠ 0 := by
    intro hr
    have hG'_r0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, G' x = - G x / x := by
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt hx.1
      have hGne : G x ≠ 0 := N.G_ne_zero_of_mem_Ioo hx
      have hH0 : H x = k * x ^ (-1 : ℝ) := by
        simpa [hr] using (hH_eq x hx)
      have hH0' : (G x)⁻¹ * G' x = k * x⁻¹ := by
        simpa [H, hr, Real.rpow_neg_one] using hH0
      have h : G' x = k * x⁻¹ * G x := by
        calc
          G' x = (G x) * ((G x)⁻¹ * G' x) := by field_simp [hGne]
          _ = (G x) * (k * x⁻¹) := by simp [hH0']
          _ = k * x⁻¹ * G x := by ring
      simpa [hkneg_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    let J : ℝ → ℝ := fun x => x * G x
    have hderivJ : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv J x = 0 := by
      intro x hx
      have hxpos : 0 < x := hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hdiff_id : DifferentiableAt ℝ (fun x => x) x := differentiableAt_id
      have hdiff_G : DifferentiableAt ℝ G x := N.G_differentiableAt hxpos
      have hderivJ' : deriv J x = G x + x * G' x := by
        simpa [J] using (deriv_fun_mul (c := fun x => x) (d := G) hdiff_id hdiff_G)
      have hG' := hG'_r0 x hx
      calc
        deriv J x = G x + x * G' x := hderivJ'
        _ = G x + x * (- G x / x) := by simp [hG']
        _ = 0 := by
          field_simp [hxne]
          ring
    have hJ_const : ∃ K0, ∀ x ∈ Set.Ioo (0 : ℝ) 1, J x = K0 := by
      have hdiffJ : DifferentiableOn ℝ J (Set.Ioo 0 1) := by
        intro x hx
        have hxpos : 0 < x := hx.1
        have hdiff_id : DifferentiableAt ℝ (fun x => x) x := differentiableAt_id
        have hdiff_G : DifferentiableAt ℝ G x := N.G_differentiableAt hxpos
        exact (hdiff_id.mul hdiff_G).differentiableWithinAt
      have hderiv_eq : (Set.Ioo (0 : ℝ) 1).EqOn (deriv J) 0 := by
        intro x hx
        simp [hderivJ x hx]
      have hs : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
      have hs' : IsPreconnected (Set.Ioo (0 : ℝ) 1) := isPreconnected_Ioo
      exact (IsOpen.exists_is_const_of_deriv_eq_zero hs hs' hdiffJ hderiv_eq)
    obtain ⟨K0, hK0⟩ := hJ_const
    have hJ_cont : Continuous J := by
      have hcont_id : Continuous (fun x : ℝ => x) := continuous_id
      exact hcont_id.mul N.G_continuous
    have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ J ⁻¹' {K0} := by
      intro x hx
      simp [J, hK0 x hx]
    have hclosed : IsClosed (J ⁻¹' {K0}) := isClosed_singleton.preimage hJ_cont
    have hclosure : closure (Set.Ioo (0 : ℝ) 1) ⊆ J ⁻¹' {K0} :=
      closure_minimal hsubset hclosed
    have h1mem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := by
        exact (closure_Ioo (a := (0 : ℝ)) (b := (1 : ℝ)) (by exact (zero_ne_one : (0 : ℝ) ≠ 1)))
      have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [hcl]
      exact h1
    have h1mem' : (1 : ℝ) ∈ J ⁻¹' {K0} := hclosure h1mem
    have hJ1 : J 1 = K0 := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using h1mem'
    have hK0eq : K0 = 0 := by simpa [J, N.G_one] using hJ1.symm
    have hpos := N.G_pos_of_mem_Ioo (by
      have : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
      exact this)
    have hcontra : (1 / 2 : ℝ) * G (1 / 2) = 0 := by
      have hx0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
      simpa [J, hK0eq] using hK0 (1 / 2) hx0
    have : (1 / 2 : ℝ) * G (1 / 2) > 0 := by
      have hxpos : 0 < (1 / 2 : ℝ) := by norm_num
      have hGpos : 0 < G (1 / 2) := N.G_pos_of_mem_Ioo (by norm_num)
      exact mul_pos hxpos hGpos
    exact (ne_of_gt this) hcontra
  -- Show r > 0 using the constant C.
  have hr_pos : 0 < r := by
    by_contra hle
    have hrle : r ≤ 0 := le_of_not_gt hle
    rcases lt_or_eq_of_le hrle with hrneg | hreq
    · -- r < 0 leads to contradiction: choose x with x^r > C.
      have hrne : r ≠ 0 := ne_of_lt hrneg
      let x : ℝ := (C + 1) ^ (r⁻¹)
      have hxpos : 0 < x := by
        have hC1pos : 0 < C + 1 := by linarith [hCpos]
        exact Real.rpow_pos_of_pos hC1pos _
      have hxlt : x < 1 := by
        have hC1gt : 1 < C + 1 := by linarith [hCpos]
        have h1r : r⁻¹ < 0 := by
          simpa using (inv_lt_zero.mpr hrneg)
        simpa [x] using (Real.rpow_lt_one_of_one_lt_of_neg hC1gt h1r)
      have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, hxlt⟩
      have hxpow : x ^ r = C + 1 := by
        have hC1nonneg : 0 ≤ C + 1 := by linarith [hCpos]
        have hmul : r⁻¹ * r = 1 := by field_simp [hrne]
        calc
          x ^ r = (C + 1) ^ (r⁻¹ * r) := by
            simpa [x] using (Real.rpow_mul hC1nonneg r⁻¹ r).symm
          _ = (C + 1) ^ (1 : ℝ) := by rw [hmul]
          _ = C + 1 := by simp [Real.rpow_one]
      have hCeq := hC x hxmem
      have hGpos : 0 ≤ (G x) ^ r := by
        exact (Real.rpow_pos_of_pos (N.G_pos_of_mem_Ioo hxmem) _).le
      have hcontra : (G x) ^ r = -1 := by
        linarith [hCeq, hxpow]
      have hne : (G x) ^ r ≠ -1 := by linarith [hGpos]
      exact (hne hcontra)
    · -- r = 0 contradicts G_one (handled above).
      exact (hr_ne hreq)
  -- With r > 0, the constant must be 1 (using boundary at x = 1).
  have hC_eq : C = 1 := by
    have hF_cont : Continuous F := by
      have hG_cont : Continuous G := N.G_continuous
      have hGpow : Continuous (fun x => G x ^ r) :=
        hG_cont.rpow_const (fun _ => Or.inr hr_pos.le)
      have hxpow : Continuous (fun x : ℝ => x ^ r) :=
        Real.continuous_rpow_const hr_pos.le
      exact hGpow.add hxpow
    have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ F ⁻¹' {C} := by
      intro x hx
      simp [F, hC x hx]
    have hclosed : IsClosed (F ⁻¹' {C}) := isClosed_singleton.preimage hF_cont
    have hclosure : closure (Set.Ioo (0 : ℝ) 1) ⊆ F ⁻¹' {C} :=
      closure_minimal hsubset hclosed
    have h1mem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := by
        exact (closure_Ioo (a := (0 : ℝ)) (b := (1 : ℝ)) (by exact (zero_ne_one : (0 : ℝ) ≠ 1)))
      have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [hcl]
      exact h1
    have h1mem' : (1 : ℝ) ∈ F ⁻¹' {C} := hclosure h1mem
    have hF1 : F 1 = C := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using h1mem'
    have hF1' : F 1 = 1 := by
      have hrne : r ≠ 0 := ne_of_gt hr_pos
      simp [F, N.G_one, Real.zero_rpow hrne, Real.one_rpow]
    exact by simpa [hF1] using hF1'
  -- Final result.
  refine ⟨r, hr_pos, ?_⟩
  intro x hx
  have h := hC x hx
  simpa [F, hC_eq] using h

end CoxNegationAxioms

/-- **Cox's Negation Theorem (power-family form)**:
there exists `r > 0` such that `G(x)^r + x^r = 1` on `(0,1)`.
Regraduation by `x ↦ x^r` yields the standard negation rule. -/
theorem cox_negationRule (N : CoxNegationAxioms) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, (N.G x) ^ r + x ^ r = 1 := by
  simpa using (N.negation_power_family)

end Mettapedia.ProbabilityTheory.Cox
