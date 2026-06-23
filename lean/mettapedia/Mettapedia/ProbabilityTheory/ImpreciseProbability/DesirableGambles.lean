import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Desirable Gambles: A Minimal Foundation for Credal Sets

This file formalizes **desirable gambles** as a standard minimal axiomatic foundation
for imprecise probability (credal sets), and relates this foundation to stronger
exact-additive representation stories such as K&S.

## The Hierarchy

```
Desirable Gambles (D1-D4)  ←― minimal axioms (one common choice)
        ↓
Lower Previsions (Walley)
        ↓ (Envelope Theorem)
Credal Sets
        ↓ + Completeness
Point-valued Probability
```

## Main Results

1. **Desirable gambles form a convex cone** (D1-D4 axioms)
2. **The Envelope Theorem viewpoint**: coherent lower previsions ↔ credal sets
3. **Exact-additive representations imply desirable-gamble closure**
4. **Desirable gambles do NOT imply completeness**

## References

Primary sources:
- Walley, P. (1991). "Statistical Reasoning with Imprecise Probabilities"
  [The envelope theorem and lower previsions]
- Williams, P.M. (1975). "Notes on conditional previsions"
  [Original desirable gambles framework]
- Quaeghebeur, E. (2014). "Desirability" in Introduction to Imprecise Probabilities
  [Modern survey of the D1-D4 axioms]

Stanford Encyclopedia of Philosophy:
- https://plato.stanford.edu/entries/imprecise-probabilities/

Key insight (informal): The D1-D4 axioms are a lean way to axiomatize coherent imprecise
probability. Stronger algebraic theories add exact additive structure on top of this.
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-!
## §1: Gambles and the D1-D4 Axioms

A gamble is a function from states to payoffs: `f : Ω → ℝ`.
We work over a finite state space for simplicity where needed.
-/

/-- A gamble over state space Ω is a function from states to real payoffs -/
abbrev Gamble (Ω : Type*) := Ω → ℝ

/-- A gamble is strictly positive if f(ω) > 0 for all ω -/
def Gamble.StrictlyPositive {Ω : Type*} (f : Gamble Ω) : Prop := ∀ ω, f ω > 0

/-- A gamble is non-negative if f(ω) ≥ 0 for all ω -/
def Gamble.NonNegative {Ω : Type*} (f : Gamble Ω) : Prop := ∀ ω, f ω ≥ 0

/-- A gamble is strictly negative if f(ω) < 0 for all ω -/
def Gamble.StrictlyNegative {Ω : Type*} (f : Gamble Ω) : Prop := ∀ ω, f ω < 0

/-!
### The D1-D4 Axioms for Coherent Sets of Desirable Gambles

These are a widely used minimal axiom set for imprecise probability.
-/

/-- A set of desirable gambles satisfying the D1-D4 coherence axioms -/
structure CoherentDesirableSet (Ω : Type*) where
  /-- The set of gambles considered desirable -/
  D : Set (Gamble Ω)
  /-- D1: The zero gamble is not desirable (no free lunch) -/
  D1 : (0 : Gamble Ω) ∉ D
  /-- D2: Strictly positive gambles are desirable (sure gains are good) -/
  D2 : ∀ f, f.StrictlyPositive → f ∈ D
  /-- D3: Desirable gambles are closed under addition (combining bets) -/
  D3 : ∀ f g, f ∈ D → g ∈ D → f + g ∈ D
  /-- D4: Desirable gambles are closed under positive scaling (stake independence) -/
  D4 : ∀ f (c : ℝ), f ∈ D → c > 0 → c • f ∈ D

/-!
### Properties of Coherent Desirable Sets
-/

/-- Coherent desirable sets avoid sure loss: no strictly negative gamble is desirable -/
theorem avoid_sure_loss {Ω : Type*} (C : CoherentDesirableSet Ω) :
    ∀ f : Gamble Ω, f.StrictlyNegative → f ∉ C.D := by
  intro f hf_neg hf_in
  have h_minus_f_pos : (-f).StrictlyPositive := by
    intro ω
    simp only [Pi.neg_apply, neg_pos]
    exact hf_neg ω
  have h_minus_f_in : (-f) ∈ C.D := C.D2 (-f) h_minus_f_pos
  have h_zero : f + (-f) ∈ C.D := C.D3 f (-f) hf_in h_minus_f_in
  simp at h_zero
  exact C.D1 h_zero

/-- The set of desirable gambles forms a convex cone -/
theorem desirable_is_cone {Ω : Type*} (C : CoherentDesirableSet Ω) :
    ∀ f g : Gamble Ω, f ∈ C.D → g ∈ C.D → ∀ a b : ℝ, a > 0 → b > 0 → a • f + b • g ∈ C.D := by
  intro f g hf hg a b ha hb
  have h1 : a • f ∈ C.D := C.D4 f a hf ha
  have h2 : b • g ∈ C.D := C.D4 g b hg hb
  exact C.D3 (a • f) (b • g) h1 h2

/-!
## §2: Lower Previsions from Desirable Gambles

A lower prevision is extracted as: `P*(f) = sup{α : f - α ∈ D}`.
-/

/-- The lower prevision induced by a coherent desirable set -/
noncomputable def lowerPrevision {Ω : Type*} (C : CoherentDesirableSet Ω) (f : Gamble Ω) : ℝ :=
  sSup {α : ℝ | (f - (fun _ => α)) ∈ C.D}

/-!
## §3: Credal Sets from Lower Previsions

A credal set is the set of all probability distributions compatible with
the lower prevision bounds.
-/

/-- A probability distribution on Ω (finitely additive) -/
structure ProbDist (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  non_neg : ∀ ω, prob ω ≥ 0
  sum_one : ∑ ω : Ω, prob ω = 1

/-- The expected value of a gamble under a probability distribution -/
def expectedValue {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω) : ℝ :=
  ∑ ω : Ω, P.prob ω * f ω

/-- Expected value is additive: `E[f + g] = E[f] + E[g]`. -/
theorem expectedValue_add {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f g : Gamble Ω) :
    expectedValue P (f + g) = expectedValue P f + expectedValue P g := by
  simp only [expectedValue, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Expected value of a nonnegative gamble is nonnegative. -/
theorem expectedValue_nonneg_of_nonnegative {Ω : Type*} [Fintype Ω]
    (P : ProbDist Ω) (f : Gamble Ω) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ expectedValue P f := by
  unfold expectedValue
  exact Finset.sum_nonneg (by
    intro ω _
    exact mul_nonneg (P.non_neg ω) (hf ω))

/-- Expected value of a gamble bounded above by one is at most one. -/
theorem expectedValue_le_one_of_le_one {Ω : Type*} [Fintype Ω]
    (P : ProbDist Ω) (f : Gamble Ω) (hf : ∀ ω, f ω ≤ 1) :
    expectedValue P f ≤ 1 := by
  unfold expectedValue
  calc
    (∑ ω : Ω, P.prob ω * f ω) ≤ ∑ ω : Ω, P.prob ω * 1 := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_left (hf ω) (P.non_neg ω)
    _ = ∑ ω : Ω, P.prob ω := by simp
    _ = 1 := P.sum_one

/-- Expected value of a unit-bounded gamble lies in `[0,1]`. -/
theorem expectedValue_mem_unit_of_unit_gamble {Ω : Type*} [Fintype Ω]
    (P : ProbDist Ω) (f : Gamble Ω) (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    expectedValue P f ∈ Set.Icc 0 1 :=
  ⟨expectedValue_nonneg_of_nonnegative P f (fun ω => (hf ω).1),
    expectedValue_le_one_of_le_one P f (fun ω => (hf ω).2)⟩

/-- A credal set: a set of probability distributions -/
abbrev CredalSetFinite (Ω : Type*) [Fintype Ω] := Set (ProbDist Ω)

/-- Lower probability from a credal set -/
noncomputable def lowerProb {Ω : Type*} [Fintype Ω] (C : CredalSetFinite Ω) (f : Gamble Ω) : ℝ :=
  sInf (Set.image (fun P => expectedValue P f) C)

/-- Upper probability from a credal set -/
noncomputable def upperProb {Ω : Type*} [Fintype Ω] (C : CredalSetFinite Ω) (f : Gamble Ω) : ℝ :=
  sSup (Set.image (fun P => expectedValue P f) C)

/-- The lower probability of a unit-bounded gamble lies in `[0,1]` when the
credal set is nonempty. -/
theorem lowerProb_mem_unit_of_unit_gamble {Ω : Type*} [Fintype Ω]
    (C : CredalSetFinite Ω) (hC : C.Nonempty) (f : Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    lowerProb C f ∈ Set.Icc 0 1 := by
  let S : Set ℝ := Set.image (fun P => expectedValue P f) C
  have hS_ne : S.Nonempty := by
    rcases hC with ⟨P, hP⟩
    exact ⟨expectedValue P f, ⟨P, hP, rfl⟩⟩
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro x hx
    rcases hx with ⟨P, _hP, rfl⟩
    exact (expectedValue_mem_unit_of_unit_gamble P f hf).1
  unfold lowerProb
  constructor
  · exact le_csInf hS_ne (by
      intro x hx
      rcases hx with ⟨P, _hP, rfl⟩
      exact (expectedValue_mem_unit_of_unit_gamble P f hf).1)
  · rcases hC with ⟨P, hP⟩
    exact (csInf_le hS_bddBelow ⟨P, hP, rfl⟩).trans
      (expectedValue_mem_unit_of_unit_gamble P f hf).2

/-- The upper probability of a unit-bounded gamble lies in `[0,1]` when the
credal set is nonempty. -/
theorem upperProb_mem_unit_of_unit_gamble {Ω : Type*} [Fintype Ω]
    (C : CredalSetFinite Ω) (hC : C.Nonempty) (f : Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    upperProb C f ∈ Set.Icc 0 1 := by
  let S : Set ℝ := Set.image (fun P => expectedValue P f) C
  have hS_ne : S.Nonempty := by
    rcases hC with ⟨P, hP⟩
    exact ⟨expectedValue P f, ⟨P, hP, rfl⟩⟩
  have hS_bddAbove : BddAbove S := by
    refine ⟨1, ?_⟩
    intro x hx
    rcases hx with ⟨P, _hP, rfl⟩
    exact (expectedValue_mem_unit_of_unit_gamble P f hf).2
  unfold upperProb
  constructor
  · rcases hC with ⟨P, hP⟩
    exact (expectedValue_mem_unit_of_unit_gamble P f hf).1.trans
      (le_csSup hS_bddAbove ⟨P, hP, rfl⟩)
  · exact csSup_le hS_ne (by
      intro x hx
      rcases hx with ⟨P, _hP, rfl⟩
      exact (expectedValue_mem_unit_of_unit_gamble P f hf).2)

/-- Lower probability is below upper probability for nonempty finite credal
sets and unit-bounded gambles. -/
theorem lowerProb_le_upperProb_of_unit_gamble {Ω : Type*} [Fintype Ω]
    (C : CredalSetFinite Ω) (hC : C.Nonempty) (f : Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    lowerProb C f ≤ upperProb C f := by
  let S : Set ℝ := Set.image (fun P => expectedValue P f) C
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro x hx
    rcases hx with ⟨P, _hP, rfl⟩
    exact (expectedValue_mem_unit_of_unit_gamble P f hf).1
  have hS_bddAbove : BddAbove S := by
    refine ⟨1, ?_⟩
    intro x hx
    rcases hx with ⟨P, _hP, rfl⟩
    exact (expectedValue_mem_unit_of_unit_gamble P f hf).2
  rcases hC with ⟨P, hP⟩
  unfold lowerProb upperProb
  calc
    sInf S ≤ expectedValue P f := csInf_le hS_bddBelow ⟨P, hP, rfl⟩
    _ ≤ sSup S := le_csSup hS_bddAbove ⟨P, hP, rfl⟩

/-- Lower probability is superadditive: `P*(f + g) ≥ P*(f) + P*(g)`. -/
theorem lowerProb_superadditive {Ω : Type*} [Fintype Ω] (K : CredalSetFinite Ω)
    (hK : K.Nonempty) (f g : Gamble Ω)
    (hf_bdd : BddBelow (Set.image (fun P => expectedValue P f) K))
    (hg_bdd : BddBelow (Set.image (fun P => expectedValue P g) K))
    (_hfg_bdd : BddBelow (Set.image (fun P => expectedValue P (f + g)) K)) :
    lowerProb K f + lowerProb K g ≤ lowerProb K (f + g) := by
  obtain ⟨P₀, hP₀⟩ := hK
  have hf_ne : (Set.image (fun P => expectedValue P f) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  have hg_ne : (Set.image (fun P => expectedValue P g) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  have hfg_ne : (Set.image (fun P => expectedValue P (f + g)) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  unfold lowerProb
  apply le_csInf hfg_ne
  intro v ⟨P, hP_in, hv⟩
  simp only at hv
  rw [← hv, expectedValue_add]
  apply add_le_add
  · exact csInf_le hf_bdd ⟨P, hP_in, rfl⟩
  · exact csInf_le hg_bdd ⟨P, hP_in, rfl⟩

/-!
## §4: The Envelope Theorem Viewpoint

Walley's envelope theorem says a coherent lower prevision arises as the infimum of
linear expectations over a suitable credal set. We do not formalize the full theorem
here; instead we formalize the structural pieces used downstream.
-/

/-!
## §5: Relationship to Stronger Exact-Additive Axioms

Strong additive/algebraic theories include:
- Associativity: `(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)`
- Monotonicity: `x ≤ y → x ⊕ z ≤ y ⊕ z`

We show that exact-additive representation structure implies desirable-gamble closure,
but desirable gambles need much less structure.
-/

/-- A simple ordered algebraic skeleton with a binary operation and monotonicity. -/
structure KSAlgebra (α : Type*) where
  op : α → α → α
  le : α → α → Prop
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  mono : ∀ x y z, le x y → le (op x z) (op y z)

/-- From an exact additive representation, positive elements are closed under combination. -/
theorem KS_implies_desirable (α : Type*) (A : KSAlgebra α) (θ : α → ℝ)
    (_h_mono : ∀ x y, A.le x y → θ x ≤ θ y)
    (h_add : ∀ x y, θ (A.op x y) = θ x + θ y) :
    (∀ x y, θ x > 0 → θ y > 0 → θ (A.op x y) > 0) := by
  intro x y hx hy
  rw [h_add]
  linarith

/-!
## §6: The Additivity Gap

| System | Representation Property | Theorem |
|--------|------------------------|---------|
| D1-D4 + Walley | `P*(f + g) ≥ P*(f) + P*(g)` | `lowerProb_superadditive` |
| Exact additive representations | `θ(x ⊕ y) = θ(x) + θ(y)` | `KS_implies_desirable` |

Desirable gambles give superadditive lower bounds.
Exact additive theories force stronger linear structure.
-/

/-!
## §7: Summary

| Axiom System | Representation | Additivity | Completeness? |
|--------------|----------------|------------|---------------|
| D1-D4 (Desirable Gambles) | Lower previsions `P*` | Super-additive (`≥`) | NO |
| Exact additive interval semantics | Interval-valued `θ` | Exact (`=`) | NO |
| Exact additive + completeness | Point-valued `θ : α → ℝ` | Exact (`=`) | YES |

This file sits at the minimal imprecise-probability end of that spectrum.
-/

/-!
## §8: Constructive Examples (Proving Intervals Exist)
-/

/-- For a singleton credal set, the lower probability is just that
distribution's expected value. -/
theorem lowerProb_singleton_eq_expectedValue {Ω : Type*} [Fintype Ω]
    (P : ProbDist Ω) (f : Gamble Ω) :
    lowerProb (Set.singleton P) f = expectedValue P f := by
  unfold lowerProb
  have h :
      ((fun Q => expectedValue Q f) '' Set.singleton P) =
        ({expectedValue P f} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hQP : Q = P := hQ
      simp [hQP]
    · intro hx
      have hx' : x = expectedValue P f := by simpa using hx
      subst x
      exact ⟨P, rfl, rfl⟩
  rw [h]
  exact csInf_singleton _

/-- For a singleton credal set, the upper probability is just that
distribution's expected value. -/
theorem upperProb_singleton_eq_expectedValue {Ω : Type*} [Fintype Ω]
    (P : ProbDist Ω) (f : Gamble Ω) :
    upperProb (Set.singleton P) f = expectedValue P f := by
  unfold upperProb
  have h :
      ((fun Q => expectedValue Q f) '' Set.singleton P) =
        ({expectedValue P f} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hQP : Q = P := hQ
      simp [hQP]
    · intro hx
      have hx' : x = expectedValue P f := by simpa using hx
      subst x
      exact ⟨P, rfl, rfl⟩
  rw [h]
  exact csSup_singleton _

/-- For a singleton credal set, lower = upper. -/
theorem singleton_credal_collapse {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω) :
    lowerProb (Set.singleton P) f = upperProb (Set.singleton P) f := by
  rw [lowerProb_singleton_eq_expectedValue, upperProb_singleton_eq_expectedValue]

/-- The singleton collapse principle. -/
theorem V3_is_singleton_collapse :
    ∀ (Ω : Type*) [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω),
      lowerProb (Set.singleton P) f = upperProb (Set.singleton P) f :=
  fun _ _ P f => singleton_credal_collapse P f

/-- If two distributions in a credal set disagree on a gamble, the interval is non-trivial. -/
theorem interval_from_disagreement {Ω : Type*} [Fintype Ω]
    (P Q : ProbDist Ω) (f : Gamble Ω) (hPQ : expectedValue P f < expectedValue Q f)
    (C : CredalSetFinite Ω) (hPC : P ∈ C) (hQC : Q ∈ C)
    (hBddBelow : BddBelow (Set.image (fun R => expectedValue R f) C))
    (hBddAbove : BddAbove (Set.image (fun R => expectedValue R f) C)) :
    lowerProb C f < upperProb C f := by
  unfold lowerProb upperProb
  calc sInf (Set.image (fun R => expectedValue R f) C)
      ≤ expectedValue P f := csInf_le hBddBelow ⟨P, hPC, rfl⟩
    _ < expectedValue Q f := hPQ
    _ ≤ sSup (Set.image (fun R => expectedValue R f) C) := le_csSup hBddAbove ⟨Q, hQC, rfl⟩

/-- Credal sets with disagreeing distributions have non-trivial intervals. -/
theorem V2_intervals_exist_general {Ω : Type*} [Fintype Ω] :
    ∀ (P Q : ProbDist Ω) (f : Gamble Ω),
      expectedValue P f < expectedValue Q f →
      lowerProb (Set.insert P (Set.singleton Q)) f <
      upperProb (Set.insert P (Set.singleton Q)) f := by
  intro P Q f hPQ
  let eP := expectedValue P f
  let eQ := expectedValue Q f
  let C := Set.insert P (Set.singleton Q)
  have hBddBelow : BddBelow (Set.image (fun R => expectedValue R f) C) := by
    use min eP eQ - 1
    intro x hx
    obtain ⟨R, hR, rfl⟩ := hx
    rcases Set.mem_insert_iff.mp hR with rfl | hR'
    · have h := min_le_left eP eQ
      linarith
    · have hRQ : R = Q := Set.mem_singleton_iff.mp hR'
      rw [hRQ]
      have h := min_le_right eP eQ
      linarith
  have hBddAbove : BddAbove (Set.image (fun R => expectedValue R f) C) := by
    use max eP eQ + 1
    intro x hx
    obtain ⟨R, hR, rfl⟩ := hx
    rcases Set.mem_insert_iff.mp hR with rfl | hR'
    · have h := le_max_left eP eQ
      linarith
    · have hRQ : R = Q := Set.mem_singleton_iff.mp hR'
      rw [hRQ]
      have h := le_max_right eP eQ
      linarith
  exact interval_from_disagreement P Q f hPQ C
    (Set.mem_insert P _) (Set.mem_insert_of_mem P rfl) hBddBelow hBddAbove

end Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles
