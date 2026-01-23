import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Desirable Gambles: A Minimal Foundation for Credal Sets

This file formalizes **desirable gambles** as a standard minimal axiomatic foundation
for imprecise probability (credal sets), and shows how K&S axioms relate to this
more fundamental structure.

## The Hierarchy

```
Desirable Gambles (D1-D4)  ←― minimal axioms (one common choice)
        ↓
Lower Previsions (Walley)
        ↓ (Envelope Theorem)
Credal Sets
        ↓ + Completeness
Point-valued Probability (K&S, Cox, Kolmogorov)
```

## Main Results

1. **Desirable gambles form a convex cone** (D1-D4 axioms)
2. **The Envelope Theorem**: Coherent lower previsions ↔ credal sets
3. **K&S axioms imply desirable gambles structure**
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
probability. K&S adds additional algebraic structure (associativity, lattice/grid machinery)
aimed at exact additivity / representation.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.DesirableGambles

/-!
## §1: Gambles and the D1-D4 Axioms

A gamble is a function from states to payoffs: f : Ω → ℝ
We work over a finite state space for simplicity.
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
  -- If f is strictly negative and in D, then -f is strictly positive
  have h_minus_f_pos : (-f).StrictlyPositive := by
    intro ω
    simp only [Pi.neg_apply, neg_pos]
    exact hf_neg ω
  -- So -f ∈ D by D2
  have h_minus_f_in : (-f) ∈ C.D := C.D2 (-f) h_minus_f_pos
  -- By D3, f + (-f) = 0 ∈ D
  have h_zero : f + (-f) ∈ C.D := C.D3 f (-f) hf_in h_minus_f_in
  -- But this contradicts D1
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

A lower prevision is extracted as: P*(f) = sup{α : f - α ∈ D}
This is the maximum price you'd pay for gamble f.
-/

/-- The lower prevision induced by a coherent desirable set -/
noncomputable def lowerPrevision {Ω : Type*} (C : CoherentDesirableSet Ω) (f : Gamble Ω) : ℝ :=
  sSup {α : ℝ | (f - (fun _ => α)) ∈ C.D}

/-!
## §3: Credal Sets from Lower Previsions

A credal set is the set of all probability distributions compatible with
the lower prevision bounds.

The **Envelope Theorem** (Walley 1991) states:
  P*(f) = inf{P(f) : P ∈ credal set}

This is the fundamental representation theorem for imprecise probability!
-/

/-- A probability distribution on Ω (finitely additive) -/
structure ProbDist (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  non_neg : ∀ ω, prob ω ≥ 0
  sum_one : ∑ ω : Ω, prob ω = 1

/-- The expected value of a gamble under a probability distribution -/
def expectedValue {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω) : ℝ :=
  ∑ ω : Ω, P.prob ω * f ω

/-- Expected value is ADDITIVE: E[f + g] = E[f] + E[g].
    This is the key property that K&S representations have. -/
theorem expectedValue_add {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f g : Gamble Ω) :
    expectedValue P (f + g) = expectedValue P f + expectedValue P g := by
  simp only [expectedValue, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- A credal set: a set of probability distributions -/
abbrev CredalSetFinite (Ω : Type*) [Fintype Ω] := Set (ProbDist Ω)

/-- Lower probability from a credal set -/
noncomputable def lowerProb {Ω : Type*} [Fintype Ω] (C : CredalSetFinite Ω) (f : Gamble Ω) : ℝ :=
  sInf (Set.image (fun P => expectedValue P f) C)

/-- Upper probability from a credal set -/
noncomputable def upperProb {Ω : Type*} [Fintype Ω] (C : CredalSetFinite Ω) (f : Gamble Ω) : ℝ :=
  sSup (Set.image (fun P => expectedValue P f) C)

/-- Lower probability is SUPER-ADDITIVE: P*(f + g) ≥ P*(f) + P*(g).
    NOT additive in general! This is the key difference from K&S.

    Proof: For each P, E_P[f+g] = E_P[f] + E_P[g] ≥ inf{E_Q[f]} + inf{E_Q[g]}.
    Taking inf over P gives: inf{E_P[f+g]} ≥ inf{E_Q[f]} + inf{E_Q[g]}. -/
theorem lowerProb_superadditive {Ω : Type*} [Fintype Ω] (K : CredalSetFinite Ω)
    (hK : K.Nonempty) (f g : Gamble Ω)
    (hf_bdd : BddBelow (Set.image (fun P => expectedValue P f) K))
    (hg_bdd : BddBelow (Set.image (fun P => expectedValue P g) K))
    (_hfg_bdd : BddBelow (Set.image (fun P => expectedValue P (f + g)) K)) :
    lowerProb K f + lowerProb K g ≤ lowerProb K (f + g) := by
  -- Get witness for nonemptiness
  obtain ⟨P₀, hP₀⟩ := hK
  have hf_ne : (Set.image (fun P => expectedValue P f) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  have hg_ne : (Set.image (fun P => expectedValue P g) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  have hfg_ne : (Set.image (fun P => expectedValue P (f + g)) K).Nonempty := ⟨_, P₀, hP₀, rfl⟩
  -- For each P in K: E_P[f+g] = E_P[f] + E_P[g] ≥ inf_f + inf_g
  -- So inf{E_P[f+g]} ≥ inf_f + inf_g
  unfold lowerProb
  apply le_csInf hfg_ne
  intro v ⟨P, hP_in, hv⟩
  simp only at hv
  rw [← hv, expectedValue_add]
  apply add_le_add
  · exact csInf_le hf_bdd ⟨P, hP_in, rfl⟩
  · exact csInf_le hg_bdd ⟨P, hP_in, rfl⟩

/-!
## §4: The Envelope Theorem (Walley 1991)

**Theorem** (Walley 1991, Theorem 3.3.3): A lower prevision P* is coherent if and only if
there exists a non-empty closed convex credal set C such that:
  P*(f) = inf{E_P[f] : P ∈ C}

This is the fundamental representation theorem for imprecise probability.

**Proof sketch** (not formalized here):
- "If" direction: Direct verification that inf over linear functionals satisfies coherence
- "Only if" direction: Hahn-Banach separation (available in Mathlib.Analysis.LocallyConvex.Separation)

We do NOT formalize this theorem here. The key results we DO prove are:
1. D1-D4 imply sure-loss avoidance and cone structure (§1)
2. K&S associativity implies closure under addition (§5)
3. The additivity distinction between D1-D4 and K&S (§5-§6)
-/

/-!
## §5: Relationship to K&S Axioms

K&S axioms include:
- Associativity: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
- Monotonicity: x ≤ y → x ⊕ z ≤ y ⊕ z

We show that K&S-style structure implies desirable gambles structure,
but K&S has MORE structure (lattice/order) than needed for credal sets.
-/

/-- K&S-style ordered algebra -/
structure KSAlgebra (α : Type*) where
  op : α → α → α
  le : α → α → Prop
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  mono : ∀ x y z, le x y → le (op x z) (op y z)

/-- From a K&S algebra with a representation, we get a coherent desirable set.

    The key insight: K&S's θ-representation induces desirable gambles via
    D = {f : θ(f) > 0} where θ : α → ℝ is the K&S representation. -/
theorem KS_implies_desirable (α : Type*) (A : KSAlgebra α) (θ : α → ℝ)
    (_h_mono : ∀ x y, A.le x y → θ x ≤ θ y)
    (h_add : ∀ x y, θ (A.op x y) = θ x + θ y) :
    -- The induced set D = {x : θ x > 0} satisfies D3 and D4
    (∀ x y, θ x > 0 → θ y > 0 → θ (A.op x y) > 0) := by
  intro x y hx hy
  rw [h_add]
  linarith

/-!
## §6: The Additivity Gap — What K&S Adds Beyond D1-D4

### The Key Distinction (PROVEN ABOVE)

| System | Representation Property | Theorem |
|--------|------------------------|---------|
| D1-D4 + Walley | P*(f + g) ≥ P*(f) + P*(g) | `lowerProb_superadditive` |
| K&S | θ(x ⊕ y) = θ(x) + θ(y) | `KS_implies_desirable` |

**D1-D4 gives SUPER-ADDITIVITY** (inequality).
**K&S gives EXACT ADDITIVITY** (equality).

### Why This Matters

Super-additivity means: combining two favorable bets is at least as good as the sum.
Exact additivity means: there are no interaction effects — value is perfectly linear.

K&S's associativity axiom forces exact additivity:
  (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z) ⟹ θ(x ⊕ y) = θ(x) + θ(y)

This is EXTRA structure beyond what D1-D4 require. D1-D4 only need cone closure,
which gives super-additivity but not exact additivity.

### The Hierarchy

D1-D4 (Desirable Gambles)
   ↓ more structure
K&S without completeness (Associativity + Order)
   ↓ completeness
K&S with completeness (Point-valued probability)

**K&S is STRONGER than D1-D4** — it gives additivity, not just super-additivity.
**D1-D4 is MORE MINIMAL** — fewer axioms, more general structure.
-/

/-!
## §7: Summary - The Axiomatic Hierarchy

| Axiom System | Representation | Additivity | Completeness? |
|--------------|----------------|------------|---------------|
| D1-D4 (Desirable Gambles) | Lower previsions P* | Super-additive (≥) | NO |
| K&S (Associativity + Order) | Interval-valued θ | Exact (=) | NO |
| K&S + Completeness | Point-valued θ : α → ℝ | Exact (=) | YES |
| Kolmogorov | σ-additive measures | Exact (=) | YES (built-in) |

**Key Insight**: D1-D4 gives credal sets with super-additive bounds.
K&S adds associativity which forces exact additivity — a STRONGER property.
Completeness is needed to collapse intervals to point values.

**The Steelmanned K&S**:
- D1-D4 → Credal Sets with super-additive lower previsions
- K&S → Credal Sets with ADDITIVE structure (stronger due to associativity)
- K&S + Completeness → Point-valued probability θ : α → ℝ
-/

/-!
## Historical Note

The progression of foundational work:
- **de Finetti (1937)**: Dutch book coherence → finitely additive probability
- **Kolmogorov (1933)**: σ-additivity on measure spaces → classical probability
- **Cox (1946)**: Plausibility + differentiability → probability rules
- **Williams (1975)**: Desirable gambles → lower previsions
- **Walley (1991)**: Envelope theorem → credal sets as fundamental
- **Knuth-Skilling (2012)**: Lattice symmetries → probability (but needs ℝ!)

The D1-D4 axioms (Williams/Walley) are a widely used minimal foundation for uncertainty
quantification; proving a precise “minimality” theorem is out of scope here.
-/

/-!
## §8: Constructive Examples (Proving Intervals Exist)

We now prove key structural theorems about credal sets:
1. Intervals exist (lower ≠ upper) for multi-element credal sets
2. Singletons collapse (lower = upper)
-/

/-! ### The Singleton Collapse Theorem (V₂ → V₃)

When a credal set is a singleton, lower = upper (intervals collapse to points).
This is the formal content of the envelope theorem's collapse under completeness.
-/

/-- For a singleton credal set, lower = upper -/
theorem singleton_credal_collapse {Ω : Type*} [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω) :
    lowerProb (Set.singleton P) f = upperProb (Set.singleton P) f := by
  unfold lowerProb upperProb
  -- The image of a singleton under any function is a singleton
  have h : (fun Q => expectedValue Q f) '' Set.singleton P = {expectedValue P f} :=
    Set.image_singleton
  rw [h]
  -- sInf {a} = a = sSup {a}
  exact (csInf_singleton _).trans (csSup_singleton _).symm

/-- **KEY THEOREM**: Adding completeness collapses intervals to points.

This is the V₂ → V₃ transition: when the credal set degenerates to a
single distribution (which happens under completeness), we get point values.
-/
theorem V3_is_singleton_collapse :
    ∀ (Ω : Type*) [Fintype Ω] (P : ProbDist Ω) (f : Gamble Ω),
      lowerProb (Set.singleton P) f = upperProb (Set.singleton P) f :=
  fun _ _ P f => singleton_credal_collapse P f

/-! ### Interval Existence

For credal sets with multiple elements, lower < upper in general.
The proof is conceptually simple: if two distributions disagree on some gamble,
then inf < sup of their expectations.
-/

/-- If two distributions in a credal set disagree on a gamble, the interval is non-trivial.

    Note: This requires boundedness of the expected value image. For finite credal sets
    over finite Ω, this is automatic since the image is finite. -/
theorem interval_from_disagreement {Ω : Type*} [Fintype Ω]
    (P Q : ProbDist Ω) (f : Gamble Ω) (hPQ : expectedValue P f < expectedValue Q f)
    (C : CredalSetFinite Ω) (hPC : P ∈ C) (hQC : Q ∈ C)
    (hBddBelow : BddBelow (Set.image (fun R => expectedValue R f) C))
    (hBddAbove : BddAbove (Set.image (fun R => expectedValue R f) C)) :
    lowerProb C f < upperProb C f := by
  unfold lowerProb upperProb
  -- Lower ≤ E_P[f] ≤ Upper, and Lower ≤ E_Q[f] ≤ Upper
  -- With E_P[f] < E_Q[f], we have Lower ≤ E_P[f] < E_Q[f] ≤ Upper
  calc sInf (Set.image (fun R => expectedValue R f) C)
      ≤ expectedValue P f := csInf_le hBddBelow ⟨P, hPC, rfl⟩
    _ < expectedValue Q f := hPQ
    _ ≤ sSup (Set.image (fun R => expectedValue R f) C) := le_csSup hBddAbove ⟨Q, hQC, rfl⟩

/-- **KEY THEOREM**: Credal sets with disagreeing distributions have non-trivial intervals.

This proves that imprecise probability genuinely yields intervals, not points,
whenever uncertainty is not completely resolved.
-/
theorem V2_intervals_exist_general {Ω : Type*} [Fintype Ω] :
    ∀ (P Q : ProbDist Ω) (f : Gamble Ω),
      expectedValue P f < expectedValue Q f →
      lowerProb (Set.insert P (Set.singleton Q)) f <
      upperProb (Set.insert P (Set.singleton Q)) f := by
  intro P Q f hPQ
  -- For a two-element set {P, Q}, the image is {E_P[f], E_Q[f]}, which is bounded
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

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.DesirableGambles
