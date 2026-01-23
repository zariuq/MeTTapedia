/-
# Hypercube Examples: REAL Formalized Instances

This file provides ACTUAL Lean formalizations of concrete examples for hypercube vertices,
not just metadata strings. Each example is proven to satisfy (or not satisfy) the relevant axioms.

## Structure

§1. KnuthSkillingAlgebraBase positive example: ℕ with addition
§2. KnuthSkillingAlgebraBase negative example: Bool (fails strict monotonicity)
§3. Non-Archimedean example: ℕ ×ₗ ℕ (imported from ProductFailsSeparation.lean)
§4. Kolmogorov probability space: Fair 6-sided die
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.ProductFailsSeparation

namespace Mettapedia.ProbabilityTheory.Hypercube.Examples

open Mettapedia.ProbabilityTheory.KnuthSkilling
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

open Mettapedia.ProbabilityTheory.KnuthSkilling.SandwichSeparation
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.ProductFailsSeparation

/-!
## §1. Positive Example for KnuthSkillingAlgebraBase: ℕ with Addition

Natural numbers with addition form a `KnuthSkillingAlgebraBase`.
This is the simplest infinite totally ordered monoid with strict monotonicity.

**Note**: This is also a full `KnuthSkillingAlgebra` (Archimedean), but we demonstrate
the weaker structure first.
-/

/-- ℕ with addition forms a KnuthSkillingAlgebraBase.
    Identity = 0, operation = addition. -/
instance : KnuthSkillingAlgebraBase ℕ where
  op := (· + ·)
  ident := 0
  op_assoc := Nat.add_assoc
  op_ident_right := Nat.add_zero
  op_ident_left := Nat.zero_add
  op_strictMono_left := fun y => fun _ _ h => Nat.add_lt_add_right h y
  op_strictMono_right := fun x => fun _ _ h => Nat.add_lt_add_left h x
  ident_le := Nat.zero_le

/-- ℕ addition is commutative. -/
theorem nat_op_comm : ∀ x y : ℕ, op x y = op y x :=
  Nat.add_comm

/-- ℕ is Archimedean: for any x > 0 and any y, some iterate of x exceeds y. -/
theorem nat_archimedean (x y : ℕ) (hx : 0 < x) : ∃ n : ℕ, y < Nat.iterate (· + x) n x := by
  -- We show iterate (· + x) n x = (n + 1) * x
  have key : ∀ n : ℕ, (· + x)^[n] x = (n + 1) * x := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      -- f^[k+1] x = f (f^[k] x) by iterate_succ_apply'
      rw [Function.iterate_succ_apply']
      -- f (f^[k] x) = (f^[k] x) + x = (k+1)*x + x
      simp only [ih]
      ring
  -- For large enough n, (n + 1) * x > y
  use y
  rw [key]
  have h : (y + 1) * x > y := by
    have hx' : x ≥ 1 := hx
    calc (y + 1) * x ≥ (y + 1) * 1 := Nat.mul_le_mul_left (y + 1) hx'
    _ = y + 1 := Nat.mul_one (y + 1)
    _ > y := Nat.lt_succ_self y
  exact h

/-!
## §2. Negative Example: Bool Does NOT Form KnuthSkillingAlgebraBase

Boolean {false, true} with ANY binary operation CANNOT satisfy strict monotonicity.

**Key insight**: Strict monotonicity requires `a < b → f(a) < f(b)`.
With only 2 elements, if `false < true`, then `f(false) < f(true)` means
`f(false) = false` and `f(true) = true`. But then `f` is the identity on {false, true},
and we can't have strict monotonicity in BOTH arguments of a binary operation.
-/

/-- Bool cannot satisfy KnuthSkillingAlgebraBase: strict monotonicity fails.

The proof shows that ANY binary operation on Bool must fail strict monotonicity
in at least one position.

Key insight: in a 2-element set with `a < b`, strict monotonicity `f(a) < f(b)`
forces `f(a) = a` and `f(b) = b`. But a binary operation can't have both
`op(·, y)` and `op(x, ·)` be strictly monotone for all arguments. -/
theorem bool_not_ksAlgebraBase :
    ¬∃ (op : Bool → Bool → Bool) (ident : Bool),
      (∀ x y z, op (op x y) z = op x (op y z)) ∧
      (∀ x, op x ident = x) ∧
      (∀ x, op ident x = x) ∧
      (∀ y, StrictMono (fun x => op x y)) ∧
      (∀ x, StrictMono (fun y => op x y)) ∧
      (∀ x, ident ≤ x) := by
  intro ⟨op, ident, _, _, hleft, hstrictL, _, hle⟩
  -- Case on ident
  cases ident with
  | false =>
    -- ident = false, so ∀x, false ≤ x (trivially true)
    -- From hleft: op false x = x for all x
    -- Strict monotonicity in left arg at y = true:
    --   false < true → op false true < op true true
    --   i.e., true < op true true  (since op false true = true by hleft)
    -- But op true true ∈ {false, true}, and true is maximal, so contradiction!
    have h1 : op false true = true := hleft true
    have h2 : StrictMono (fun x => op x true) := hstrictL true
    have hlt : false < true := Bool.false_lt_true
    have h3 : op false true < op true true := h2 hlt
    rw [h1] at h3
    -- h3 : true < op true true, but op true true ∈ {false, true}
    cases h : op true true with
    | false =>
      -- h3 : true < false, which is impossible since false ≤ true
      rw [h] at h3
      exact not_lt.mpr (Bool.false_le true) h3
    | true =>
      -- h3 : true < true, which is impossible (irreflexivity)
      rw [h] at h3
      exact (lt_irrefl true) h3
  | true =>
    -- ident = true, so ∀x, true ≤ x
    -- This means true ≤ false, but Bool order has false < true, contradiction
    have h : true ≤ false := hle false
    exact not_lt.mpr h Bool.false_lt_true

/-!
## §3. Non-Archimedean Example: ℕ ×ₗ ℕ

This section connects to the existing formalization in ProductFailsSeparation.lean.

The key facts already proven there:
- `NatProdLex` = `ℕ ×ₗ ℕ` with lexicographic order
- `instance : KnuthSkillingAlgebraBase NatProdLex` (componentwise addition)
- `natProdLex_fails_KSSeparation` : ¬ KSSeparation NatProdLex
-/

/-- Re-export: ℕ ×ₗ ℕ with componentwise addition is a KnuthSkillingAlgebraBase. -/
example : KnuthSkillingAlgebraBase NatProdLex :=
  inferInstance

/-- Re-export: ℕ ×ₗ ℕ does NOT satisfy KSSeparation. -/
example : ¬ KSSeparation NatProdLex :=
  natProdLex_fails_KSSeparation

/-!
## §4. Kolmogorov Probability Space: Fair 6-Sided Die

A concrete example of a Kolmogorov probability space:
- Sample space Ω = Fin 6 (outcomes 0..5, representing die faces 1..6)
- σ-algebra = powerset (every subset is measurable in finite case)
- Probability measure: P(A) = |A| / 6 (uniform distribution)

This is the canonical positive example for the Kolmogorov vertex of the hypercube.
-/

/-- The sample space for a fair 6-sided die: outcomes 0,1,2,3,4,5. -/
abbrev DieOutcome := Fin 6

/-- The probability of a single die outcome is 1/6. -/
noncomputable def singleOutcomeProb : ℝ := 1 / 6

/-- All die outcomes. -/
def allDieOutcomes : Finset DieOutcome := Finset.univ

theorem allDieOutcomes_card : allDieOutcomes.card = 6 := by
  simp [allDieOutcomes]

/-- The uniform probability of any event A ⊆ Fin 6 is |A|/6. -/
noncomputable def uniformDieProb (A : Finset DieOutcome) : ℝ := A.card / 6

/-- Empty event has probability 0. -/
theorem uniformDieProb_empty : uniformDieProb ∅ = 0 := by
  simp [uniformDieProb]

/-- Full event has probability 1. -/
theorem uniformDieProb_full : uniformDieProb allDieOutcomes = 1 := by
  simp [uniformDieProb, allDieOutcomes]

/-- Probability is non-negative. -/
theorem uniformDieProb_nonneg (A : Finset DieOutcome) : 0 ≤ uniformDieProb A := by
  simp [uniformDieProb]
  positivity

/-- Probability is at most 1. -/
theorem uniformDieProb_le_one (A : Finset DieOutcome) : uniformDieProb A ≤ 1 := by
  simp only [uniformDieProb]
  have h : A.card ≤ 6 := by
    calc A.card ≤ allDieOutcomes.card := Finset.card_le_card (Finset.subset_univ A)
    _ = 6 := allDieOutcomes_card
  have h6 : (6 : ℝ) > 0 := by norm_num
  rw [div_le_one h6]
  exact Nat.cast_le.mpr h

/-- Additivity for disjoint events. -/
theorem uniformDieProb_additive (A B : Finset DieOutcome) (hAB : Disjoint A B) :
    uniformDieProb (A ∪ B) = uniformDieProb A + uniformDieProb B := by
  simp only [uniformDieProb]
  rw [Finset.card_union_of_disjoint hAB]
  push_cast
  ring

/-- Probability of getting an even number (2, 4, 6 = indices 1, 3, 5). -/
def evenOutcomes : Finset DieOutcome := {1, 3, 5}

theorem evenOutcomes_card : evenOutcomes.card = 3 := by
  native_decide

theorem prob_even : uniformDieProb evenOutcomes = 1 / 2 := by
  simp [uniformDieProb, evenOutcomes_card]
  norm_num

/-- Probability of getting a 6 (index 5). -/
def sixOutcome : Finset DieOutcome := {5}

theorem sixOutcome_card : sixOutcome.card = 1 := by
  native_decide

theorem prob_six : uniformDieProb sixOutcome = 1 / 6 := by
  simp [uniformDieProb, sixOutcome_card]

/-!
### Formal Probability Mass Function

We use `PMF` (Probability Mass Function) from mathlib, which is the correct
abstraction for discrete probability distributions on finite sets.
-/

/-- The uniform PMF on Fin 6: each outcome has probability 1/6. -/
noncomputable def diePMF : PMF DieOutcome := PMF.uniformOfFintype DieOutcome

/-- Each outcome has probability 1/6. -/
theorem diePMF_apply (k : DieOutcome) : diePMF k = 1 / 6 := by
  simp only [diePMF, PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num

/-- The PMF sums to 1 (this is automatic from the PMF definition). -/
theorem diePMF_tsum_eq_one : ∑' k : DieOutcome, diePMF k = 1 := by
  exact diePMF.tsum_coe

/-- Convert PMF to measure: this gives a proper probability measure. -/
noncomputable def dieProbMeasure : MeasureTheory.Measure DieOutcome := diePMF.toMeasure

/-- The die probability measure is a probability measure (total mass = 1). -/
instance dieProbMeasure_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure dieProbMeasure :=
  PMF.toMeasure.isProbabilityMeasure diePMF

/-!
## §5. Imprecise Probability: Interval-Valued Fair Die

An imprecise probability assigns interval [lower, upper] instead of a point value.
This is the positive example for the "imprecise" vertex of the hypercube.

**Key insight**: Imprecise probability arises when we weaken totality - some events
become incomparable rather than having P(A) ≤ P(B) or P(B) ≤ P(A).
-/

/-- An interval probability value: [lower, upper] with lower ≤ upper. -/
@[ext]
structure IntervalProb where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1

/-- Interval probabilities form a partial order (by interval containment). -/
instance : PartialOrder IntervalProb where
  le := fun I J => J.lower ≤ I.lower ∧ I.upper ≤ J.upper  -- J contains I
  le_refl := fun I => ⟨le_refl I.lower, le_refl I.upper⟩
  le_trans := fun I J K hIJ hJK => ⟨le_trans hJK.1 hIJ.1, le_trans hIJ.2 hJK.2⟩
  le_antisymm := fun I J hIJ hJI => by
    ext
    · exact le_antisymm hJI.1 hIJ.1
    · exact le_antisymm hIJ.2 hJI.2

/-- Two intervals are incomparable if neither contains the other. -/
def IntervalProb.incomparable (I J : IntervalProb) : Prop :=
  ¬(I ≤ J) ∧ ¬(J ≤ I)

/-- Example: [0.1, 0.3] and [0.2, 0.4] are incomparable (overlapping but neither contains other). -/
theorem incomparable_example :
    ∃ I J : IntervalProb, IntervalProb.incomparable I J := by
  use ⟨0.1, 0.3, by norm_num, by norm_num, by norm_num⟩
  use ⟨0.2, 0.4, by norm_num, by norm_num, by norm_num⟩
  constructor
  · -- ¬(I ≤ J): need J.lower ≤ I.lower ∧ I.upper ≤ J.upper
    -- J.lower = 0.2 > 0.1 = I.lower, so false
    intro ⟨h1, _⟩
    norm_num at h1
  · -- ¬(J ≤ I): need I.lower ≤ J.lower ∧ J.upper ≤ I.upper
    -- J.upper = 0.4 > 0.3 = I.upper, so false
    intro ⟨_, h2⟩
    norm_num at h2

/-- Imprecise probability for the fair die: each outcome has interval [1/6 - ε, 1/6 + ε].
    This models epistemic uncertainty about the exact probability. -/
noncomputable def impreciseDieProb (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/6) (_k : DieOutcome) :
    IntervalProb where
  lower := 1/6 - ε
  upper := 1/6 + ε
  valid := by linarith
  lower_nonneg := by linarith
  upper_le_one := by linarith

/-- All outcomes have the same interval in this symmetric imprecise model. -/
theorem impreciseDieProb_uniform (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/6) :
    ∀ i j : DieOutcome, impreciseDieProb ε hε hε' i = impreciseDieProb ε hε hε' j := by
  intros
  rfl

/-- The interval bounds sum to 1 (as expected). -/
theorem impreciseDie_lower_sum (ε : ℝ) :
    6 * (1/6 - ε) = 1 - 6*ε := by ring

theorem impreciseDie_upper_sum (ε : ℝ) :
    6 * (1/6 + ε) = 1 + 6*ε := by ring

/-- **Key theorem**: Imprecise probability is NOT totally ordered.
    There exist events with incomparable probabilities. -/
theorem imprecise_not_total :
    ∃ I J : IntervalProb, ¬(I ≤ J ∨ J ≤ I) := by
  obtain ⟨I, J, hIJ⟩ := incomparable_example
  exact ⟨I, J, fun h => h.elim hIJ.1 hIJ.2⟩

/-!
## §6. Non-Archimedean/Hyperreal Probability: Lexicographic Example

The ℕ ×ₗ ℕ model from ProductFailsSeparation.lean gives us "lexicographic probability"
where some events have infinitesimally small probability compared to others.

**Interpretation**: Think of (a, b) as representing probability `a + b·ε` where ε
is an infinitesimal. Then:
- (1, 0) represents "standard" probability 1
- (0, 1) represents infinitesimal probability ε
- (0, n) < (1, 0) for ALL n: no number of infinitesimal events sums to a standard one

This is the formal content of "lexicographic probability" (Blume et al. 1991).
-/

open Prod.Lex in
/-- The "infinitesimal unit" in lexicographic probability. -/
def lexInfinitesimal : NatProdLex := toLex (0, 1)

open Prod.Lex in
/-- The "standard unit" in lexicographic probability. -/
def lexStandard : NatProdLex := toLex (1, 0)

/-- Key property: infinitesimals are smaller than standards. -/
theorem infinitesimal_lt_standard : lexInfinitesimal < lexStandard := by
  simp only [lexInfinitesimal, lexStandard]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl Nat.zero_lt_one)

/-- No finite sum of infinitesimals reaches a standard value.
    This is the key non-Archimedean property: n·ε < 1 for all n. -/
theorem no_finite_sum_reaches_standard :
    ∀ n : ℕ, iterate_op lexInfinitesimal n < lexStandard := by
  intro n
  rw [iterate_op_natProd]
  -- lexInfinitesimal = toLex (0, 1), lexStandard = toLex (1, 0)
  -- iterate_op (toLex (0,1)) n = toLex (n*0, n*1) = toLex (0, n)
  -- Need: toLex (0, n) < toLex (1, 0)
  -- This holds because 0 < 1 in the first component
  have h : (0 : ℕ) < 1 := Nat.zero_lt_one
  simp only [lexInfinitesimal, lexStandard, ofLex_toLex, mul_zero, mul_one]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- **Hyperreal interpretation**: The element (a, b) represents a + b·ε where ε is infinitesimal.
    This gives a concrete model of infinitesimal probability.

    - (0, 0) represents 0
    - (n, 0) represents the standard number n
    - (0, m) represents the infinitesimal m·ε
    - (n, m) represents n + m·ε
-/
def hyperrealComponents (x : NatProdLex) : ℕ × ℕ := ofLex x

/-- Example: "rolling infinitely many dice" scenario.
    Event A = "first die shows 6" has probability ~1/6 (standard)
    Event B = "all dice show 6" has probability 0 (but > 0 infinitesimally)

    In lexicographic probability:
    - P(A) ~ (1, 0) (standard probability)
    - P(B) ~ (0, 1) (infinitesimal probability)
    - P(B) < P(A) always, even though both are "possible" -/
theorem lexicographic_probability_example :
    let eventA := lexStandard   -- "standard event"
    let eventB := lexInfinitesimal  -- "infinitesimal event"
    -- B is strictly less probable than A
    eventB < eventA ∧
    -- But B is still positive (greater than identity)
    ident < eventB := by
  constructor
  · exact infinitesimal_lt_standard
  · simp only [KnuthSkillingAlgebraBase.ident, natProdIdent, lexInfinitesimal]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, Nat.zero_lt_one⟩)

/-!
### Lexicographic Probability in Game Theory

This model formalizes Blume, Brandenburger & Dekel's (1991) "Lexicographic Probabilities
and Choice Under Uncertainty" - where players can have beliefs that distinguish
between "probability zero" events.

**Key application**: In game theory, trembling-hand perfect equilibrium requires
distinguishing between "mistakes" of different magnitudes. Lexicographic probability
provides the formal framework.
-/

/-!
## §7. Summary: The Example Web

We have now FORMALLY proven:

| Example | Positive For | Negative For | Key Theorem |
|---------|--------------|--------------|-------------|
| ℕ with + | KnuthSkillingAlgebraBase, Archimedean | - | `instance`, `nat_archimedean` |
| Bool | - | KnuthSkillingAlgebraBase | `bool_not_ksAlgebraBase` |
| ℕ ×ₗ ℕ | Non-Archimedean, Hyperreal prob | Archimedean, KSSeparation | `no_finite_sum_reaches_standard` |
| Fair Die | Kolmogorov probability | - | `IsProbabilityMeasure dieProbMeasure` |
| Interval Prob | Imprecise probability | Totality | `imprecise_not_total` |
| Lex Prob | Hyperreal/infinitesimal | Archimedean | `lexicographic_probability_example` |

### The Example Web

```
PRECISE (point values)          IMPRECISE (interval values)
        │                               │
        ▼                               ▼
  ┌─────────────┐               ┌───────────────┐
  │  Fair Die   │               │ Interval Die  │
  │  P(k)=1/6   │               │ P(k)∈[L,U]    │
  └─────────────┘               └───────────────┘
        │                               │
        │ weaken Archimedean            │
        ▼                               │
  ┌─────────────┐                       │
  │ Lex Prob    │◄──────────────────────┘
  │ P = a + bε  │   (can combine!)
  └─────────────┘
```

**Key insight**: These are REAL formalizations with PROOFS, not just metadata!
-/

end Mettapedia.ProbabilityTheory.Hypercube.Examples
