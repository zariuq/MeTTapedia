/-
# Scale Completeness and σ-Additivity

## The Key Insight

The K&S representation theorem embeds S into (ℝ, +) algebraically, independently of events.
The σ-additivity gap is about whether Θ(S) ⊆ ℝ is *sequentially complete*.

## Architecture

```
K&S Axioms (Finite Additivity)
    │
    │  Gate 1: NAP → Θ : S ↪ (ℝ,+) exists (Hölder/Alimov)
    ▼
Representation Theorem (scale-only, event-free)
    │
    │  Gate 2: Sequential Completeness → Θ(S) closed under bounded ω-sups
    │         + Scott Continuity of v → v preserves directed sups
    ▼
σ-Additivity: μ = Θ ∘ v is countably additive
```

## Design Principles

1. **Integrated with K&S stack**: Builds on RepresentationResult from Additive/Representation.lean
2. **Hölder/Alimov (NAP) route**: Uses NoAnomalousPairs, NOT require KSSeparation
3. **Θ from representation theorem**: Not a free parameter
4. **Automatic preservation**: Θ commutes with seqSup by construction (closure property)
5. **Sequential completeness**: We only need ω-chains, not full Dedekind completeness

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Billingsley, "Probability and Measure" (1995), §1.4 for finite→σ bridge
-/

import Mathlib.Order.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.Model
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Representation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open KnuthSkillingMonoidBase KSSemigroupBase
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

/-! ## Section 1: Sequential Completeness of the Scale -/

/-! ### Unbundled Predicates

Following the K&S design pattern: each axiom has both:
- An unbundled **predicate** (`def XxxProp`) for flexibility
- A bundled **class** (`class KSXxx`) for typeclass inference

This matches the pattern used for `SeparationProp` / `KSSeparation`. -/

/-- **Unbundled predicate**: Scale completeness property.

Θ(S) ⊆ ℝ is closed under suprema of bounded increasing ω-sequences.
This is the predicate form; see `KSScaleComplete` for the class form. -/
def ScaleCompleteProp {S : Type*} [KSSemigroupBase S] (R : RepresentationResult S) : Prop :=
  ∀ (f : ℕ → S), Monotone f → BddAbove (Set.range (R.Θ ∘ f)) →
    ∃ s : S, R.Θ s = ⨆ n, R.Θ (f n)

/-- Sequential completeness of the scale, relative to a K&S representation.

Given a representation Θ from the Hölder/Alimov embedding (via NoAnomalousPairs),
this says: Θ(S) ⊆ ℝ is closed under suprema of bounded increasing ω-sequences.

This is **sequential completeness** (ω-completeness), NOT full Dedekind completeness.
It's the minimal axiom bridging K&S finite additivity to σ-additivity.

**Key Design**: Θ-preservation is automatic from the closure property - we don't need
to axiomatize that Θ preserves sups separately, it falls out of the definition. -/
class KSScaleComplete (S : Type*) [KSSemigroupBase S] (R : RepresentationResult S) where
  /-- Θ(S) is closed: bounded increasing sequences have preimages of their sups -/
  closed_seqSup : ∀ (f : ℕ → S), Monotone f → BddAbove (Set.range (R.Θ ∘ f)) →
    ∃ s : S, R.Θ s = ⨆ n, R.Θ (f n)

namespace KSScaleComplete

variable {S : Type*} [KSSemigroupBase S] (R : RepresentationResult S) [KSScaleComplete S R]

/-- The supremum element in S (chosen via closure property).

This exists by KSScaleComplete: there's some s ∈ S with Θ(s) = sup Θ(fₙ). -/
noncomputable def seqSup (f : ℕ → S) (hf : Monotone f)
    (hbdd : BddAbove (Set.range (R.Θ ∘ f))) : S :=
  Classical.choose (closed_seqSup (R := R) f hf hbdd)

/-- Θ automatically preserves seqSup by construction.

This is NOT an axiom - it's derived from the closure property.
The closure says "∃ s, Θ s = sup Θ(fₙ)", and seqSup picks that s. -/
theorem Θ_seqSup (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f))) :
    R.Θ (seqSup R f hf hbdd) = ⨆ n, R.Θ (f n) :=
  Classical.choose_spec (closed_seqSup (R := R) f hf hbdd)

/-- seqSup is an upper bound: each f n ≤ seqSup f -/
theorem le_seqSup (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f))) (n : ℕ) :
    f n ≤ seqSup R f hf hbdd := by
  rw [R.order_preserving]
  rw [Θ_seqSup]
  exact le_ciSup hbdd n

/-- seqSup is the least upper bound -/
theorem seqSup_le (f : ℕ → S) (hf : Monotone f) (hbdd : BddAbove (Set.range (R.Θ ∘ f)))
    (b : S) (hb : ∀ n, f n ≤ b) : seqSup R f hf hbdd ≤ b := by
  rw [R.order_preserving]
  rw [Θ_seqSup]
  apply ciSup_le
  intro n
  exact (R.order_preserving (f n) b).mp (hb n)

end KSScaleComplete

/-! ### Connection to Unbundled Predicate -/

/-- The `KSScaleComplete` instance satisfies the unbundled `ScaleCompleteProp` predicate. -/
theorem KSScaleComplete.scaleCompleteProp {S : Type*} [KSSemigroupBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] : ScaleCompleteProp R :=
  KSScaleComplete.closed_seqSup

/-! ## Section 2: σ-Complete Events -/

/-- **Unbundled predicate**: σ-complete events property.

Events have countable joins. This is the predicate form; see `SigmaCompleteEvents` for the class form. -/
def SigmaCompleteEventsProp (E : Type*) [PlausibilitySpace E] : Prop :=
  ∃ (iSup : (ℕ → E) → E),
    (∀ (f : ℕ → E) (n : ℕ), f n ≤ iSup f) ∧
    (∀ (f : ℕ → E) (b : E), (∀ n, f n ≤ b) → iSup f ≤ b)

/-- σ-complete event structure: events have countable joins.

This extends PlausibilitySpace with countable joins (σ-frame structure).
The key operation is `iSup : (ℕ → E) → E` for countable families. -/
class SigmaCompleteEvents (E : Type*) extends PlausibilitySpace E where
  /-- Countable supremum exists -/
  iSup : (ℕ → E) → E
  /-- iSup is an upper bound -/
  le_iSup : ∀ (f : ℕ → E) (n : ℕ), f n ≤ iSup f
  /-- iSup is the least upper bound -/
  iSup_le : ∀ (f : ℕ → E) (b : E), (∀ n, f n ≤ b) → iSup f ≤ b

namespace SigmaCompleteEvents

variable {E : Type*} [SigmaCompleteEvents E]

/-- Countable union of events -/
def countableUnion (f : ℕ → E) : E := iSup f

/-- The iSup of a monotone sequence -/
theorem iSup_mono {f : ℕ → E} (_hf : Monotone f) : ∀ n, f n ≤ iSup f := le_iSup f

/-- iSup of a constant sequence -/
theorem iSup_eq_of_const {f : ℕ → E} {a : E} (h : ∀ n, f n = a) :
    iSup f = a := by
  apply le_antisymm
  · exact iSup_le f a (fun n => le_of_eq (h n))
  · have : a = f 0 := (h 0).symm
    rw [this]
    exact le_iSup f 0

end SigmaCompleteEvents

/-! ### Connection to Unbundled Predicate -/

/-- The `SigmaCompleteEvents` instance satisfies the unbundled `SigmaCompleteEventsProp` predicate. -/
theorem SigmaCompleteEvents.sigmaCompleteEventsProp {E : Type*} [inst : SigmaCompleteEvents E] :
    SigmaCompleteEventsProp E :=
  ⟨inst.iSup, inst.le_iSup, inst.iSup_le⟩

/-! ## Section 3: Scott Continuity for Valuations -/

/-- **Unbundled predicate**: Scott continuity property.

v preserves directed suprema (ω-chains). This is the predicate form;
see `KSScottContinuous` for the class form. -/
def ScottContinuousProp {E S : Type*} [SigmaCompleteEvents E] [KSSemigroupBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] (v : E → S) : Prop :=
  ∀ (f : ℕ → E), Monotone f →
    ∃ _hf_mono : Monotone (R.Θ ∘ v ∘ f),
    ∃ _hf_bdd : BddAbove (Set.range (R.Θ ∘ v ∘ f)),
    R.Θ (v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (v (f n))

/-- Scott continuity: v preserves directed suprema (ω-chains).

Phrased via the representation Θ since S may not have internal sups.
The key property: when events increase to a limit, their Θ-images converge
to the Θ-image of the limit.

This is the second gate axiom (alongside scale completeness) needed for σ-additivity.

**Identity note**: The unbundled predicate is identity-free; the bundled class
`KSScottContinuous` requires identity only because it extends `KSModel`. -/
class KSScottContinuous (E S : Type*) [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
    (R : RepresentationResult S) [KSScaleComplete S R] extends KSModel E S where
  /-- v preserves countable sups of increasing sequences (via Θ) -/
  v_scott : ∀ (f : ℕ → E), Monotone f →
    ∃ _hf_mono : Monotone (R.Θ ∘ v ∘ f),
    ∃ _hf_bdd : BddAbove (Set.range (R.Θ ∘ v ∘ f)),
    R.Θ (v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (v (f n))

namespace KSScottContinuous

variable {E S : Type*} [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
variable (R : RepresentationResult S) [KSScaleComplete S R]
variable (m : KSScottContinuous E S R)

/-- The valuation of a countable increasing union equals the sup of valuations (via Θ) -/
theorem v_countable_union_eq (f : ℕ → E) (hf : Monotone f) :
    R.Θ (m.v (SigmaCompleteEvents.iSup f)) = ⨆ n, R.Θ (m.v (f n)) := by
  obtain ⟨_, _, heq⟩ := m.v_scott f hf
  exact heq

end KSScottContinuous

/-! ### Connection to Unbundled Predicate -/

/-- The `KSScottContinuous` instance satisfies the unbundled `ScottContinuousProp` predicate. -/
theorem KSScottContinuous.scottContinuousProp {E S : Type*} [SigmaCompleteEvents E]
    [KnuthSkillingMonoidBase S] (R : RepresentationResult S) [KSScaleComplete S R]
    (m : KSScottContinuous E S R) : ScottContinuousProp R m.v :=
  m.v_scott

/-! ## Section 4: Pairwise Disjointness -/

/-- Pairwise disjoint family of events -/
def PairwiseDisjoint' {E : Type*} [SemilatticeInf E] [OrderBot E] (f : ℕ → E) : Prop :=
  ∀ i j, i ≠ j → Disjoint (f i) (f j)

/-! ## Section 5: Partial Sums Infrastructure -/

/-- Partial unions: the finite union of the first n events -/
def partialUnion {E : Type*} [PlausibilitySpace E] (f : ℕ → E) (n : ℕ) : E :=
  Finset.sup (Finset.range n) f

/-- Partial unions are monotone -/
theorem partialUnion_mono {E : Type*} [PlausibilitySpace E] (f : ℕ → E) :
    Monotone (partialUnion f) := by
  intro m n hmn
  apply Finset.sup_mono
  exact Finset.range_mono hmn

/-- Partial union at n+1 extends by f n -/
theorem partialUnion_succ {E : Type*} [PlausibilitySpace E] (f : ℕ → E) (n : ℕ) :
    partialUnion f (n + 1) = partialUnion f n ⊔ f n := by
  simp only [partialUnion, Finset.range_add_one, Finset.sup_insert]
  rw [sup_comm]

/-- iSup of f equals iSup of partial unions -/
theorem iSup_eq_iSup_partialUnion {E : Type*} [SigmaCompleteEvents E] (f : ℕ → E) :
    SigmaCompleteEvents.iSup f = SigmaCompleteEvents.iSup (partialUnion f) := by
  apply le_antisymm
  · -- Each f n ≤ partialUnion f (n+1) ≤ iSup (partialUnion f)
    apply SigmaCompleteEvents.iSup_le
    intro n
    have h1 : f n ≤ partialUnion f (n + 1) := by
      simp only [partialUnion]
      exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_add_one n))
    exact le_trans h1 (SigmaCompleteEvents.le_iSup (partialUnion f) (n + 1))
  · -- Each partialUnion f n ≤ iSup f
    apply SigmaCompleteEvents.iSup_le
    intro n
    simp only [partialUnion]
    apply Finset.sup_le
    intro i _
    exact SigmaCompleteEvents.le_iSup f i

/-! ## Section 6: Finite Additivity for n terms -/

/-- For a pairwise disjoint family in range n, partialUnion f n is disjoint from f n -/
theorem disjoint_partialUnion_of_pairwiseDisjoint {E : Type*} [PlausibilitySpace E]
    {f : ℕ → E} (hd : PairwiseDisjoint' f) (n : ℕ) :
    Disjoint (partialUnion f n) (f n) := by
  simp only [partialUnion]
  rw [Finset.disjoint_sup_left]
  intro i hi
  exact hd i n (Finset.mem_range.mp hi).ne

/-- Finite additivity: Θ(v(partialUnion f n)) = ∑ i in range n, Θ(v(f i))

Requires NormalizedRepresentationResult for the base case Θ(ident) = 0. -/
theorem Θ_v_partialUnion_eq_sum {E S : Type*} [PlausibilitySpace E] [KnuthSkillingMonoidBase S]
    (R : NormalizedRepresentationResult S) (m : KSModel E S)
    (f : ℕ → E) (hd : PairwiseDisjoint' f) (n : ℕ) :
    R.Θ (m.v (partialUnion f n)) = ∑ i ∈ Finset.range n, R.Θ (m.v (f i)) := by
  induction n with
  | zero =>
    simp only [partialUnion, Finset.range_zero, Finset.sup_empty, Finset.sum_empty]
    rw [m.v_bot, R.ident_zero]
  | succ n ih =>
    rw [partialUnion_succ, Finset.sum_range_succ]
    have hdisj := disjoint_partialUnion_of_pairwiseDisjoint hd n
    rw [m.v_sup_of_disjoint hdisj, R.additive, ih]

/-! ## Section 7: Key Lemmas for tsum-iSup Connection -/

/-- **Key Lemma**: For nonnegative sequences with bounded partial sums, tsum equals the iSup of partial sums.

For f : ℕ → ℝ with f ≥ 0 and bounded partial sums:
- The series is summable (by completeness)
- The tsum equals the limit of partial sums (definition of HasSum)
- For monotone bounded sequences, the limit equals the supremum

**Note**: The boundedness hypothesis is necessary - without it, the equality may not hold
(tsum = 0 for non-summable by Lean convention, but ciSup is undefined for unbounded sets). -/
theorem tsum_eq_iSup_partialSums_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hbdd : BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, f i))) :
    ∑' n, f n = ⨆ n, ∑ i ∈ Finset.range n, f i := by
  -- Extract the bound explicitly
  obtain ⟨C, hC⟩ := hbdd
  -- Bounded partial sums + nonnegative terms → summable
  have hsummable : Summable f := summable_of_sum_range_le (c := C) hf (fun n => hC (Set.mem_range_self n))
  -- The partial sums are monotone (adding nonnegative terms)
  have hmono : Monotone (fun n => ∑ i ∈ Finset.range n, f i) := by
    intro m n hmn
    apply Finset.sum_mono_set_of_nonneg hf
    exact Finset.range_mono hmn
  -- Reconstruct hbdd for tendsto_atTop_ciSup
  have hbdd' : BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, f i)) := ⟨C, hC⟩
  -- Partial sums converge to their supremum (monotone + bounded → converges to sup)
  have htends : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop
      (nhds (⨆ n, ∑ i ∈ Finset.range n, f i)) :=
    tendsto_atTop_ciSup hmono hbdd'
  -- tsum = limit of partial sums (definition of HasSum)
  have hsum : HasSum f (⨆ n, ∑ i ∈ Finset.range n, f i) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]
    · simpa only [Real.norm_of_nonneg (hf _)] using htends
    · exact hsummable.norm
  exact hsum.tsum_eq

/-! ## Section 8: The Main Theorem -/

/-- **K&S σ-Additivity Theorem**

Given:
- S with a K&S representation R (from Hölder/Alimov via NoAnomalousPairs)
- KSScaleComplete S R (Θ(S) is sequentially closed)
- KSScottContinuous E S R (v preserves directed sups)

Then μ = R.Θ ∘ v is σ-additive on disjoint families.

This is the clean bridge from K&S finite additivity to Kolmogorov σ-additivity,
building on the representation theorem without importing σ-algebra structure.

**Two independent gates**:
- Gate 1 (NAP): For Θ's existence (via Hölder/Alimov, already formalized)
- Gate 2 (Completeness + Scott): For σ-additivity (this theorem)

**Note**: This theorem requires NormalizedRepresentationResult (with Θ(ident) = 0)
for the base case of the finite additivity induction. -/
theorem ks_sigma_additive
    {E S : Type*} [SigmaCompleteEvents E] [KnuthSkillingMonoidBase S]
    (R : NormalizedRepresentationResult S) [KSScaleComplete S R.toRepresentationResult]
    (m : KSScottContinuous E S R.toRepresentationResult)
    (f : ℕ → E) (hd : PairwiseDisjoint' f) :
    let μ := R.Θ ∘ m.v
    μ (SigmaCompleteEvents.iSup f) = ∑' n, μ (f n) := by
  intro μ
  -- Step 1: The iSup of f equals iSup of partial unions
  rw [iSup_eq_iSup_partialUnion f]
  -- Unfold μ for rewriting
  show R.Θ (m.v (SigmaCompleteEvents.iSup (partialUnion f))) = ∑' n, R.Θ (m.v (f n))
  -- Step 2: Apply Scott continuity to get Θ(v(iSup (partialUnion f))) = ⨆ n, Θ(v(partialUnion f n))
  have hscott := m.v_countable_union_eq R.toRepresentationResult (partialUnion f) (partialUnion_mono f)
  rw [hscott]
  -- Step 3: By finite additivity, Θ(v(partialUnion f n)) = ∑ i < n, μ(f i)
  have hfinite : ∀ n, R.Θ (m.v (partialUnion f n)) = ∑ i ∈ Finset.range n, μ (f i) := by
    intro n
    induction n with
    | zero =>
      simp only [partialUnion, Finset.range_zero, Finset.sup_empty, Finset.sum_empty]
      rw [m.v_bot]
      exact R.ident_zero
    | succ n ih =>
      rw [partialUnion_succ, Finset.sum_range_succ]
      have hdisj := disjoint_partialUnion_of_pairwiseDisjoint hd n
      rw [m.v_sup_of_disjoint hdisj, R.additive, ih]
      rfl
  -- Now goal is: ⨆ n, R.Θ (m.v (partialUnion f n)) = ∑' n, R.Θ (m.v (f n))
  -- Apply hfinite to rewrite LHS
  have hfinite' : (fun n => R.Θ (m.v (partialUnion f n))) = (fun n => ∑ i ∈ Finset.range n, R.Θ (m.v (f i))) := by
    ext n; exact hfinite n
  rw [hfinite']
  -- Now goal is: ⨆ n, ∑ i ∈ Finset.range n, R.Θ (m.v (f i)) = ∑' n, R.Θ (m.v (f n))
  -- μ ≥ 0 since Θ preserves order and v(a) ≥ v(⊥) = ident, so Θ(v(a)) ≥ Θ(ident) = 0
  have hμ_nonneg : ∀ n, 0 ≤ R.Θ (m.v (f n)) := by
    intro n
    have h := m.v_ident_le (f n)
    rw [← R.ident_zero]
    exact (R.order_preserving ident (m.v (f n))).mp h
  -- Step 4: Get boundedness from Scott continuity on the partial unions
  -- Scott continuity on partialUnion gives bounded Θ(v(partialUnion f n))
  obtain ⟨_, hbdd_pu, _⟩ := m.v_scott (partialUnion f) (partialUnion_mono f)
  -- Convert boundedness: Θ(v(partialUnion f n)) = ∑ i < n, μ(f i) by hfinite
  have hbdd : BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, R.Θ (m.v (f i)))) := by
    obtain ⟨c, hc⟩ := hbdd_pu
    use c
    intro x hx
    obtain ⟨n, hn⟩ := hx
    simp only at hn
    rw [← hn]
    -- hfinite n : R.Θ (m.v (partialUnion f n)) = ∑ i ∈ Finset.range n, μ (f i)
    -- But μ = R.Θ ∘ m.v, so ∑ i ∈ Finset.range n, μ (f i) = ∑ i ∈ Finset.range n, R.Θ (m.v (f i))
    have heq : ∑ i ∈ Finset.range n, R.Θ (m.v (f i)) = R.Θ (m.v (partialUnion f n)) := by
      rw [hfinite n]; rfl
    rw [heq]
    exact hc (Set.mem_range_self n)
  -- Apply the key lemma connecting iSup of partial sums to tsum for nonnegative sequences
  exact (tsum_eq_iSup_partialSums_nonneg hμ_nonneg hbdd).symm

/-! ## Section 9: NNReal Instance -/

/-- NNReal with identity and coercion to ℝ forms a valid K&S representation.

This provides the standard model where Θ is just coercion to ℝ. -/
def nnrealRepresentation : RepresentationResult NNReal where
  Θ := fun x => x.val
  order_preserving := fun a b => NNReal.coe_le_coe
  additive := fun x y => by
    show (op x y).val = x.val + y.val
    -- op on NNReal is addition, defined in Model.lean
    rfl

/-- NNReal is sequentially complete (inherits from ℝ's conditional completeness).

The image Θ(NNReal) = [0, ∞) ⊆ ℝ is closed under bounded ω-sups. -/
instance instKSScaleCompleteNNReal : KSScaleComplete NNReal nnrealRepresentation where
  closed_seqSup := fun f _hf hbdd => by
    -- The sequence (f n).val is bounded and monotone in ℝ
    -- Its sup exists in [0, ∞) since NNReal is conditionally complete
    have hne : (Set.range (fun n => (f n).val)).Nonempty := ⟨(f 0).val, ⟨0, rfl⟩⟩
    -- The sup is nonnegative since all terms are
    have hsup_nonneg : 0 ≤ ⨆ n, (f n).val := by
      apply Real.iSup_nonneg
      intro n
      exact (f n).coe_nonneg
    -- Construct the NNReal sup
    use ⟨⨆ n, (f n).val, hsup_nonneg⟩
    rfl

/-- The standard model NNReal satisfies scale completeness. -/
theorem nnreal_scale_complete : KSScaleComplete NNReal nnrealRepresentation := inferInstance

/-! ## Section 8: Summary

We have established the clean path to σ-additivity:

```
K&S Axioms (Finite Additivity)
        +
NoAnomalousPairs (NAP)
        ↓
Representation Theorem: Θ : S ↪ (ℝ,+)
        +
KSScaleComplete S R (Θ(S) sequentially closed)
        +
KSScottContinuous E S R (v preserves directed sups)
        ↓
σ-Additivity: μ = Θ ∘ v is countably additive
```

**Key Design Choices**:

1. **Integrated with K&S stack**: Uses `RepresentationResult` from Additive/Representation.lean
2. **Closure-based completeness**: Θ-preservation is automatic (not an axiom)
3. **Scott continuity via Θ**: Since S may lack internal sups
4. **Hölder/Alimov route**: Uses NoAnomalousPairs, not KSSeparation
5. **Two independent gates**: NAP for Θ's existence; Completeness+Scott for σ-additivity

**What we did NOT assume**:
- Events form a σ-algebra (we use σ-complete lattice instead)
- Full Dedekind completeness (we only need sequential/ω-completeness)
- The valuation is continuous a priori (derived from Scott continuity of v)
- Any topology on events (continuity lives on the scale via Θ)
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling
