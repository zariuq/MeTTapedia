import Mettapedia.OSLF.RhoCalculus.MultiStep
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Spice Calculus: n-Step Lookahead for ρ-Calculus

Formalizes Meredith's spice calculus - the lookahead variant giving
agents temporal structure (past, present, future).

Based on: "How the Agents Got Their Present Moment" (Meredith, 2026)

## The Spice Rule

The spice rule generalizes the COMM rule with n-step lookahead:

```
Q --n--> { Q1, ..., Qm }  (where Qi are processes reachable in ≤n steps)
==>
for(y <- x)P | x!(Q) → P{ @{ Q1, ..., Qm } / y }
```

When n=0: recovers original ρ-calculus (just {Q} itself)
When n>0: agents get precognitive ability

## Temporal Structure

- **Past**: Trace of reductions (continuation-saturated form)
- **Present**: 1-step reachability (the "present moment")
- **Future**: n-step lookahead (precognition)

## Main Definitions

* `futureStates p n` - All states reachable in exactly n steps from p
* `presentMoment p` - All states reachable in exactly 1 step from p
* `reachableStates p n` - All states reachable in ≤n steps from p

## References

- Meredith, L.G. (2026): "How the Agents Got Their Present Moment"
- Meredith & Radestock (2005): "A Reflective Higher-Order Calculus"
-/

namespace Mettapedia.OSLF.RhoCalculus.Spice

open Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Future states: all patterns reachable in exactly n steps.

    This is the set of patterns that an agent with n-step lookahead
    can "see" into the future.

    Note: Finiteness depends on the pattern structure; not proven here.
-/
def futureStates (p : Pattern) (n : ℕ) : Set Pattern :=
  { q | Nonempty (p ⇝[n] q) }

/-- Present moment: all patterns reachable in exactly 1 step.

    This is the agent's "now" - the immediate interactions available.
-/
def presentMoment (p : Pattern) : Set Pattern :=
  futureStates p 1

/-- Reachable states: all patterns reachable in ≤n steps.

    This is the union of all futureStates for k ≤ n.
-/
def reachableStates (p : Pattern) (n : ℕ) : Set Pattern :=
  { q | ∃ k ≤ n, Nonempty (p ⇝[k] q) }

/-! ## Basic Properties -/

/-- The present moment equals 1-step future -/
theorem presentMoment_eq_future_one (p : Pattern) :
    presentMoment p = futureStates p 1 :=
  rfl

/-- n=0 future is just the pattern itself (reflexivity) -/
theorem futureStates_zero (p : Pattern) :
    futureStates p 0 = {p} := by
  ext q
  simp only [futureStates, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact (ReducesN.zero_iff_eq p q).trans eq_comm

/-- Present moment is non-empty only if p can reduce -/
theorem presentMoment_nonempty_iff_reduces (p : Pattern) :
    (presentMoment p).Nonempty ↔ ∃ q, Nonempty (Reduces p q) := by
  simp [presentMoment, futureStates]
  constructor
  · intro ⟨q, h⟩
    exact ⟨q, (ReducesN.one_iff_reduces p q).mp h⟩
  · intro ⟨q, h⟩
    exact ⟨q, (ReducesN.one_iff_reduces p q).mpr h⟩

/-- **Value ↔ empty present moment**: A pattern is a value (normal form)
    if and only if its present moment is empty.

    This connects the semantic `Value` (= `NormalForm` = irreducibility) to
    the paper's "present moment" concept from "How the Agents Got Their
    Present Moment" (Meredith, 2026).

    An agent whose present moment is empty has no available interactions —
    it is stuck, i.e., a value. -/
theorem value_iff_presentMoment_empty (p : Pattern) :
    Value p ↔ ¬ (presentMoment p).Nonempty := by
  simp only [Value, NormalForm, CanStep]
  rw [presentMoment_nonempty_iff_reduces]

/-- Reachable states at 0 is just p itself -/
theorem reachableStates_zero (p : Pattern) :
    reachableStates p 0 = {p} := by
  ext q
  simp only [reachableStates, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨k, hk, h⟩
    have : k = 0 := Nat.le_zero.mp hk
    rw [this] at h
    exact ((ReducesN.zero_iff_eq p q).mp h).symm
  · intro h
    exact ⟨0, Nat.le_refl 0, (ReducesN.zero_iff_eq p q).mpr h.symm⟩

/-- Reachable states is monotone in n -/
theorem reachableStates_mono {p : Pattern} {n m : ℕ} (h : n ≤ m) :
    reachableStates p n ⊆ reachableStates p m := by
  intro q ⟨k, hk, hr⟩
  exact ⟨k, Nat.le_trans hk h, hr⟩

/-- Future states at n is a subset of reachable states at n -/
theorem futureStates_subset_reachable (p : Pattern) (n : ℕ) :
    futureStates p n ⊆ reachableStates p n := by
  intro q hq
  exact ⟨n, Nat.le_refl n, hq⟩

/-! ## Connection to Star Closure -/

/-- Reachable states via star closure -/
def reachableViaStarClosure (p : Pattern) : Set Pattern :=
  { q | Nonempty (p ⇝* q) }

/-- If q is reachable in n steps, it's reachable via star -/
theorem futureStates_subset_star (p : Pattern) (n : ℕ) :
    futureStates p n ⊆ reachableViaStarClosure p := by
  intro q ⟨hq⟩
  exact ⟨reducesN_to_star hq⟩

/-- If q is reachable in ≤n steps, it's reachable via star -/
theorem reachableStates_subset_star (p : Pattern) (n : ℕ) :
    reachableStates p n ⊆ reachableViaStarClosure p := by
  intro q ⟨k, _, ⟨hk⟩⟩
  exact ⟨reducesN_to_star hk⟩

/-- Helper: star closure implies n-step for some n -/
theorem star_to_reducesN {p q : Pattern} (h : p ⇝* q) : ∃ n, Nonempty (p ⇝[n] q) := by
  induction h with
  | refl =>
    use 0
    exact ⟨ReducesN.zero _⟩
  | @step p' q' r' h_step _ ih =>
    obtain ⟨n, ⟨hn⟩⟩ := ih
    use n + 1
    have ⟨h1⟩ : Nonempty (p' ⇝[1] q') := (ReducesN.one_iff_reduces p' q').mpr ⟨h_step⟩
    have concat : p' ⇝[1 + n] r' := reducesN_concat h1 hn
    rw [Nat.add_comm] at concat
    exact ⟨concat⟩

/-- The reachable states via star is the union of all futureStates.

    This is the fundamental theorem connecting star closure to n-step reachability:
    every pattern reachable via reflexive-transitive closure is reachable in
    exactly n steps for some finite n.
-/
theorem star_eq_union_future (p : Pattern) :
    reachableViaStarClosure p = ⋃ n, futureStates p n := by
  ext q
  simp [reachableViaStarClosure, futureStates]
  constructor
  · intro ⟨h⟩
    obtain ⟨n, hn⟩ := star_to_reducesN h
    exact ⟨n, hn⟩
  · intro ⟨n, ⟨h⟩⟩
    exact ⟨reducesN_to_star h⟩

/-! ## Spice Evaluation (Precognitive Agents)

The spice calculus allows agents to evaluate their environment n steps into
the future before committing to an interaction.
-/

/-- Spice evaluation: collect all reachable states in ≤n steps.

    This is what an agent with n-step lookahead "sees" before making a choice.

    Note: In practice, this would be computed by iterative reduction, but we
    define it here abstractly via the reachability predicate.
-/
def spiceEval (p : Pattern) (n : ℕ) : Set Pattern :=
  reachableStates p n

/-- Spice at n=0 gives the current state (just p itself).

    Note: This is NOT the "present moment" (which is 1-step reachability).
    The present moment is defined as futureStates p 1.
-/
theorem spice_zero_is_current (p : Pattern) :
    spiceEval p 0 = {p} := by
  simp [spiceEval]
  exact reachableStates_zero p

/-- Spice is monotone: more lookahead gives more information -/
theorem spice_mono {p : Pattern} {n m : ℕ} (h : n ≤ m) :
    spiceEval p n ⊆ spiceEval p m := by
  simp [spiceEval]
  exact reachableStates_mono h

/-- spiceEval at n=0 is finite (singleton set {q}).

    This is the base case for finiteness and is unconditionally true:
    `spiceEval q 0 = {q}` is a singleton, hence finite.

    General finiteness for n>0 requires finite branching (each pattern has
    finitely many 1-step successors up to structural congruence). This is
    standard in process calculus but not provable here because `Reduces.equiv`
    combined with `AlphaEquiv.lambda_rename` produces infinitely many
    syntactically distinct alpha-variants. A quotient by `StructuralCongruence`
    would make general finiteness provable.
-/
theorem spiceEval_zero_finite (q : Pattern) : (spiceEval q 0).Finite := by
  simp only [spiceEval, reachableStates_zero]
  exact Set.toFinite {q}

/-! ## Temporal Horizon

The "temporal horizon" of an agent is how far it can see into the future.
-/

/-- An agent with temporal horizon n can see n steps ahead -/
def temporalHorizon (n : ℕ) : Prop :=
  n > 0

/-- The present moment is the minimal temporal horizon -/
theorem present_is_minimal_horizon :
    temporalHorizon 1 :=
  Nat.one_pos

/-! ## Summary

This file establishes the spice calculus foundations:

**Core definitions:**
1. ✅ **futureStates**: Exact n-step reachability
2. ✅ **presentMoment**: 1-step reachability (the "now")
3. ✅ **reachableStates**: ≤n-step reachability
4. ✅ **spiceEval**: n-step lookahead evaluation

**Key theorems (all proven, 0 sorries, 0 axioms):**
5. ✅ **spice_zero_is_current**: n=0 gives current state {p}
6. ✅ **spice_mono**: Monotonicity of lookahead
7. ✅ **star_eq_union_future**: Star = ⋃ₙ futureStates
8. ✅ **spiceEval_zero_finite**: {q} is finite (for n=0 CommRule usage)
9. ✅ **value_iff_presentMoment_empty**: Value p ↔ empty present moment
-/

end Mettapedia.OSLF.RhoCalculus.Spice
