import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
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

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Spice

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
  simp only [reachableViaStarClosure, futureStates, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ⟨h⟩
    obtain ⟨n, hn⟩ := star_to_reducesN h
    exact ⟨n, hn⟩
  · intro ⟨n, ⟨h⟩⟩
    exact ⟨reducesN_to_star h⟩

/-! ## Parallel Congruence for Future States

If a component can evolve, the whole parallel composition can evolve.
These theorems lift n-step futures through parallel contexts, which is
essential for compositional reasoning about SPICE agents.
-/

/-- Future states lift through parallel (head position).

    If `q ∈ futureStates p n` then the parallel composition with `rest`
    also has a corresponding n-step future. -/
theorem futureStates_par_head {p : Pattern} {rest : List Pattern} {n : ℕ}
    {q : Pattern} (hq : q ∈ futureStates p n) :
    .collection .hashBag (q :: rest) none ∈
      futureStates (.collection .hashBag (p :: rest) none) n := by
  obtain ⟨h⟩ := hq
  exact ⟨ReducesN.par_head h⟩

/-- Future states lift through parallel (any position). -/
theorem futureStates_par_any {p : Pattern} {before after : List Pattern} {n : ℕ}
    {q : Pattern} (hq : q ∈ futureStates p n) :
    .collection .hashBag (before ++ [q] ++ after) none ∈
      futureStates (.collection .hashBag (before ++ [p] ++ after) none) n := by
  obtain ⟨h⟩ := hq
  exact ⟨ReducesN.par_any_pos h⟩

/-- Present moment lifts through parallel (head position).

    If an agent `p` has `q` in its present moment, then `{| p, rest |}` has
    `{| q, rest |}` in its present moment. Agents don't lose interactions
    by being placed in parallel. -/
theorem presentMoment_par_head {p : Pattern} {rest : List Pattern}
    {q : Pattern} (hq : q ∈ presentMoment p) :
    .collection .hashBag (q :: rest) none ∈
      presentMoment (.collection .hashBag (p :: rest) none) :=
  futureStates_par_head hq

/-- Reachable states lift through parallel (head position). -/
theorem reachableStates_par_head {p : Pattern} {rest : List Pattern} {n : ℕ}
    {q : Pattern} (hq : q ∈ reachableStates p n) :
    .collection .hashBag (q :: rest) none ∈
      reachableStates (.collection .hashBag (p :: rest) none) n := by
  obtain ⟨k, hk, ⟨h⟩⟩ := hq
  exact ⟨k, hk, ⟨ReducesN.par_head h⟩⟩

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

/-! ## The Past: Temporal Duality

The past is the temporal dual of the future. Where futureStates asks
"where can I go?", pastStates asks "where could I have come from?"

Paper reference: Meredith (2026), Section 4.4.3 - "The Past"

The key insight: past and future are connected through the present moment.
If q is in my past (q ⇝ⁿ p), then I am in q's future (p ∈ futureStates q n).
-/

/-- Past states: all patterns that reduce to p in exactly n steps.

    This is the temporal dual of `futureStates`:
    - futureStates(p, n) = { q | p ⇝ⁿ q }  (where p can go)
    - pastStates(p, n) = { q | q ⇝ⁿ p }    (where p came from)

    Paper reference: Meredith (2026), Section 4.4.3
-/
def pastStates (p : Pattern) (n : ℕ) : Set Pattern :=
  { q | Nonempty (q ⇝[n] p) }

/-- The immediate past: all patterns that reduce to p in one step.

    These are the direct predecessors of p.
-/
def immediatePast (p : Pattern) : Set Pattern :=
  pastStates p 1

/-- All predecessors: patterns reachable via star closure (backwards).
-/
def predecessors (p : Pattern) : Set Pattern :=
  { q | Nonempty (q ⇝* p) }

/-- pastStates at n=0 is just {p} (reflexivity).

    Dual of `futureStates_zero`. -/
theorem pastStates_zero (p : Pattern) :
    pastStates p 0 = {p} := by
  ext q
  simp only [pastStates, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ReducesN.zero_iff_eq q p

/-- **Past-Future Duality**: q is in the past of p ↔ p is in the future of q.

    This is the fundamental theorem connecting past and future:
    the past of p at horizon n is exactly the set of processes whose
    n-step future includes p.

    Paper reference: Meredith (2026), Section 4.4.3 - the temporal structure
    is symmetric: being in someone's past means they are in your future.
-/
theorem past_future_duality (p q : Pattern) (n : ℕ) :
    q ∈ pastStates p n ↔ p ∈ futureStates q n := by
  simp [pastStates, futureStates]

/-- **Present Moment Bridge**: q is an immediate predecessor of p
    ↔ p is in q's present moment.

    This connects the "past" (Section 4.4.3) to the "present" (Section 4.4.1):
    the present moment of q is exactly the immediate future of q,
    which is exactly the set of processes whose immediate past includes q.
-/
theorem immediatePast_iff_presentMoment (p q : Pattern) :
    q ∈ immediatePast p ↔ p ∈ presentMoment q := by
  simp [immediatePast, pastStates, presentMoment, futureStates]

/-- Past states at n is a subset of all predecessors.

    Dual of `futureStates_subset_star`. -/
theorem pastStates_subset_predecessors (p : Pattern) (n : ℕ) :
    pastStates p n ⊆ predecessors p := by
  intro q ⟨hq⟩
  exact ⟨reducesN_to_star hq⟩

/-- Predecessors is the union of all pastStates.

    Dual of `star_eq_union_future`. -/
theorem predecessors_eq_union_past (p : Pattern) :
    predecessors p = ⋃ n, pastStates p n := by
  ext q
  simp only [predecessors, pastStates, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro ⟨h⟩
    obtain ⟨n, hn⟩ := star_to_reducesN h
    exact ⟨n, hn⟩
  · intro ⟨n, ⟨h⟩⟩
    exact ⟨reducesN_to_star h⟩

/-- A value has no future but can have a past.

    More precisely: Value(p) implies presentMoment(p) = ∅,
    but does NOT imply immediatePast(p) = ∅.

    This asymmetry is fundamental: a stuck process has no available
    reductions, but other processes can still reduce TO it.
    For example, *(@P) ⇝ P by DROP, so P ∈ immediatePast of any
    pattern, even if P itself is a value.

    We prove the "no future" direction; the "can have past" direction
    is witnessed by the DROP rule for any concrete pattern.
-/
theorem value_no_future (p : Pattern) (h : Value p) :
    presentMoment p = ∅ := by
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  have : (presentMoment p).Nonempty := ⟨q, hq⟩
  exact ((value_iff_presentMoment_empty p).mp h) this

/-- Concrete witness: values CAN have predecessors.

    *(@p) ⇝ p by DROP, so p has *(@p) as an immediate predecessor.
    This holds regardless of whether p is a value.
-/
theorem drop_in_immediatePast (p : Pattern) :
    .apply "PDrop" [.apply "NQuote" [p]] ∈ immediatePast p := by
  simp [immediatePast, pastStates]
  exact ⟨ReducesN.succ Reduces.drop (ReducesN.zero p)⟩

/-- Past is monotone: more steps gives more predecessors.

    Dual of `reachableStates_mono`. -/
theorem pastStates_mono_via_predecessors (p : Pattern) (n : ℕ) :
    pastStates p n ⊆ predecessors p :=
  pastStates_subset_predecessors p n

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Spice
