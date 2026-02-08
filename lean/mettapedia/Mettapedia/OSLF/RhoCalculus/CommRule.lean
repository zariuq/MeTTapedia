import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.RhoCalculus.SpiceRule
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Sort

/-!
# COMM Rule with n-Step Lookahead (Spice Calculus)

This file formalizes the spice calculus operational semantics: the COMM rule
with n-step lookahead that gives agents "precognition".

## The Spice COMM Rule

**Original ρ-calculus COMM**:
```
for(y <- x)P | x!(Q) → P{ @Q / y }
```

**Spice COMM (with n-step lookahead)**:
```
Q --n--> { Q₁, ..., Qₘ }  (where Qᵢ are states reachable in ≤n steps)
==>
for(y <- x)P | x!(Q) → P{ @{ Q₁, ..., Qₘ } / y }
```

## Key Insight

When n=0: spice COMM recovers original ρ-calculus COMM
When n>0: agents get "precognitive" ability - they see futures before committing

## Main Definitions

* `SpiceCommReduction` - COMM with n-step lookahead
* `spiceCommSubst` - Substitution with future states
* `spice_comm_preserves_reduces` - Spice COMM is compatible with base reduction

## References

- Meredith (2026): "How the Agents Got Their Present Moment"
- Meredith & Stay (2005): "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.RhoCalculus.SpiceComm

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.RhoCalculus.Spice
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Spice COMM Substitution

The key difference: we substitute the SET of future states, not just the current state.
-/

/-- Helper: Convert a finite set to a list.

    Uses mathlib's Set.Finite.toFinset followed by Finset.toList.
    The operation is noncomputable because it relies on classical choice.
-/
noncomputable def finiteSetToList (s : Set Pattern) (h : Set.Finite s) : List Pattern :=
  (Set.Finite.toFinset h).toList

/-- Convert finite set of future states to Pattern using hashSet semantics.

    **Key design decision**: Singletons are unwrapped to their element.

    **Rationale**:
    - Standard process calculus: `P | 0 ≡ P` (parallel with nil = just P)
    - For n=0: `spiceEval q 0 = {q}`, so we get `q` (recovers standard COMM)
    - For n>0: Multiple futures remain as collections (spice behavior)

    **Implementation**:
    - Singleton `{p}` → unwrap to `p` (structural equivalence)
    - Multiple elements → `.collection .hashSet [...]` (true parallel composition)

    **Why Pattern.set with Set Pattern DOES NOT work**:
    - All Pattern operations require computability (applySubst, freeVars, sizeOf)
    - `Set Pattern` is NOT computable (no decidable equality)
    - Would break substitution (needs List.map), induction (needs List.fold)

    Requires: h proves futures is finite (from spiceEval_finite theorem)
-/
noncomputable def futureSetAsPattern (futures : Set Pattern) (h : Set.Finite futures) : Pattern :=
  let list := finiteSetToList futures h
  match list with
  | [singleton] => singleton  -- Unwrap singletons: {p} = p (structural equivalence)
  | _ => .collection .hashSet list none  -- Keep multiple elements as collection

/-- Spice COMM substitution: substitute the future states of Q.

    Instead of substituting @Q, we substitute @{spiceEval(Q, n)} - the set of
    all states reachable from Q in ≤n steps.

    Takes a finiteness proof `h_fin` for the spiceEval set. For n=0, use
    `spiceEval_zero_finite`. For n>0, finiteness requires finite branching
    (standard in process calculus, not provable without quotienting by SC).
-/
noncomputable def spiceCommSubst (pBody : Pattern) (q : Pattern) (n : ℕ)
    (h_fin : (spiceEval q n).Finite) : Pattern :=
  let futurePattern := futureSetAsPattern (spiceEval q n) h_fin
  openBVar 0 (.apply "NQuote" [futurePattern]) pBody

/-! ## Spice COMM Reduction

The spice COMM rule with n-step lookahead.
-/

/-- Spice COMM reduction with horizon n.

    This extends the base COMM rule to substitute future states instead of
    just the current state.

    When n=0, this reduces to standard COMM (since spiceEval q 0 = {q}).
-/
inductive SpiceCommReduction (n : ℕ) : Pattern → Pattern → Prop where
  /-- Spice COMM: {n!(q) | for(x<-n){p} | ...rest} ⇝ {p[@{futures(q,n)}/x] | ...rest}

      The input body p receives the FUTURES of q (all states reachable in ≤n steps)
      instead of just q itself. Carries a finiteness proof for the future set.
  -/
  | spice_comm {channel q p : Pattern} {rest : List Pattern}
      (h_fin : (spiceEval q n).Finite) :
      SpiceCommReduction n
        (.collection .hashBag ([.apply "POutput" [channel, q],
                                .apply "PInput" [channel, .lambda p]] ++ rest) none)
        (.collection .hashBag ([spiceCommSubst p q n h_fin] ++ rest) none)

  /-- Structural: reduction under parallel composition (head position) -/
  | par {p q : Pattern} {rest : List Pattern} :
      SpiceCommReduction n p q →
      SpiceCommReduction n
        (.collection .hashBag (p :: rest) none)
        (.collection .hashBag (q :: rest) none)

  /-- Structural: reduction under parallel composition (any position) -/
  | par_any {p q : Pattern} {before after : List Pattern} :
      SpiceCommReduction n p q →
      SpiceCommReduction n
        (.collection .hashBag (before ++ [p] ++ after) none)
        (.collection .hashBag (before ++ [q] ++ after) none)

  /-- Structural: closure under structural congruence -/
  | equiv {p p' q q' : Pattern} :
      StructuralCongruence p p' →
      SpiceCommReduction n p' q' →
      StructuralCongruence q' q →
      SpiceCommReduction n p q

notation:20 p " ⇝ₛ[" n "] " q => SpiceCommReduction n p q

/-! ## Basic Properties -/

/-- finiteSetToList returns a singleton list for singleton sets.

    Proven using Set.Finite.toFinset_singleton and Finset.toList_singleton.
-/
theorem finiteSetToList_singleton (q : Pattern) (h : Set.Finite ({q} : Set Pattern)) :
    finiteSetToList {q} h = [q] := by
  unfold finiteSetToList
  -- Goal: (Set.Finite.toFinset h).toList = [q]
  rw [Set.Finite.toFinset_singleton]
  -- Now: {q}.toList = [q]  (where {q} is a Finset)
  exact Finset.toList_singleton q

/-- Singleton sets unwrap to their element.

    By the definition of futureSetAsPattern, singleton sets match the `[singleton]`
    case and return just the element.

    This is the key property that makes spice COMM with n=0 equal to standard COMM.
-/
theorem futureSetAsPattern_singleton (q : Pattern) (h : Set.Finite ({q} : Set Pattern)) :
    futureSetAsPattern {q} h = q := by
  unfold futureSetAsPattern
  rw [finiteSetToList_singleton q h]
  -- Now we have: match [q] with | [singleton] => singleton | _ => ...
  -- This matches the first case, returning q

/-- spiceCommSubst with n=0 equals commSubst.

    This captures the key property that 0-step lookahead recovers standard substitution.

    Proven using:
    1. `spiceEval q 0 = {q}` (spice_zero_is_current)
    2. `futureSetAsPattern {q} h = q` (futureSetAsPattern_singleton)
    3. Proof irrelevance (Subsingleton.elim) for finiteness proofs
-/
theorem spiceCommSubst_zero (p : Pattern) (q : Pattern)
    (h_fin : (spiceEval q 0).Finite) :
    spiceCommSubst p q 0 h_fin = commSubst p q := by
  unfold spiceCommSubst commSubst
  have h1 : spiceEval q 0 = {q} := spice_zero_is_current q
  simp only [h1]
  have h2 : futureSetAsPattern {q} (h1 ▸ h_fin) = q :=
    futureSetAsPattern_singleton q (h1 ▸ h_fin)
  simp only [h2]

/-- Spice COMM with n=0 is just standard COMM.

    When n=0, the spice rule substitutes the same value as standard COMM,
    so if spice COMM fires, standard COMM fires with the same result.

    **Proof**: Standard COMM rule + spiceCommSubst_zero lemma showing substitutions are equal.
-/
theorem spice_comm_zero_is_comm {channel q p : Pattern} {rest : List Pattern}
    (h_fin : (spiceEval q 0).Finite) :
    SpiceCommReduction 0
      (.collection .hashBag ([.apply "POutput" [channel, q],
                              .apply "PInput" [channel, .lambda p]] ++ rest) none)
      (.collection .hashBag ([spiceCommSubst p q 0 h_fin] ++ rest) none) →
    Nonempty (Reduces
      (.collection .hashBag ([.apply "POutput" [channel, q],
                              .apply "PInput" [channel, .lambda p]] ++ rest) none)
      (.collection .hashBag ([commSubst p q] ++ rest) none)) := by
  intro _
  exact ⟨Reduces.comm⟩

/- NOTE: spice_comm_mono was removed because the statement was unsound.
    Different horizons produce different substitution targets (singleton unwrapping
    at n=0 vs. collection at n>0), so monotonicity of the target is false.
    A correct variant would assert existence of SOME target, not the same target.
-/

/-! ## Compatibility with Base Reduction

The spice COMM rule should be compatible with the base reduction relation.
-/

/- NOTE: spice_comm_extends_reduces was removed because different horizons produce
    different results. For n=0, this IS true and proven as `spice_comm_zero_is_comm`.
-/

/-! ## Temporal Horizon and Agent Behavior

The horizon n determines how far an agent "looks ahead" before committing to
an interaction.
-/

/-- An agent with horizon 0 is reactive (no lookahead). -/
def ReactiveAgent (p : Pattern) : Prop :=
  ∀ q, (p ⇝ₛ[0] q) → Nonempty (p ⇝ q)

/-- An agent with horizon n>0 is precognitive (has lookahead). -/
def PrecognitiveAgent (p : Pattern) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ q, (p ⇝ₛ[n] q) → ∃ futures : Set Pattern, futures = spiceEval q n

/-- Reactive agents coincide with standard ρ-calculus agents.

    An agent with horizon 0 behaves exactly like a standard ρ-calculus agent.

    **Proof**: By induction on SpiceCommReduction structure:
    - Base case: spice_comm_zero_is_comm
    - Inductive case: PAR preserves the property
-/
theorem reactive_is_standard (p : Pattern) :
    ReactiveAgent p := by
  intro q hpq
  -- Induction on the spice reduction derivation with n=0
  induction hpq with
  | @spice_comm channel qpat pbody rest h_fin =>
    have h_eq : [spiceCommSubst pbody qpat 0 h_fin] = [commSubst pbody qpat] := by
      rw [spiceCommSubst_zero]
    rw [h_eq]
    exact ⟨Reduces.comm⟩
  | @par pinner qinner rest h_inner ih =>
    obtain ⟨h_std⟩ := ih
    exact ⟨Reduces.par h_std⟩
  | @par_any pinner qinner before after h_inner ih =>
    obtain ⟨h_std⟩ := ih
    exact ⟨Reduces.par_any h_std⟩
  | @equiv p' p'' q' q'' h_pre h_inner h_post ih =>
    obtain ⟨h_std⟩ := ih
    exact ⟨Reduces.equiv h_pre h_std h_post⟩

/-! ## Summary

This file establishes the spice COMM rule infrastructure:

**0 sorries, 0 axioms**:
1. **SpiceCommReduction n**: COMM with n-step lookahead — 4 constructors:
   - `spice_comm`: base COMM with future substitution
   - `par` / `par_any`: reduction in parallel (head / any position)
   - `equiv`: closure under structural congruence
2. **spiceCommSubst**: Substitution with future states (parameterized by finiteness)
3. **futureSetAsPattern**: Singleton unwrapping for n=0 recovery
4. **ReactiveAgent/PrecognitiveAgent**: Agent classifications
5. **spice_comm_zero_is_comm**: n=0 recovers standard COMM (proven)
6. **reactive_is_standard**: Reactive agents = standard (proven, handles all 4 constructors)

**Design**: `spiceCommSubst` takes `(h_fin : (spiceEval q n).Finite)` as parameter.
For n=0, `spiceEval_zero_finite` provides the proof (singleton {q}).
For n>0, finiteness requires finite branching up to structural congruence
(standard assumption in process calculus, not provable without SC quotient)
-/

end Mettapedia.OSLF.RhoCalculus.SpiceComm
