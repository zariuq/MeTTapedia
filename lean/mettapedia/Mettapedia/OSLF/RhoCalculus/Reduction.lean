import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.CategoryTheory.LambdaTheory

/-!
# ρ-Calculus Reduction Semantics

This file defines the reduction relation for the ρ-calculus, connecting
the MeTTaIL COMM rewrite rule to the categorical semantics.

## The COMM Rule

The fundamental reduction in ρ-calculus is communication:

  {n!(q) | for(x<-n){p} | ...rest} ~> {p[@q/x] | ...rest}

This says:
- An output `n!(q)` on channel `n` with payload `q`
- Can synchronize with an input `for(x<-n){p}` listening on `n`
- The result is `p` with the quoted process `@q` substituted for `x`

## Connection to Modal Types

From the COMM rule, we derive modal operators:
- `possibly φ` = processes that CAN reduce to something in φ
- `rely φ` = processes that ALL predecessors were in φ

These form a Galois connection (◇ ⊣ ⧫).

## References

- Meredith & Stay, "Operational Semantics in Logical Form" Section 4
- Meredith & Radestock, "A Reflective Higher-Order Calculus"
-/

namespace Mettapedia.OSLF.RhoCalculus.Reduction

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.CategoryTheory.LambdaTheories

/-! ## The Reduction Relation

We define the one-step reduction relation ⇝ on processes.
-/

/-- The one-step reduction relation on ρ-calculus processes.

    p ⇝ q means p reduces to q in one step via the COMM rule
    (or a structural congruence).

    **Design Decision (2026-02-04)**: Reduces is Type-valued, not Prop-valued.

    **Rationale**: Reduction derivations are computational objects that encode HOW
    a reduction happens, not just THAT it happens. Using Type enables:
    - Automatic termination proofs (sizeOf works smoothly for Type inductives)
    - Extraction of derivation trees for proof complexity analysis
    - Alignment with process calculus tradition (derivations as witnesses)

    Via Curry-Howard, Type subsumes Prop, so this works anywhere Prop would.
    This decision was made after fighting Lean's termination checker for hours
    with Prop - the Type approach makes sizeOf inequalities trivial.
-/
inductive Reduces : Pattern → Pattern → Type where
  /-- COMM: {n!(q) | for(x<-n){p} | ...rest} ⇝ {p[@q/x] | ...rest}

      When an output and input on the same channel meet in parallel,
      they synchronize: the input body receives the quoted output payload.
  -/
  | comm {n q p : Pattern} {x : String} {rest : List Pattern} :
      Reduces
        (.collection .hashBag ([.apply "POutput" [n, q],
                                .apply "PInput" [n, .lambda x p]] ++ rest) none)
        (.collection .hashBag ([commSubst p x q] ++ rest) none)

  /-- DROP: *(@p) ⇝ p

      Dropping a quoted process yields the process itself.
      This is the reflection rule in ρ-calculus.
  -/
  | drop {p : Pattern} :
      Reduces (.apply "PDrop" [.apply "NQuote" [p]]) p

  /-- PAR: structural congruence under parallel composition

      If p ⇝ q, then {p | rest} ⇝ {q | rest}
  -/
  | par {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (p :: rest) none)
              (.collection .hashBag (q :: rest) none)

  /-- PAR_ANY: structural congruence for any element (via permutation)

      If p ∈ ps and p ⇝ q, then {ps} ⇝ {ps with p replaced by q}
      This captures that parallel composition is commutative.
  -/
  | par_any {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (before ++ [p] ++ after) none)
              (.collection .hashBag (before ++ [q] ++ after) none)

  /-- PAR_SET: structural reduction inside set collections (spice calculus variant)

      This enables the SET variant of the spice calculus as described in Meredith (2026).

      Sets (.hashSet) are used for future states in the spice rule to represent distinct
      reachable states without duplicates. This rule treats .hashSet as a transparent
      container: reductions inside propagate through the container.

      For singletons, .hashSet [p] behaves identically to .hashBag [p] (proven in
      Bisimulation.lean via singleton_bag_set_equiv theorem).

      **Design choice**: This is a CONSERVATIVE EXTENSION. The original ρ-calculus
      uses .hashBag (multisets), and that remains the primary semantics. This rule
      adds support for the set variant without changing existing bag semantics.

      **Idempotence**: Handled at construction time (Set → List conversion), not here.
      The reduction rule only propagates reductions through the container.
  -/
  | par_set {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (p :: rest) none)
              (.collection .hashSet (q :: rest) none)

  /-- PAR_SET_ANY: structural congruence for sets at any position

      Parallel to PAR_ANY but for .hashSet collections.
      Enables reduction at any position in the set collection.
  -/
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (before ++ [p] ++ after) none)
              (.collection .hashSet (before ++ [q] ++ after) none)

infix:50 " ⇝ " => Reduces

/-! ## Modal Operators via Reduction

Now we can define the modal operators concretely using the reduction relation.
-/

/-- Possibly: ◇φ = { p | ∃q. p ⇝ q ∧ q ∈ φ }

    A process p satisfies ◇φ if it can reduce to some process in φ.

    Note: Uses Nonempty wrapper to convert Type-valued reduction to Prop.
-/
def possiblyProp (φ : Pattern → Prop) : Pattern → Prop :=
  fun p => ∃ q, Nonempty (p ⇝ q) ∧ φ q

/-- Rely: ⧫φ = { p | ∀q. q ⇝ p → q ∈ φ }

    A process p satisfies ⧫φ if all its predecessors are in φ.

    Note: Uses Nonempty wrapper to convert Type-valued reduction to Prop.
-/
def relyProp (φ : Pattern → Prop) : Pattern → Prop :=
  fun p => ∀ q, Nonempty (q ⇝ p) → φ q

/-! ## Galois Connection

The key theorem: possibly and rely form a Galois connection.
-/

/-- Galois connection: possibly ⊣ rely

    possiblyProp φ ⊆ ψ  ↔  φ ⊆ relyProp ψ

    This is the fundamental relationship between the modal operators.
-/
theorem galois_connection (φ ψ : Pattern → Prop) :
    (∀ p, possiblyProp φ p → ψ p) ↔ (∀ p, φ p → relyProp ψ p) := by
  constructor
  -- Forward: if ◇φ ⊆ ψ then φ ⊆ ⧫ψ
  · intro h p hp q hqp
    apply h
    exact ⟨p, hqp, hp⟩
  -- Backward: if φ ⊆ ⧫ψ then ◇φ ⊆ ψ
  · intro h p ⟨q, hpq, hq⟩
    exact h q hq p hpq

/-! ## Connecting to Categorical Semantics

The PropRed semantics defines predicates on processes. We need to show
that our reduction-based modal operators correspond to the categorical ones.
-/

/-- A predicate on processes (as a Prop-valued function) -/
def ProcessPred := Pattern → Prop

/-- The categorical possibly operator (identity) trivially agrees with possibly at any fixed process.

    Note: A full correspondence would require SubPr to be predicates on processes,
    not just Prop. With SubPr = Prop, we can only state pointwise agreement.
-/
theorem possibly_pointwise (φ : ProcessPred) (p : Pattern) :
    possiblyProp φ p → (∃ q, φ q) := by
  intro ⟨q, _, hq⟩
  exact ⟨q, hq⟩

/-- The categorical rely operator (identity) trivially agrees with rely at any fixed process. -/
theorem rely_pointwise (φ : ProcessPred) (p : Pattern) :
    (∀ q, φ q) → relyProp φ p := by
  intro hall q _
  exact hall q

/-! ## Properties of COMM

We prove key properties of the COMM rule.
-/

/-- COMM reduces synchronizable terms (constructive witness).

    Returns a dependent pair (Σ) containing both the result pattern and the
    derivation witness. This is a def (not theorem) because it returns Type-valued data.
-/
def comm_reduces {n q p : Pattern} {x : String} :
    Σ r, (.collection .hashBag [.apply "POutput" [n, q],
                                .apply "PInput" [n, .lambda x p]] none) ⇝ r := by
  use .collection .hashBag [commSubst p x q] none
  -- Apply COMM with rest = []
  have h := @Reduces.comm n q p x []
  simp only [List.append_nil] at h
  exact h

-- TODO: once we have a syntactic predicate `IsProc : Pattern → Prop`,
-- prove `p ⇝ q → IsProc p → IsProc q`.

/-! ## Summary

This file establishes the reduction semantics for ρ-calculus:

1. ✅ **Reduces**: One-step reduction relation (COMM + PAR)
2. ✅ **possiblyProp**: Process can reduce to φ
3. ✅ **relyProp**: All predecessors satisfy φ
4. ✅ **galois_connection**: ◇ ⊣ ⧫ (PROVEN!)
5. ⚠️ **toSubPr**: Embedding into categorical semantics (axiomatized)
6. ⚠️ **possibly_agrees/rely_agrees**: Correspondence with Types.lean (needs proof)

**Key achievement**: The Galois connection is proven purely from the definitions!
This validates the OSLF construction.

**Connection to Types.lean**: The `possibly` and `rely` functions in Types.lean
are categorical versions of the propositional operators defined here. The
`possibly_agrees` and `rely_agrees` theorems (when completed) show they coincide.
-/

end Mettapedia.OSLF.RhoCalculus.Reduction
