import Mathlib.Order.CompleteBooleanAlgebra

/-!
# OSLF Framework: Rewrite Systems and Generated Type Systems

The OSLF (Operational Semantics in Logical Form) algorithm takes a rewrite system
as input and produces a spatial-behavioral type system as output.

## The OSLF Algorithm (Meredith & Stay)

**Input**: A rewrite system R = (sorts, terms, reduction relation)
**Output**: A type system where:
  - Types are (sort, predicate) pairs -- "native types"
  - Predicates form a Frame (complete Heyting algebra) at each sort
  - Modal operators diamond (step-future) and box (step-past) derived from reduction
  - diamond -| box form a Galois connection

## Key Structures

- `RewriteSystem`: The input -- sorts, terms, reduction
- `OSLFTypeSystem`: The output -- predicates, modal operators, Galois connection
- `NativeTypeOf`: A native type (sort, predicate) pair
- `Substitutability`: The key theorem: bisimilar processes have the same types

## References

- Meredith & Stay, "Operational Semantics in Logical Form" (oslf.pdf)
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Stay & Wells, "Generating Hypercubes of Type Systems"
-/

namespace Mettapedia.OSLF.Framework

/-! ## Rewrite Systems -/

/-- A rewrite system: the INPUT to the OSLF algorithm.

    Per OSLF paper section 3 (Def 1) + section 8.4:
    - `Sorts` classifies the different kinds of terms
    - `procSort` is the distinguished process sort (carrier of the reduction relation)
    - `Term S` gives the terms at each sort S
    - `Reduces` is the one-step reduction relation on process terms

    This is a simplified version of the full second-order signature from section 3,
    focusing on what's needed for the type system generation.

    Example: For the rho-calculus, Sorts = {Proc, Name}, procSort = Proc.
    Example: For the lambda-calculus, Sorts = {Term}, procSort = Term.
-/
structure RewriteSystem where
  /-- The sorts of the calculus -/
  Sorts : Type*
  /-- The distinguished process sort -/
  procSort : Sorts
  /-- Terms at each sort -/
  Term : Sorts → Type*
  /-- The reduction relation on process terms -/
  Reduces : Term procSort → Term procSort → Prop

/-! ## OSLF-Generated Type Systems -/

/-- The OSLF-generated type system: the OUTPUT of the OSLF algorithm.

    Per OSLF paper section 4 (NT construction) + section 6 (the algorithm):

    Given a rewrite system R, OSLF generates:
    1. A Frame of predicates at each sort (section 4: "Sub(Y(X)) is a cHa")
    2. A membership/satisfaction relation
    3. Modal operators diamond (step-future) and box (step-past) from reduction
    4. A proven Galois connection diamond -| box

    The Frame structure provides:
    - inf (meet/conjunction), sup (join/disjunction)
    - himp (Heyting implication)
    - sSup, sInf (arbitrary joins/meets)
    - top (full), bot (empty)
    - The quantale law: a inf (Sup S) = Sup (a inf . '' S)

    This structure captures the FULL output of the OSLF algorithm in a form
    that can be instantiated for any concrete calculus.
-/
structure OSLFTypeSystem (R : RewriteSystem) where
  /-- Predicates at each sort -/
  Pred : R.Sorts → Type*
  /-- Each predicate type forms a Frame (complete Heyting algebra).
      Per OSLF section 4: Sub(Y(X)) is a complete Heyting algebra. -/
  frame : ∀ S, Order.Frame (Pred S)
  /-- When a term satisfies a predicate -/
  satisfies : ∀ {S : R.Sorts}, R.Term S → Pred S → Prop
  /-- Step-future modal operator: diamond(phi) = { p | exists q. p reduces q and phi(q) }
      Per OSLF section 6 "Modal operators", STEP-FUTURE rule. -/
  diamond : Pred R.procSort → Pred R.procSort
  /-- diamond is characterized by its specification -/
  diamond_spec : ∀ (φ : Pred R.procSort) (p : R.Term R.procSort),
    satisfies p (diamond φ) ↔ ∃ q, R.Reduces p q ∧ satisfies q φ
  /-- Step-past modal operator: box(phi) = { p | forall q. q reduces p -> phi(q) }
      Per OSLF section 6 "Modal operators", STEP-PAST rule. -/
  box : Pred R.procSort → Pred R.procSort
  /-- box is characterized by its specification -/
  box_spec : ∀ (φ : Pred R.procSort) (p : R.Term R.procSort),
    satisfies p (box φ) ↔ ∀ q, R.Reduces q p → satisfies q φ
  /-- The OSLF Galois connection: diamond -| box.
      Per OSLF paper section 4 + section 6: the modal operators form an adjoint pair.

      Stated in terms of `satisfies` for maximum generality:
        (forall p, p in diamond(phi) -> p in psi) <-> (forall p, p in phi -> p in box(psi))

      When `satisfies` is function application and `le` is pointwise implication,
      this is equivalent to `GaloisConnection diamond box` from Mathlib. -/
  galois : ∀ (φ ψ : Pred R.procSort),
    (∀ p : R.Term R.procSort, satisfies p (diamond φ) → satisfies p ψ) ↔
    (∀ p : R.Term R.procSort, satisfies p φ → satisfies p (box ψ))

/-! ## Native Types -/

/-- A native type is a (sort, predicate) pair.

    Per OSLF section 4 + section 6.1: types are (U, X) where X is a sort and
    U is a predicate (filter) in the fiber over X.

    This captures "the set of terms of sort X satisfying predicate U".

    Example: (Proc, "can output on channel n") is a native type classifying
    processes that can send on channel n.
-/
structure NativeTypeOf {R : RewriteSystem} (ts : OSLFTypeSystem R) where
  /-- The sort -/
  sort : R.Sorts
  /-- The predicate at that sort -/
  pred : ts.Pred sort

/-! ## Substitutability -/

/-- The Substitutability property (OSLF Theorem 1, section 11):

    P bisim Q  <->  forall phi : Pred procSort, P in phi <-> Q in phi

    Two bisimilar processes satisfy exactly the same native types
    (predicates at the process sort).

    This is THE key soundness property of OSLF: behavioral equivalence
    coincides with logical equivalence (having the same types).

    The full OSLF statement quantifies over all native types (U, X).
    Since p, q are process terms, only procSort-sorted predicates apply directly.
    The general case (all sorts) follows when contexts are available.
-/
def Substitutability {R : RewriteSystem} (ts : OSLFTypeSystem R)
    (bisim : R.Term R.procSort → R.Term R.procSort → Prop) : Prop :=
  ∀ p q, bisim p q ↔
    ∀ (φ : ts.Pred R.procSort), ts.satisfies p φ ↔ ts.satisfies q φ

/-! ## Derived Properties -/

namespace OSLFTypeSystem

variable {R : RewriteSystem} (ts : OSLFTypeSystem R)

/-- Frame instance on each fiber -/
instance instFrame (S : R.Sorts) : Order.Frame (ts.Pred S) := ts.frame S

/-- diamond is monotone: if phi implies psi (w.r.t. satisfies),
    then diamond phi implies diamond psi. -/
theorem diamond_mono {φ ψ : ts.Pred R.procSort}
    (h : ∀ p, ts.satisfies p φ → ts.satisfies p ψ) :
    ∀ p, ts.satisfies p (ts.diamond φ) → ts.satisfies p (ts.diamond ψ) := by
  intro p hp
  rw [ts.diamond_spec] at hp ⊢
  obtain ⟨q, hred, hq⟩ := hp
  exact ⟨q, hred, h q hq⟩

/-- box is monotone: if phi implies psi (w.r.t. satisfies),
    then box phi implies box psi. -/
theorem box_mono {φ ψ : ts.Pred R.procSort}
    (h : ∀ p, ts.satisfies p φ → ts.satisfies p ψ) :
    ∀ p, ts.satisfies p (ts.box φ) → ts.satisfies p (ts.box ψ) := by
  intro p hp
  rw [ts.box_spec] at hp ⊢
  intro q hred
  exact h q (hp q hred)

/-- Forward direction of Galois: diamond phi subset psi implies phi subset box psi. -/
theorem galois_forward {φ ψ : ts.Pred R.procSort}
    (h : ∀ p, ts.satisfies p (ts.diamond φ) → ts.satisfies p ψ) :
    ∀ p, ts.satisfies p φ → ts.satisfies p (ts.box ψ) :=
  (ts.galois φ ψ).mp h

/-- Backward direction of Galois: phi subset box psi implies diamond phi subset psi. -/
theorem galois_backward {φ ψ : ts.Pred R.procSort}
    (h : ∀ p, ts.satisfies p φ → ts.satisfies p (ts.box ψ)) :
    ∀ p, ts.satisfies p (ts.diamond φ) → ts.satisfies p ψ :=
  (ts.galois φ ψ).mpr h

end OSLFTypeSystem

end Mettapedia.OSLF.Framework
