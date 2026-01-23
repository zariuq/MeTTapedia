import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.KSSeparationNotDerivable
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation

/-!
# Noncommutative models for `KnuthSkillingAlgebra`

This file explores whether the `KnuthSkillingAlgebra` axioms are already strong enough to
force commutativity, by attempting to build a noncommutative model.

## Status: RESOLVED (2026-01-08)

**Key results:**
- There are easy noncommutative models of `KnuthSkillingAlgebra` (see `KSSeparationNotDerivable.lean`).
- Every noncommutative model **must** fail `KSSeparation`.
- This is because `KSSeparation → Commutativity` is **proven** in `SandwichSeparation.lean`.

## The (Former) Open Problem

> Does there exist a noncommutative `KnuthSkillingAlgebra` that *does* satisfy `KSSeparation`?

**Answer: NO.** This is now proven impossible via contrapositive:
- `ksSeparation_implies_commutative` proves `KSSeparation → Commutativity`
- Therefore `¬Commutativity → ¬KSSeparation`

This validates K&S's claim that "commutativity is imposed by the associativity and order
required of a scalar representation" — because scalar representation implies `KSSeparation`,
which in turn forces commutativity.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations

open KnuthSkillingAlgebra
open KnuthSkillingAlgebraBase (op ident)
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

/-- A "true" countermodel to the Appendix-A commutativity theorem would be a noncommutative
`KnuthSkillingAlgebra` that also satisfies `KSSeparation`.

**This is now proven to be impossible** — see `noncommutativeKSSeparationCountermodel_false`. -/
def NoncommutativeKSSeparationCountermodel : Prop :=
  ∃ (α : Type),
    ∃ (_ : KnuthSkillingAlgebra α),
      ∃ (_ : KSSeparation α),
        ∃ x y : α, op x y ≠ op y x

/-- No noncommutative `KnuthSkillingAlgebra` can satisfy `KSSeparation`.

This is the contrapositive of `ksSeparation_implies_commutative`:
- `KSSeparation → Commutativity` (proven in `SandwichSeparation.lean`)
- Therefore `¬Commutativity → ¬KSSeparation`

This resolves the former "open problem" and validates K&S's claim that commutativity
is forced by the properties required for scalar representation. -/
theorem noncommutativeKSSeparationCountermodel_false : ¬ NoncommutativeKSSeparationCountermodel := by
  intro ⟨α, _, inst_sep, x, y, h_neq⟩
  exact h_neq (SandwichSeparation.ksSeparation_implies_commutative x y)

/-- If a `KnuthSkillingAlgebra` is non-commutative, it cannot satisfy `KSSeparation`.

This is the key consequence: non-commutativity implies failure of separation. -/
theorem noncommutative_implies_not_ksSeparation
    {α : Type*} [KnuthSkillingAlgebra α]
    (h_noncomm : ∃ x y : α, op x y ≠ op y x) :
    ¬ KSSeparation α := by
  intro inst_sep
  obtain ⟨x, y, h_neq⟩ := h_noncomm
  exact h_neq (@SandwichSeparation.ksSeparation_implies_commutative α _ inst_sep x y)

/-- There exists a noncommutative `KnuthSkillingAlgebra` (so commutativity is not automatic). -/
theorem exists_noncommutative_knuthskilling :
    ∃ (α : Type), ∃ (_ : KnuthSkillingAlgebra α), ∃ x y : α, op x y ≠ op y x :=
  exists_knuthskilling_noncomm

/-- There exists a `KnuthSkillingAlgebra` that does **not** satisfy `KSSeparation`. -/
theorem exists_knuthskilling_not_separation' :
    ∃ (α : Type), ∃ (_ : KnuthSkillingAlgebra α), ¬ KSSeparation α :=
  exists_knuthskilling_not_separation

/-!
## Historical Note: Obstruction Methods

Before `ksSeparation_implies_commutative` was proven, we used obstruction methods to rule out
specific noncommutative countermodel attempts (e.g., rank obstructions that showed models with
monotone additive "rank" functions and nontrivial fibers must fail `KSSeparation`).

This ruled out a wide class of noncommutative constructions (free monoids, semidirect/lex products,
affine-composition-style models, …).

**These methods are now superseded** by the direct proof `ksSeparation_implies_commutative`,
which shows that *all* noncommutative models must fail `KSSeparation`, not just those with
obvious "size" coordinates.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Experimental.RepresentationTheorem.Explorations
