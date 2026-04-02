import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Functor
import Mettapedia.Languages.MeTTa.HE.Types

/-!
# Nondeterminism Carrier for MeTTa Evaluation

MeTTa's evaluation is nondeterministic: each expression can produce multiple
results. The HE spec (EvalSpec.lean) models this as multiple valid derivation
trees. The evaluator (Eval.lean) materializes this as `List ResultPair`.

But the spec says "the relation is order-free by construction" (EvalSpec.lean:24).
`List` imposes ordering. The compensating hack is `ResultEqBag` (Types.lean:261):
a separate permutation equivalence.

The correct fix: use `Multiset` as the semantic result type. Then:
- `ResultEqBag` becomes definitional equality (`=`)
- Order-sensitivity bugs are impossible by construction
- The monad laws transfer via `Multiset.coe_bind`

## Key Results

- `ResultBag` — `Multiset ResultPair`, the semantically correct result type
- `ResultList.toBag` — canonical projection from computable to semantic
- `toBag_perm_iff` — the payoff: `Perm ↔ (= on Multiset)`
- `toBag_flatMap` — `List.flatMap` commutes with `toBag` (bridge theorem)

## References

- Corsini & Leoreanu (2003): hyperoperations produce sets/multisets
- Fujita (2025): n-superhyperstructures via iterated powerset
- Mathlib: `LawfulMonad Multiset` (Data.Multiset.Functor)
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: The semantically correct result type -/

/-- `ResultBag` is `Multiset ResultPair` — the semantically correct result type
    for MeTTa evaluation. Unordered, preserves multiplicity.

    The evaluator uses `List ResultPair` (= `ResultSet`) for computability.
    `ResultBag` is the spec-level type where bag equivalence is `=`. -/
abbrev ResultBag := Multiset ResultPair

/-- Alias for clarity: the computable result type (= `ResultSet = List ResultPair`). -/
abbrev ResultList := List ResultPair

/-! ## §2: The canonical projection -/

/-- Project a computable result list to its semantic bag.
    This is `List → Multiset` coercion (Quotient.mk). -/
def ResultList.toBag (rs : ResultList) : ResultBag := (rs : Multiset ResultPair)

/-- **The payoff theorem**: two result lists are permutations iff their bags are equal.

    This makes `ResultEqBag` (Types.lean:261) redundant. Instead of:
    ```
    def ResultEqBag (r1 r2 : ResultSet) : Prop := r1.Perm r2
    ```
    we have: `r1.toBag = r2.toBag`. Same content, but `=` instead of a custom relation. -/
theorem toBag_perm_iff (r1 r2 : ResultList) :
    r1.Perm r2 ↔ r1.toBag = r2.toBag := by
  exact Multiset.coe_eq_coe.symm

/-- Empty result list projects to empty bag. -/
@[simp]
theorem toBag_nil : ResultList.toBag [] = (0 : ResultBag) := rfl

/-- Singleton result list projects to singleton bag. -/
@[simp]
theorem toBag_singleton (r : ResultPair) :
    ResultList.toBag [r] = {r} := rfl

/-- Append projects to multiset addition. -/
@[simp]
theorem toBag_append (r1 r2 : ResultList) :
    ResultList.toBag (r1 ++ r2) = r1.toBag + r2.toBag := by
  simp [ResultList.toBag, Multiset.coe_add]

/-! ## §3: The bridge theorem — flatMap commutes with toBag -/

/-- **Bridge theorem**: `List.flatMap` projected to `Multiset` equals `Multiset.bind`.

    This is the key correctness property: the computable evaluator (using `flatMap`)
    produces results that, when projected to the semantic level, equal what a
    hypothetical `Multiset`-based evaluator would produce.

    In other words: the `List` evaluator is correct up to ordering. -/
theorem toBag_flatMap (rs : ResultList) (f : ResultPair → ResultList) :
    ResultList.toBag (rs.flatMap f) =
    rs.toBag.bind (fun r => ResultList.toBag (f r)) := by
  exact (Multiset.coe_bind rs f).symm

/-- `filter` commutes with `toBag`. -/
theorem toBag_filter (rs : ResultList) (p : ResultPair → Bool) :
    ResultList.toBag (rs.filter p) =
    Multiset.filter (fun r => p r = true) rs.toBag := by
  simp [ResultList.toBag, Multiset.filter_coe]

/-- `map` commutes with `toBag`. -/
theorem toBag_map (rs : ResultList) (f : ResultPair → ResultPair) :
    ResultList.toBag (rs.map f) =
    Multiset.map f rs.toBag := by
  simp [ResultList.toBag]

/-! ## §4: Monad law transfer

The key structural property: because `Multiset` is a `LawfulMonad` (Mathlib),
and `toBag` commutes with `bind`/`flatMap` (§3), the monad laws transfer
from `Multiset` to the evaluator's `List.flatMap` chains modulo `toBag`.

Concretely, for any result lists `rs` and functions `f`, `g`:
```
toBag ((rs.flatMap f).flatMap g) = toBag (rs.flatMap (fun r => (f r).flatMap g))
```

This is `bind_assoc` for `List`, projected through `toBag`. It's why
MeTTa's sequential nondeterministic evaluation composes correctly
regardless of result ordering. -/

/-- Bind associativity transfers through toBag. -/
theorem toBag_flatMap_assoc (rs : ResultList)
    (f : ResultPair → ResultList) (g : ResultPair → ResultList) :
    ResultList.toBag ((rs.flatMap f).flatMap g) =
    ResultList.toBag (rs.flatMap (fun r => (f r).flatMap g)) := by
  rw [toBag_flatMap, toBag_flatMap]
  rw [toBag_flatMap]
  -- Now it's Multiset.bind associativity
  simp only [Multiset.bind_assoc]
  congr 1
  funext r
  exact (toBag_flatMap (f r) g).symm

/-! ## §5: Interpretation

### What this gives us

1. **`ResultEqBag` is now `=`**: Instead of a separate equivalence relation,
   we have `r1.toBag = r2.toBag`. This is definitional equality on `Multiset`.

2. **Order-sensitivity is type-impossible**: Any property proved about `ResultBag`
   is automatically permutation-invariant. No need to check.

3. **Monad laws are free**: `LawfulMonad Multiset` in Mathlib gives us
   `bind_assoc`, `pure_bind`, `bind_pure` for free. Through `toBag`, these
   transfer to the computable evaluator.

### Connection to Hyperstructure.lean

The `Hyperstructure.lean` formalization proved that the powerset monad's
Kleisli composition is associative (`kleisliAssoc`). Here we instantiate:
- `Set` carrier → `LawfulMonad Set` (Mathlib.Data.Set.Functor)
- `Multiset` carrier → `Multiset.bind_assoc` (Mathlib, LawfulMonad)
- `List` carrier → `List.flatMap` associativity (Mathlib)

All three satisfy the same monad laws. The evaluator uses `List` for computation,
projects to `Multiset` for semantic correctness, and the `Set` version gives the
hyperstructure connection to Fujita/Smarandache.

### Connection to CeTTa

CeTTa's `Space` with `SPACE_KIND_ATOM` stores atoms as `Atom **atoms` (a C array).
Semantically, this is a multiset: `add-atom` adds with possible duplicates,
`match` is symmetric (order doesn't affect results), and `add-atom-nodup`
is the explicit downgrade to set semantics.

The Space revision counter (planned in the CeTTa tabling tranche) is a
multiset-mutation counter: it bumps on every `space_add` / `space_remove`.
-/

end Mettapedia.Languages.MeTTa.HE
