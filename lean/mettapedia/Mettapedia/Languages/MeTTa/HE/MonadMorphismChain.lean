import Mettapedia.Languages.MeTTa.HE.BagSupportBridge

/-!
# Monad Morphism Chain: List →ₘ Multiset →ₘ Finset

Proves that the projections `toBag` (List → Multiset) and `support`
(Multiset → Finset) are **monad morphisms**: they commute with `pure`
and `bind`. The composition `support ∘ toBag` is therefore also a
monad morphism, giving a single clean bridge from the computable evaluator
to the index level.

```
List ResultPair  ──toBag──▶  Multiset ResultPair  ──support──▶  Finset ResultPair
   (computable)                  (semantic)                        (index)
      Kl(List)          →ₘ        Kl(Multiset)          →ₘ        Kl(Finset)
```

## Key Results

- `toBag_monad_unit` / `toBag_monad_bind` — toBag is a monad morphism
- `support_monad_unit` / `support_monad_bind` — support is a monad morphism
- `toSupport` / `toSupport_bind` — the composed morphism List →ₘ Finset

## References

- Mathlib: `LawfulMonad Multiset`, `LawfulMonad Finset`
- NondeterminismCarrier.lean: `toBag_flatMap`
- BagSupportBridge.lean: `support_bind`, `support_toBag`
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: toBag is a monad morphism (List →ₘ Multiset) -/

/-- Unit law: `toBag (pure a) = pure a`. -/
theorem toBag_monad_unit (r : ResultPair) :
    ResultList.toBag [r] = ({r} : Multiset ResultPair) := rfl

/-- Bind law: `toBag (xs >>= f) = (toBag xs) >>= (toBag ∘ f)`.
    This is `toBag_flatMap` restated with monad notation. -/
theorem toBag_monad_bind (rs : ResultList) (f : ResultPair → ResultList) :
    ResultList.toBag (rs.flatMap f) =
    (ResultList.toBag rs).bind (fun r => ResultList.toBag (f r)) :=
  toBag_flatMap rs f

/-! ## §2: support is a monad morphism (Multiset →ₘ Finset) -/

/-- Unit law: `support (pure a) = {a}`. -/
@[simp]
theorem support_monad_unit {α : Type*} [DecidableEq α] (a : α) :
    support ({a} : Multiset α) = ({a} : Finset α) :=
  support_singleton a

/-- Bind law: `support (xs >>= f) = support(xs).biUnion (support ∘ f)`.
    This is `support_bind` from BagSupportBridge. -/
theorem support_monad_bind {α β : Type*} [DecidableEq α] [DecidableEq β]
    (bag : Multiset α) (f : α → Multiset β) :
    support (bag.bind f) = (support bag).biUnion (fun a => support (f a)) :=
  support_bind bag f

/-! ## §3: Composed morphism List →ₘ Finset -/

/-- The composed projection: List → Finset (= `List.toFinset`). -/
def toSupport (rs : ResultList) : Finset ResultPair := rs.toFinset

/-- The composed projection equals `support ∘ toBag`. -/
theorem toSupport_eq (rs : ResultList) :
    toSupport rs = support (ResultList.toBag rs) :=
  (support_toBag rs).symm

/-- Unit law for the composed morphism. -/
@[simp]
theorem toSupport_singleton (r : ResultPair) :
    toSupport [r] = {r} := by
  simp [toSupport]

/-- Bind law for the composed morphism:
    `(rs.flatMap f).toFinset = rs.toFinset.biUnion (fun r => (f r).toFinset)`

    This is THE theorem PathMap Claude needs: it says the Finset of
    flatMap results equals the biUnion of individual Finset results.
    PathMap trie queries should return this biUnion. -/
theorem toSupport_bind (rs : ResultList) (f : ResultPair → ResultList) :
    toSupport (rs.flatMap f) =
    (toSupport rs).biUnion (fun r => toSupport (f r)) := by
  show support (ResultList.toBag (rs.flatMap f)) =
       (support (ResultList.toBag rs)).biUnion (fun r => support (ResultList.toBag (f r)))
  rw [toBag_monad_bind, support_monad_bind]

/-! ## §4: Interpretation

### What this gives us

The monad morphism chain is the formal justification for the architecture:

1. **Evaluator** computes in `Kl(List)` — ordered, with duplicates, computable
2. **Spec** lives in `Kl(Multiset)` — unordered, with multiplicities
3. **Index** lives in `Kl(Finset)` — deduped, what PathMap stores

Each arrow is a monad morphism, so:
- Kleisli composition (sequential nondeterministic evaluation) commutes through
- What the evaluator computes, projected to any level, is correct

### The key property for PathMap

`toSupport_bind` says: the support of a flatMap = biUnion of supports.

For PathMap: if you store the support of each equation's RHS, then
answering a query = biUnion over matching equations' stored supports.
This is exactly what trie-based query answering does.
-/

end Mettapedia.Languages.MeTTa.HE
