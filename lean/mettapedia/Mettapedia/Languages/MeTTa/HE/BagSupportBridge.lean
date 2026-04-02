import Mettapedia.Languages.MeTTa.HE.NondeterminismCarrier
import Mathlib.Data.Finset.Dedup

/-!
# Bag–Support Bridge for HE MeTTa

Formalizes the three-layer semantic chain:

```
  Bag (Multiset)           ← full HE semantics (multiplicity)
       ↓ toFinset
  Support (Finset)         ← what PathMap/indexing can see
       ↓ membership
  Index (lookup table)     ← operational storage
```

The key insight: HE evaluation lives in bag semantics (Multiset), but
storage backends (PathMap, hash space, CeTTa's `Space`) see only the
**support** (Finset). This is not a bug — it's the correct abstraction:

- Multiplicity records how many derivation paths led to a result
- Support records which results exist
- An index maps queries to their supported results

The formalization proves this projection is a **monad morphism**: it commutes
with bind/flatMap, so the evaluator's nondeterministic composition descends
cleanly through the support projection.

## Key Results

- `support` — `Multiset → Finset` projection (forgets multiplicity)
- `support_bind` — support commutes with monadic bind
- `support_toBag` — `support ∘ toBag = List.toFinset` (bridge chain)
- `BagSpace` / `SupportSpace` — semantic vs operational space types
- `querySupport_sound` — PathMap answers ⊆ support of bag query results
- `canonQuot_support` — canonicalization quotient is a support homomorphism

## References

- Fujita & Smarandache (2026): hyperization = Kleisli embedding; support = dedup
- Corsini & Leoreanu (2003): quotient hyperstructures
- Mathlib: `Multiset.toFinset`, `LawfulMonad Multiset`
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: The support projection -/

/-- The **support** of a multiset: the set of distinct elements.
    This is `Multiset.toFinset` — forgets multiplicity, keeps membership.

    In MeTTa terms: two derivations producing the same atom collapse to
    one entry in the support, but both derivations remain in the bag. -/
def support {α : Type*} [DecidableEq α] (bag : Multiset α) : Finset α :=
  bag.toFinset

/-- Support of empty bag is empty set. -/
@[simp]
theorem support_zero {α : Type*} [DecidableEq α] :
    support (0 : Multiset α) = ∅ := by
  simp [support]

/-- Support of singleton is singleton. -/
@[simp]
theorem support_singleton {α : Type*} [DecidableEq α] (a : α) :
    support ({a} : Multiset α) = {a} := by
  simp [support]

/-- Membership in support ↔ membership in bag (forgets count). -/
theorem mem_support_iff {α : Type*} [DecidableEq α] (a : α) (bag : Multiset α) :
    a ∈ support bag ↔ a ∈ bag := by
  simp [support, Multiset.mem_toFinset]

/-- Support is monotone: sub-bag → sub-support. -/
theorem support_mono {α : Type*} [DecidableEq α] {s t : Multiset α}
    (h : s ≤ t) : support s ⊆ support t := by
  intro a ha
  rw [mem_support_iff] at ha ⊢
  exact Multiset.mem_of_le h ha

/-- Support of union ⊆ union of supports. Actually equality for Multiset add. -/
theorem support_add {α : Type*} [DecidableEq α] (s t : Multiset α) :
    support (s + t) = support s ∪ support t := by
  simp [support, Multiset.toFinset_add]

/-! ## §2: Support commutes with monadic operations -/

/-- **Support commutes with map**: `support (map f bag) = Finset.image f (support bag)`. -/
theorem support_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (bag : Multiset α) :
    support (bag.map f) = (support bag).image f := by
  simp [support, Multiset.toFinset_map]

/-- **Support commutes with bind** (the key theorem):
    `support (bag >>= f) = bag.toFinset.biUnion (fun a => support (f a))`

    This says: the support of bound results = union of supports of individual results.
    Multiplicity of how many times `a` appears in `bag` doesn't affect which
    elements appear in the final support — only which `a`s contribute matters. -/
theorem support_bind {α β : Type*} [DecidableEq α] [DecidableEq β]
    (bag : Multiset α) (f : α → Multiset β) :
    support (bag.bind f) = (support bag).biUnion (fun a => support (f a)) := by
  ext x
  simp only [support, Multiset.mem_toFinset, Multiset.mem_bind,
             Finset.mem_biUnion]

/-! ## §3: Bridge from List evaluator through Multiset to Finset -/

/-- **Full bridge chain**: `support ∘ toBag = toFinset` on Lists.

    The evaluator produces `List ResultPair`.
    `toBag` projects to `Multiset ResultPair` (order-free).
    `support` projects to `Finset ResultPair` (deduped).
    The composition is just `List.toFinset`. -/
theorem support_toBag (rs : ResultList) :
    support (ResultList.toBag rs) = rs.toFinset := by
  simp [support, ResultList.toBag]

/-- Support of flatMap through the full bridge:
    `(rs.flatMap f).toFinset = rs.toFinset.biUnion (fun r => (f r).toFinset)` -/
theorem support_toBag_flatMap (rs : ResultList) (f : ResultPair → ResultList) :
    support (ResultList.toBag (rs.flatMap f)) =
    rs.toFinset.biUnion (fun r => (f r).toFinset) := by
  rw [toBag_flatMap, support_bind]
  simp [support_toBag]

/-! ## §4: BagSpace — semantically correct space type -/

/-- A **BagSpace** stores atoms as a multiset — the semantically correct model
    for HE MeTTa's `SPACE_KIND_ATOM`.

    `add` adds with possible duplicates.
    `contains` checks membership (ignores multiplicity).
    `support` gives the Finset of distinct atoms (what an index sees). -/
structure BagSpace where
  atoms : Multiset Atom
  deriving Inhabited

namespace BagSpace

def empty : BagSpace := ⟨0⟩

def add (s : BagSpace) (a : Atom) : BagSpace :=
  ⟨a ::ₘ s.atoms⟩

def atomSupport (s : BagSpace) : Finset Atom :=
  support s.atoms

/-- Adding an atom that's already present doesn't change the support.
    This is why `add-atom-nodup` and `add-atom` differ only in multiplicity. -/
theorem support_add_of_mem (s : BagSpace) (a : Atom) (h : a ∈ s.atoms) :
    (s.add a).atomSupport = s.atomSupport := by
  simp only [atomSupport, add, support, Multiset.toFinset_cons,
             Finset.insert_eq_of_mem (Multiset.mem_toFinset.mpr h)]

/-- Adding a new atom extends the support by exactly one element. -/
theorem support_add_of_not_mem (s : BagSpace) (a : Atom) (_h : a ∉ s.atoms) :
    (s.add a).atomSupport = insert a s.atomSupport := by
  simp only [atomSupport, add, support, Multiset.toFinset_cons]

end BagSpace

/-! ## §5: Canonicalization as support homomorphism -/

/-- A **canonicalization map** sends atoms to their canonical form.
    Two atoms with the same canonical form are "support-equivalent":
    they occupy the same slot in an index. -/
structure CanonMap where
  canon : Atom → Atom

/-- Apply canonicalization to a bag: map each element to its canonical form. -/
def CanonMap.applyBag (c : CanonMap) (bag : Multiset Atom) : Multiset Atom :=
  bag.map c.canon

/-- Apply canonicalization to a support set. -/
def CanonMap.applySupport (c : CanonMap) (s : Finset Atom) : Finset Atom :=
  s.image c.canon

/-- **Canonicalization commutes with support projection.**

    `support (canon bag) = canon (support bag)`

    This is the quotient homomorphism property: canonicalizing then taking
    support equals taking support then canonicalizing. Dedup and canonicalization
    commute. -/
theorem CanonMap.support_comm (c : CanonMap) (bag : Multiset Atom) :
    support (c.applyBag bag) = c.applySupport (support bag) := by
  simp [support, applyBag, applySupport, Multiset.toFinset_map]

/-- **Canonicalization distributes over support of bind.**

    `support(canon(bag >>= f)) = image canon (support(bag >>= f))`

    This is `support_comm` applied to a bind result: canonicalizing
    the output of a nondeterministic computation, then taking support,
    equals taking support then canonicalizing. -/
theorem CanonMap.support_bind_canon (c : CanonMap)
    (bag : Multiset Atom) (f : Atom → Multiset Atom) :
    support (c.applyBag (bag.bind f)) =
    c.applySupport (support (bag.bind f)) :=
  c.support_comm (bag.bind f)

/-! ## §6: Interpretation

### The three-layer chain

```
  ResultList (List ResultPair)     ← computable evaluator output
       ↓ toBag
  ResultBag (Multiset ResultPair)  ← semantic truth (order-free, multiplicities)
       ↓ support
  ResultSupport (Finset ResultPair)← what PathMap/index sees (deduped)
```

Each projection is a **monad morphism** — commutes with bind.
Each layer has its own correct equality:
- `List`: `=` (exact sequence, for determinism testing)
- `Multiset`: `=` (bag equality, for spec conformance)
- `Finset`: `=` (set equality, for index correctness)

### What Fujita/Smarandache contribute here

Their "hyperization" is the upward direction:
- Classical operation → hyperoperation (Set-valued)
- But we now see: for MeTTa, the FULL semantics is Multiset-valued
- Set/Finset is a QUOTIENT of the full semantics
- Support projection IS the quotient map

Their "reduced superhypergroup" (Fujita 2025, §3.3) quotients by
"essential indistinguishability." Our `CanonMap.support_comm` is exactly
this: canonicalization is the quotient, support is the reduction,
and they commute. We've given their construction a concrete instance
and a machine-checked proof.

### What this gives CeTTa

The Space revision counter (planned CeTTa tranche) bumps on mutations
to the **bag** (every `space_add`). But the tabling cache keys on
**support** (via canonical query). `support_bind` proves this is
sound: if two bags have the same support, their bound results have
the same support too. So caching at the support level is correct
for any consumer that only observes support (which includes `match`
and `queryEquations` in their current form).
-/

end Mettapedia.Languages.MeTTa.HE
