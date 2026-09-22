/-
# A soup presentation needs a binary composition

`SoupPresentation.lean` proves the soup theorem for any carrier that
*decomposes*: whose terms are congruent to the parallel composition of their own
components. The abstraction was built with one instance, the rho combinators,
and a second was identified as the natural next one — the rho calculus itself,
whose structural congruence is component-bag equality by a theorem already in the
tree.

That second instance is **not available**, and this file says why rather than
leaving it as a remaining task with an estimate.

## The obstruction

`Soup`'s composition is **binary**, and `decomposes` asks that a term be
congruent to the *right-nested* composition of its components. Rho's parallel
composition is not binary: it is a collection, so a three-element parallel
process is one flat former applied to three arguments, not two nested
applications.

The generic congruence has only the monoid laws on `comp` and closure under
`comp`. None of them reaches inside a former that is not `comp`. So a flat
`n`-ary composition cannot be related to the binary nesting of its components,
and `decomposes` is unsatisfiable for such a carrier.

`tripleCount_cong` is the invariant that proves it: the number of flat `n`-ary
nodes is preserved by the generic congruence, because every one of its rules is
about `comp` and `unit`. A flat triple has one; the binary nesting of three atoms
has none.

`no_soup_with_flat_composition` is the conclusion, and it is stated for **any**
decomposition whose components are atoms — which is what any sensible
decomposition of a flat composition gives.

## The same cause as the census failure

This is not a new obstruction. It is `PPar`'s bag-valued parameter, which
`collection_parameter_not_assemblable` already proved is not positionally
assemblable and which is why rho fails the §3 admissibility census. One cause,
two manifestations: a variadic composition has no fixed arity, so it neither
admits a name-free target nor forms a soup.

So the consolidation the abstraction was built for is available for a **binary**
presentation of parallel composition — which is what the combinator calculus is,
and what `combSoup` instantiates — and not for the authored rho presentation.
That is a statement about the presentation, not about rho.
-/
import Mettapedia.GSLT.Logic.SoupPresentation

set_option autoImplicit false

namespace Mettapedia.GSLT.SoupPresentation

/-! ## A carrier with a flat composition -/

/-- A minimal carrier with both a binary composition and a flat ternary one:
the shape a collection-valued parallel composition has. -/
inductive Flat where
  | atom : ℕ → Flat
  | empty : Flat
  | pair : Flat → Flat → Flat
  | triple : Flat → Flat → Flat → Flat

namespace Flat

/-- How many flat ternary nodes a term has. -/
def tripleCount : Flat → ℕ
  | atom _ => 0
  | empty => 0
  | pair p q => tripleCount p + tripleCount q
  | triple a b c => tripleCount a + tripleCount b + tripleCount c + 1

/-- **The generic congruence cannot change the number of flat nodes.**  Every one
of its rules is about the binary composition and its unit, so none of them
reaches inside a former that is not that composition. -/
theorem tripleCount_cong {p q : Flat} (h : Cong Flat.empty Flat.pair p q) :
    tripleCount p = tripleCount q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compUnit p => simp [tripleCount]
  | compComm p q => simp only [tripleCount]; omega
  | compAssoc p q r => simp only [tripleCount]; omega
  | compLeft q _ ih => simp only [tripleCount, ih]
  | compRight p _ ih => simp only [tripleCount, ih]

/-- Recomposing a list of flat-free terms is flat-free. -/
theorem tripleCount_ofList :
    ∀ l : List Flat, (∀ x ∈ l, tripleCount x = 0) →
      tripleCount (ofList Flat.empty Flat.pair l) = 0
  | [], _ => rfl
  | head :: rest, h => by
      have ih := tripleCount_ofList rest (fun x hx => h x (List.Mem.tail _ hx))
      simp only [ofList, tripleCount, ih, h head (List.Mem.head _)]

/-- **No decomposition makes a flat composition a soup.**  Whatever components a
flat ternary node is given, if they are ordinary terms then the binary nesting of
them has no flat node and the node itself has one, so they are not congruent and
`decomposes` cannot hold. -/
theorem no_soup_with_flat_composition (componentList : Flat → List Flat)
    (components_are_flat_free :
      ∀ x ∈ componentList (Flat.triple (atom 0) (atom 1) (atom 2)),
        tripleCount x = 0)
    (decomposes : Cong Flat.empty Flat.pair
      (Flat.triple (atom 0) (atom 1) (atom 2))
      (ofList Flat.empty Flat.pair
        (componentList (Flat.triple (atom 0) (atom 1) (atom 2))))) : False := by
  have invariant := tripleCount_cong decomposes
  rw [tripleCount_ofList _ components_are_flat_free] at invariant
  simp [tripleCount] at invariant

/-- The positive companion: a binary composition of flat-free terms *is*
congruent to the recomposition of its components, so binarity is what the
abstraction needs and the obstruction is variadicity alone. -/
theorem pair_decomposes (left right : Flat) :
    Cong Flat.empty Flat.pair (Flat.pair left right)
      (ofList Flat.empty Flat.pair [left, right]) := by
  refine Cong.trans (Cong.compRight left (Cong.symm (Cong.compUnit right))) ?_
  exact Cong.refl _

end Flat

end Mettapedia.GSLT.SoupPresentation
