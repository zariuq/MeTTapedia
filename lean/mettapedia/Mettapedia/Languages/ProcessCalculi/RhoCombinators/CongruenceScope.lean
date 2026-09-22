import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm

/-!
# What the congruence in this development is, and is not

The relation used throughout is the monoid laws for parallel composition,
closed under parallel composition and under equivalence.  It is **not** closed
under the atom constructors, and this file makes that boundary explicit rather
than leaving it to be discovered.

`cong_not_closed_under_atom_arguments` exhibits it: units cancel at the top of
a parallel soup, and the same cancellation inside an atom's argument is not
available.

## Why the development is arranged this way

Atom arguments are names, and the source presentation relates names by *name
equivalence*, not by structural congruence: two names are equivalent when the
processes they quote are congruent.  The reduction rules here consume that
relation exactly where the presentation does — at subject matching, through
the congruence hypothesis carried by every rule — rather than by closing the
congruence over argument positions.

## What this scopes, and what it does not

Results that use only rearrangement of a parallel soup are **robust to
enlarging the relation**, since they are proved with the smaller one:
the defect, the gate's release, the distributor's broadcast, the encoding
derivations, and the blindness engine all fall here.  The defect in particular
is proved with the smaller relation and therefore holds for any extension of
it.

The *invariance* results are different.  `cong_names` and `cong_components`
are theorems about the parallel-structural relation, and
`components_not_invariant_under_atom_closure` together with
`names_see_atom_argument_structure` show they would fail if the congruence
were closed over atom arguments: congruent terms would then have different
components and different name sets.

That is not a defect of the invariants but a statement about their right
formulation.  Closing the congruence over argument positions requires the
name set and the component multiset to be taken **up to name equivalence**,
not literally — so a faithful treatment of the full congruence carries a
mutually recursive pair, congruence on processes and equivalence on names,
with both invariants valued in equivalence classes.  That pair is not built
here, and no result in this development claims it.

`PresentUpTo` is already stated up to the congruence, so the separation
result is in the shape that survives the extension; the remaining work is the
invariants, not the statement.

## References

- L. G. Meredith and M. Radestock, *A reflective higher-order calculus*,
  ENTCS 141(5):49–67, 2005, for the congruence and name equivalence.
- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-- **The congruence is parallel-structural, not closed under atom
arguments.**  Units cancel at the top of a parallel soup, but the same
cancellation inside an atom's argument is not available: the relation is the
monoid laws closed under parallel composition, and no more. -/
theorem cong_not_closed_under_atom_arguments :
    Cong (par nil nil) nil ∧ ¬ Cong (kk (par nil nil)) (kk nil) := by
  refine ⟨Cong.parNil nil, ?_⟩
  intro h
  have comp := cong_components h
  simp only [components] at comp
  have members : kk (par nil nil) = kk nil := by
    simp at comp
  exact absurd members (by simp)

/-- Consequently the component invariant is a theorem about the
parallel-structural relation.  Extending the congruence to atom arguments
would relate terms with different components, so the invariant would have to
be restated with names taken up to equivalence rather than literally. -/
theorem components_not_invariant_under_atom_closure :
    components (kk (par nil nil)) ≠ components (kk nil) := by
  simp only [components]
  simp

/-- The same boundary in terms of names: an atom argument's parallel structure
is visible to the name set. -/
theorem names_see_atom_argument_structure :
    names (kk (par nil nil)) ≠ names (kk nil) := by
  intro h
  have mem : par nil nil ∈ names (kk (par nil nil)) := by simp [names]
  rw [h] at mem
  simp [names] at mem

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_not_closed_under_atom_arguments
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.components_not_invariant_under_atom_closure
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.names_see_atom_argument_structure
