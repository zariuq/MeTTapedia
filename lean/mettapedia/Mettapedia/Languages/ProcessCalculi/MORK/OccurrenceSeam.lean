import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# The list-versus-set seam of MM2 spaces

A MORK space is a set.  The computable conformance layer models it as a list.
`Conformance.lean` proves the two agree on `remove` sinks under a `Nodup`
hypothesis and explains why: `List.erase` removes one occurrence, `Finset.erase`
removes the element.  This module pins the seam as a theorem rather than a
comment: without `Nodup`, the two carriers genuinely disagree.  It is the
smallest concrete instance of the bag-versus-set face distinction in the
computational trinity, at the exact point where MM2 execution lives.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.OccurrenceSeam

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A fixed ground atom. -/
def a : Atom := .symbol "a"

theorem applySubst_a (σ : Subst) : applySubst σ a = a := by
  rfl

/-- The duplicated occurrence list is not `Nodup`, so the conformance lemma's
hypothesis fails for it. -/
theorem duplicate_not_nodup : ¬ ([a, a] : List Atom).Nodup := by
  simp

/-- On the list carrier, removing `a` from `[a, a]` leaves one occurrence. -/
theorem list_remove_keeps_one_occurrence (σ : Subst) :
    (([a, a] : List Atom).erase (applySubst σ a)).toFinset = {a} := by
  rw [applySubst_a]
  simp

/-- On the set carrier, removing `a` from the same space leaves nothing. -/
theorem set_remove_keeps_nothing (σ : Subst) :
    applySink (([a, a] : List Atom).toFinset) σ (.remove a) = ∅ := by
  simp [applySink, applySubst_a]

/-- The seam: the two carriers disagree exactly where multiplicity matters. -/
theorem remove_sink_disagrees_without_nodup (σ : Subst) :
    (([a, a] : List Atom).erase (applySubst σ a)).toFinset ≠
      applySink (([a, a] : List Atom).toFinset) σ (.remove a) := by
  rw [list_remove_keeps_one_occurrence, set_remove_keeps_nothing]
  exact Finset.singleton_ne_empty a

#print axioms remove_sink_disagrees_without_nodup

end Mettapedia.Languages.ProcessCalculi.MORK.OccurrenceSeam
