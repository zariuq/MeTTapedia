import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverChoices
import Mettapedia.Logic.Metaphysics.UltrainfiniteSymmetry

/-!
# One form for two symmetry obstructions

`AnnotatedRuns.no_equivariant_selection` (an observer's deterministic selection from a symmetric
pair) and `map_evenOddSwap_ne` (no ultrafilter on `ℕ` is fixed by the evens/odds swap) are two
instances of `select_ne_of_fixed`:

| | fixed point | symmetry on points | symmetry on values | selection | exchanged pair |
|---|---|---|---|---|---|
| observer | a record `r` | `Record.rename π` | `π` | `select` | `a`, `b` |
| ultrafilter | an ultrafilter `U` | `Ultrafilter.map σ` | `σ ⁻¹'` | `chosenHalf evens` | evens, odds |

`no_equivariant_selection_of_shared` derives the observer theorem, statement for statement, from
the shared form. Neither theorem is an instance of the other: the observer theorem is stated for
records and their renamings, while the ultrafilter theorem concerns a selection that every
ultrafilter makes, so its conclusion is that no ultrafilter is fixed at all. In the observer setting
the same step reads: since every selection must land in the pair, an equivariant selection forces
the record to have no automorphism exchanging it (`not_mem_automorphisms_of_selects`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Observation (Record)

universe uO

variable {O : Type uO}

/-- **The observer theorem from the shared form.** -/
theorem no_equivariant_selection_of_shared (select : Record O → O)
    (equivariant : ∀ (π : O ≃ O) (r : Record O), select (Record.rename π r) = π (select r))
    {r : Record O} {π : O ≃ O} (aut : π ∈ Record.automorphisms r) {a b : O} (apart : a ≠ b)
    (exchanges : π a = b ∧ π b = a) : select r ≠ a ∧ select r ≠ b :=
  select_ne_of_fixed (Record.rename π) π select (equivariant π) aut apart exchanges

/-- The derived statement is the observer library's statement: the two proofs are equal by proof
irrelevance, which checks that the propositions coincide. -/
theorem no_equivariant_selection_of_shared_eq :
    @no_equivariant_selection_of_shared.{uO} = @AnnotatedRuns.no_equivariant_selection.{uO} :=
  rfl

/-- **The ultrafilter form read for records**: an equivariant selection that always lands in a
pair `a`, `b` forbids every automorphism of the record that exchanges them. -/
theorem not_mem_automorphisms_of_selects (select : Record O → O)
    (equivariant : ∀ (π : O ≃ O) (r : Record O), select (Record.rename π r) = π (select r))
    {r : Record O} {a b : O} (apart : a ≠ b) (lands : select r = a ∨ select r = b) {π : O ≃ O}
    (exchanges : π a = b ∧ π b = a) : π ∉ Record.automorphisms r := fun aut => by
  obtain ⟨notA, notB⟩ := no_equivariant_selection_of_shared select equivariant aut apart exchanges
  rcases lands with h | h
  · exact notA h
  · exact notB h

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms no_equivariant_selection_of_shared
#print axioms no_equivariant_selection_of_shared_eq
#print axioms not_mem_automorphisms_of_selects

end Mettapedia.Logic.Metaphysics.Ultrainfinite
