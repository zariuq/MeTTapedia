import Mathlib.Data.List.Basic
import Mathlib.Data.List.Monad

/-!
# Complete candidate filters preserve the resolver's full result word

The resolver is an existing pure operation, not a replacement evaluator.
Filtering retains source order and every occurrence, including duplicates.
This is not equality of the work spent testing rejected candidates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads

universe u v
variable {Occurrence : Type u} {Answer : Type v}

def enumerate (keep : Occurrence → Bool) (rows : List Occurrence) : List Occurrence :=
  rows.filter keep

theorem enumerate_complete (keep : Occurrence → Bool) (rows : List Occurrence)
    (possible : Occurrence → Prop)
    (complete : ∀ occurrence ∈ rows, possible occurrence → keep occurrence = true)
    (occurrence : Occurrence) (member : occurrence ∈ rows) (matched : possible occurrence) :
    occurrence ∈ enumerate keep rows :=
  List.mem_filter.mpr ⟨member, complete occurrence member matched⟩

theorem enumerate_length_le (keep : Occurrence → Bool) (rows : List Occurrence) :
    (enumerate keep rows).length ≤ rows.length :=
  List.length_filter_le keep rows

theorem enumerate_resolver_word (keep : Occurrence → Bool) (resolve : Occurrence → List Answer)
    (rows : List Occurrence)
    (complete : ∀ occurrence ∈ rows, resolve occurrence ≠ [] → keep occurrence = true) :
    (enumerate keep rows).flatMap resolve = rows.flatMap resolve := by
  induction rows with
  | nil => rfl
  | cons occurrence rows ih =>
      have later := ih (fun item member => complete item (List.mem_cons_of_mem _ member))
      by_cases accepted : keep occurrence = true
      · simpa [enumerate, List.filter_cons, accepted] using congrArg (resolve occurrence ++ ·) later
      · have empty : resolve occurrence = [] := by
          by_contra nonempty
          exact accepted (complete occurrence (List.mem_cons_self ..) nonempty)
        simpa [enumerate, List.filter_cons, accepted, empty] using later

theorem enumerate_resolver_count [DecidableEq Answer]
    (keep : Occurrence → Bool) (resolve : Occurrence → List Answer) (rows : List Occurrence)
    (complete : ∀ occurrence ∈ rows, resolve occurrence ≠ [] → keep occurrence = true)
    (answer : Answer) :
    ((enumerate keep rows).flatMap resolve).count answer = (rows.flatMap resolve).count answer := by
  rw [enumerate_resolver_word keep resolve rows complete]

#print axioms enumerate_resolver_word
#print axioms enumerate_resolver_count

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads
