import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeTransport

/-!
# Controls for the renaming of native states

Native labels carry occurrence identities (`ContextualPredicateQueryAdmission.nativeLabels`), so a
predicate query's region may read an identity. The renaming of native firings therefore renames the
region with the sightings (`Interface.renameQuery`).

* **A query that reads an identity** (`marker`, selecting the occurrence `0`) holds at `{0}`
  (`marker_holds`), and its native renaming holds at the renamed world (`renamed_marker_holds`).
* **Renaming only the sightings breaks it** (`sightings_only_fails`): the first-order renaming
  (`AnnotatedRuns.renameQuery`) keeps the region and renames the sightings, which is sound for the
  first-order step, whose labels carry no identities, and unsound for native labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeTransportControls

/-- A predicate query whose region reads an occurrence identity: it selects the occurrence `0`. -/
def marker : PredicateQueryAdmission.Query (ℕ × Unit) Unit ℕ :=
  ⟨fun _ label => decide (label.1 = 0), {0}⟩

/-- The renaming that swaps the occurrences `0` and `1`. -/
def swap : ℕ ≃ ℕ := Equiv.swap 0 1

theorem marker_holds : (marker.atSolution ()).Holds (fun o => (o, ())) {0} := by
  decide

/-- **The native renaming keeps the query.** -/
theorem renamed_marker_holds :
    ((renameQuery swap marker).atSolution ()).Holds (fun o => (o, ())) (({0} : Finset ℕ).map swap.toEmbedding) :=
  (renameQuery_holds_iff swap marker () (fun _ => ()) {0}).mpr marker_holds

/-- **Renaming only the sightings breaks the query.** -/
theorem sightings_only_fails :
    ¬ ((AnnotatedRuns.renameQuery swap marker).atSolution ()).Holds (fun o => (o, ()))
      (({0} : Finset ℕ).map swap.toEmbedding) := by
  decide

#print axioms marker_holds
#print axioms renamed_marker_holds
#print axioms sightings_only_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeTransportControls
