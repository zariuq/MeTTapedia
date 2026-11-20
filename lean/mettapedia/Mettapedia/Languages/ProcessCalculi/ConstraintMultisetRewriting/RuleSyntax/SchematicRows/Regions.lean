import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.CheckAccepts

/-!
# Schematic-row observations through the shared region-query interface

At a model, a region selects physical row occurrences whose datum can read the
instantiated pattern. The none query, count and exact collect query are observations of that
one region, using `PredicateQueryAdmission.RegionQuery`. No equivalence on rows
is imposed to represent overlapping membership regions.

The semantic region uses classical proposition decision. An executable solver
licence is separate. For shared-only labels the occurrence set agrees exactly
with the existing single-firing observation, including multiplicities of distinct
occurrences with equal payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Regions

open Interface (Frames)
open PredicateQueryAdmission (RegionQuery)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf)

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {a : Obj} {O : Type uOcc}

noncomputable def membership (pattern : Tm a) {b : Obj} (σ : Hom a b) : Row Tm a → Bool := by
  classical
  exact fun row => decide (Row.ReadsAt X σ (X.act σ pattern) row)

theorem membership_iff (pattern : Tm a) {b : Obj} (σ : Hom a b) (row : Row Tm a) :
    membership X pattern σ row = true ↔ Row.ReadsAt X σ (X.act σ pattern) row := by
  classical
  simp [membership]

/-- Ask a family of the same region-query interface at every model of knowledge. -/
def asks (knowledge : EquationStore (Tm a)) (label : O → Row Tm a) (present : Finset O)
    (query : (b : Obj) → RegionQuery (Row Tm a) (Hom a b) O) : Prop :=
  X.Entails knowledge fun b σ => (query b).Holds σ label present

theorem none_iff (pattern : Tm a) {b : Obj} (σ : Hom a b)
    (label : O → Row Tm a) (present : Finset O) :
    (RegionQuery.predicate .none (membership X pattern)).Holds σ label present ↔
      ∀ o ∈ present, ¬ Row.ReadsAt X σ (X.act σ pattern) (label o) := by
  classical
  simp [RegionQuery.none_holds_iff, membership]

theorem shared_region_eq (pattern : Tm a) {b : Obj} (σ : Hom a b)
    (label : O → Tm a) (present : Finset O) :
    regionOf (fun o => Row.shared (label o)) present (membership X pattern σ) =
      matchesAt X σ label present pattern := by
  classical
  ext o
  simp only [mem_regionOf, membership_iff, Row.readsAt_shared, mem_matchesAt]
  exact and_congr_right fun _ => ⟨(X.equivalence b).symm, (X.equivalence b).symm⟩

theorem shared_count_iff (pattern : Tm a) (number : Nat) {b : Obj} (σ : Hom a b)
    (label : O → Tm a) (present : Finset O) :
    (RegionQuery.count (membership X pattern) number).Holds σ (fun o => Row.shared (label o)) present ↔
      checkHolds X σ label present (.count pattern number) := by
  rw [RegionQuery.count_holds_iff, shared_region_eq]
  exact Iff.rfl

theorem shared_predicate_iff (pattern : Tm a) (quantifier : Quantifier) {b : Obj} (σ : Hom a b)
    (label : O → Tm a) (present : Finset O) :
    (RegionQuery.predicate quantifier (membership X pattern)).Holds σ (fun o => Row.shared (label o))
        present ↔
      checkHolds X σ label present (.predicate quantifier pattern) := by
  show quantifier.Accepts (regionOf _ present (membership X pattern σ)) ↔ _
  rw [shared_region_eq, checkHolds_predicate_iff]

theorem shared_collect_iff (pattern : Tm a) (seen : Finset O) {b : Obj} (σ : Hom a b)
    (label : O → Tm a) (present : Finset O) :
    (RegionQuery.exact (membership X pattern) seen).Holds σ (fun o => Row.shared (label o)) present ↔
      matchesAt X σ label present pattern = seen := by
  rw [RegionQuery.exact_holds_iff, shared_region_eq]

#print axioms none_iff
#print axioms shared_region_eq
#print axioms shared_count_iff
#print axioms shared_predicate_iff
#print axioms shared_collect_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Regions
