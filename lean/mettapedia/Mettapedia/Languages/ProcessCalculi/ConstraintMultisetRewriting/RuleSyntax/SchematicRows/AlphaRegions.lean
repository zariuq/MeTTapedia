import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaKey
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Regions

/-!
# Alpha-normalized payloads preserve all observations of the same occurrences

Only payload presentations change. The caller interpretation, physical world,
knowledge, location and authority remain fixed. Equal schematic payload keys
select exactly the same physical occurrences for every pattern, so any region
observation is preserved, including exact collect query and multiplicity-sensitive
counts. No physical rows are deduplicated by this theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaRegions

open Mettapedia.Logic.LP
open AlphaKey
open PredicateQueryAdmission (RegionQuery)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf)

universe uOcc
variable {signature : LPSignature} {O : Type uOcc}

theorem region_preserved (first second : O → RowClosure signature) (present : Finset O)
    (same : ∀ o ∈ present, key (first o) = key (second o))
    (source : Subst signature) (pattern : Term signature) :
    regionOf (fun o => Row.schematic (first o)) present
        (Regions.membership X pattern (b := PUnit.unit) source) =
      regionOf (fun o => Row.schematic (second o)) present
        (Regions.membership X pattern (b := PUnit.unit) source) := by
  classical
  ext o
  simp only [mem_regionOf, Regions.membership_iff, Row.ReadsAt]
  exact and_congr_right fun inside => key_eq_readings (same o inside) source (source.applyTerm pattern)

theorem observation_preserved (first second : O → RowClosure signature) (present : Finset O)
    (same : ∀ o ∈ present, key (first o) = key (second o))
    (source : Subst signature) (pattern : Term signature)
    (accepts : Subst signature → Finset O → Prop) :
    (⟨Regions.membership X pattern (b := PUnit.unit), accepts⟩ :
        RegionQuery (Row (OneFrame.Terms (Term signature)) PUnit.unit) (Subst signature) O).Holds
        source (fun o => Row.schematic (first o)) present ↔
      (⟨Regions.membership X pattern (b := PUnit.unit), accepts⟩ :
        RegionQuery (Row (OneFrame.Terms (Term signature)) PUnit.unit) (Subst signature) O).Holds
        source (fun o => Row.schematic (second o)) present := by
  change accepts source (regionOf _ _ _) ↔ accepts source (regionOf _ _ _)
  rw [region_preserved first second present same source pattern]

#print axioms region_preserved
#print axioms observation_preserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaRegions
