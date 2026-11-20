import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRaceHelpers

/-!
# Invertible transport of source collect queries

An arbitrary solution-sensitive query can be carried across a contextual
isomorphism. Its rows are pulled back by the inverse, its observing solution
is composed with the forward map, and its occurrence answer is retained.
No extension law for noninvertible refinements is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} {Γ Δ Θ : Context rules}

namespace QueryTransport

def carry (comparison : Δ ≅ Γ) (query : Query levels O Γ) : Query levels O Δ where
  region solution row := query.region (solution ≫ comparison.hom) (row.reindex comparison.inv)
  reads := by
    intro observer solution first second same
    change (frames levels).E (first.reindex solution) (second.reindex solution) at same
    apply query.reads
    change (frames levels).E
      ((first.reindex comparison.inv).reindex (solution ≫ comparison.hom))
      ((second.reindex comparison.inv).reindex (solution ≫ comparison.hom))
    simpa only [← ContextualDependentEta.reindex_comp, Category.assoc,
      comparison.hom_inv_id, Category.comp_id] using same
  answer := query.answer

theorem region_carried (comparison : Δ ≅ Γ) (query : Query levels O Γ)
    (solution : Θ ⟶ Δ) (row : TotalTerm Γ) :
    (carry comparison query).region solution (row.reindex comparison.hom) ↔
      query.region (solution ≫ comparison.hom) row := by
  change query.region (solution ≫ comparison.hom)
    ((row.reindex comparison.hom).reindex comparison.inv) ↔ _
  rw [← ContextualDependentEta.reindex_comp, comparison.inv_hom_id, ContextualDependentEta.reindex_id]

theorem holds_carried (comparison : Δ ≅ Γ) (query : Query levels O Γ)
    (present : Finset O) (row : O → TotalTerm Γ) (solution : Θ ⟶ Δ) :
    (carry comparison query).Holds present (fun occurrence => (row occurrence).reindex comparison.hom) solution ↔
      query.Holds present row (solution ≫ comparison.hom) := by
  simp only [Query.Holds, carry, ← ContextualDependentEta.reindex_comp,
    comparison.inv_hom_id, ContextualDependentEta.reindex_id]

theorem carry_identity (query : Query levels O Γ) : carry (Iso.refl Γ) query = query := by
  cases query
  simp only [carry, Iso.refl_hom, Iso.refl_inv, Category.comp_id, ContextualDependentEta.reindex_id]

theorem carry_comp (first : Δ ≅ Γ) (second : Θ ≅ Δ) (query : Query levels O Γ) :
    carry second (carry first query) = carry (second ≪≫ first) query := by
  cases query
  simp only [carry, Iso.trans_hom, Iso.trans_inv, Category.assoc, ← ContextualDependentEta.reindex_comp]

end QueryTransport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.QueryTransport.holds_carried
