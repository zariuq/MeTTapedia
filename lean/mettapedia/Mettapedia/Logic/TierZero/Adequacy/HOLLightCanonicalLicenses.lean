import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore

/-!
# Canonical private context rows: one read equals positive count presence

The actual finite registry/store operation supplies canonical private rows.
Context IDs and inclusion-pair IDs use their existing injective ABT encodings.
Under that representation, a successful metadata lookup has one unification
read witness and exactly the core's count-one observation. This does not claim
the same equivalence for arbitrary duplicated private rows.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenses

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightLicensedActivation

abbrev Key := Nat ⊕ (Nat × Nat)
abbrev Store := CanonicalMetadataStore.Store Key

def payload : Key → Tm
  | .inl context => available context
  | .inr (before, after) => included before after

theorem payload_injective : Function.Injective payload := by
  intro first second same
  cases first with
  | inl context =>
      cases second with
      | inl other => exact congrArg Sum.inl (available_injective same)
      | inr pair => exact False.elim (available_ne_included context pair.1 pair.2 same)
  | inr pair =>
      cases second with
      | inl context => exact False.elim (available_ne_included context pair.1 pair.2 same.symm)
      | inr other =>
          have equal := included_injective same
          exact congrArg Sum.inr (Prod.ext equal.1 equal.2)

theorem payload_fixed (key : Key) (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (payload key) = payload key := by
  cases key with
  | inl context => exact available_fixed context assignment
  | inr pair => exact included_fixed pair.1 pair.2 assignment

def label (row : Nat × Key) : Value := (licenses, payload row.2)

theorem matches_iff_key (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (row : Nat × Key) :
    locatedAction.E (locatedAction.apply assignment (licenses, payload key))
      (locatedAction.apply assignment (label row)) ↔ row.2 = key := by
  change (licenses = licenses ∧ action.apply assignment (payload key) = action.apply assignment (payload row.2)) ↔ _
  rw [payload_fixed, payload_fixed]
  simpa only [true_and, payload_injective.eq_iff] using (eq_comm : key = row.2 ↔ row.2 = key)

theorem region_is_canonical_query (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (key : Key) :
    Check.matches locatedAction assignment label store.rows (licenses, payload key) = store.query key := by
  ext row
  simp only [Check.matches, CanonicalMetadataStore.Store.query, Finset.mem_filter]
  rw [matches_iff_key]

theorem count_one_for_registered_key (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (index : Nat) (found : store.lookup key = some index) :
    Check.Holds locatedAction assignment label store.rows (.count (licenses, payload key) 1) := by
  change (Check.matches locatedAction assignment label store.rows (licenses, payload key)).card = 1
  rw [region_is_canonical_query]
  exact store.successful_read_has_one_witness key index found

/-- The uniqueness comes from executed creation/lookup, not an assumed fresh
identity supplier or a quotient of duplicate metadata rows. -/
theorem unique_read_for_registered_key (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (index : Nat) (found : store.lookup key = some index) :
    ∃! row, row ∈ store.rows ∧ locatedAction.E (locatedAction.apply assignment (licenses, payload key))
      (locatedAction.apply assignment (label row)) := by
  refine ⟨(index, key), ?_, ?_⟩
  · exact ⟨(store.represented index key).mpr found, (matches_iff_key assignment key _).mpr rfl⟩
  · intro row present
    obtain ⟨other, otherKey⟩ := row
    have same : otherKey = key := (matches_iff_key assignment key _).mp present.2
    subst otherKey
    have indexSame := store.canonical_row_unique present.1 ((store.represented index key).mpr found)
    exact congrArg (fun id => (id, key)) indexSame

end Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenses
