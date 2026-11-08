import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Rename

/-!
# Canonical private presence in a full physical CMR occurrence world

Arbitrary public/theorem rows share a world with the actually maintained
canonical private store. Physical locations keep those rows from supplying
metadata witnesses. The core's count-one ask is exactly one canonical private
read witness, independently of the substitution and the unrelated frame.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenseWorld

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open HOLLightLicensedActivation
open HOLLightCanonicalLicenses (Key Store)

abbrev CoreOccurrence := IndexedOccurrences.Occurrence InferenceSchemaKernel.Value
abbrev Occurrence := CoreOccurrence ⊕ (Nat × Key)

local instance occurrenceDecidableEq : DecidableEq Occurrence := fun first second => instDecidableEqSum first second

def label : Occurrence → Value
  | .inl row => lift (IndexedOccurrences.label row)
  | .inr row => HOLLightCanonicalLicenses.label row

def world (frame : Finset CoreOccurrence) (store : Store) : Finset Occurrence :=
  frame.image Sum.inl ∪ store.rows.image Sum.inr

theorem inl_world (frame : Finset CoreOccurrence) (store : Store) (row : CoreOccurrence) :
    Sum.inl row ∈ world frame store ↔ row ∈ frame := by simp [world, Finset.mem_image]

theorem inr_world (frame : Finset CoreOccurrence) (store : Store) (row : Nat × Key) :
    Sum.inr row ∈ world frame store ↔ row ∈ store.rows := by simp [world, Finset.mem_image]

theorem core_row_never_supplies_license
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (key : Key) (row : CoreOccurrence) :
    ¬locatedAction.E (locatedAction.apply assignment (licenses, HOLLightCanonicalLicenses.payload key))
      (locatedAction.apply assignment (label (.inl row))) := by
  intro same
  cases same.1

theorem region_is_private_query (frame : Finset CoreOccurrence) (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (key : Key) :
    Check.matches locatedAction assignment label (world frame store) (licenses, HOLLightCanonicalLicenses.payload key) =
      (store.query key).image Sum.inr := by
  ext occurrence
  cases occurrence with
  | inl row =>
      simp [Check.matches, core_row_never_supplies_license, Finset.mem_image]
  | inr row =>
      have matched : locatedAction.E
          (locatedAction.apply assignment (licenses, HOLLightCanonicalLicenses.payload key))
          (locatedAction.apply assignment (label (.inr row))) ↔ row.2 = key :=
        HOLLightCanonicalLicenses.matches_iff_key assignment key row
      simp only [Check.matches, Finset.mem_filter, inr_world, matched]
      simp [CanonicalMetadataStore.Store.query, Finset.mem_image]

theorem canonical_count_one (frame : Finset CoreOccurrence) (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (index : Nat) (known : store.lookup key = some index) :
    Check.Holds locatedAction assignment label (world frame store)
      (.count (licenses, HOLLightCanonicalLicenses.payload key) 1) := by
  change (Check.matches locatedAction assignment label (world frame store) _).card = 1
  rw [region_is_private_query, store.query_of_present key index known]
  simp

theorem missing_license_absent (frame : Finset CoreOccurrence) (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (missing : store.lookup key = none) :
    Check.Holds locatedAction assignment label (world frame store)
      (.absent (licenses, HOLLightCanonicalLicenses.payload key)) := by
  classical
  intro occurrence present matched
  have inRegion : occurrence ∈ Check.matches locatedAction assignment label (world frame store)
      (licenses, HOLLightCanonicalLicenses.payload key) := Finset.mem_filter.mpr ⟨present, matched⟩
  rw [region_is_private_query, store.query_of_absent key missing] at inRegion
  simp at inRegion

theorem successful_read_is_unique (frame : Finset CoreOccurrence) (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (key : Key) (index : Nat) (known : store.lookup key = some index) :
    ∃! occurrence, occurrence ∈ world frame store ∧
      locatedAction.E (locatedAction.apply assignment (licenses, HOLLightCanonicalLicenses.payload key))
        (locatedAction.apply assignment (label occurrence)) := by
  classical
  have query : Check.matches locatedAction assignment label (world frame store)
      (licenses, HOLLightCanonicalLicenses.payload key) = {Sum.inr (index, key)} := by
    rw [region_is_private_query, store.query_of_present key index known]
    simp
  refine ⟨.inr (index, key), ?_, ?_⟩
  · have member : Sum.inr (index, key) ∈ Check.matches locatedAction assignment label (world frame store)
        (licenses, HOLLightCanonicalLicenses.payload key) := by rw [query]; exact Finset.mem_singleton_self _
    exact Finset.mem_filter.mp member
  · intro occurrence properties
    have member : occurrence ∈ Check.matches locatedAction assignment label (world frame store)
        (licenses, HOLLightCanonicalLicenses.payload key) := Finset.mem_filter.mpr properties
    rw [query] at member
    exact Finset.mem_singleton.mp member

end Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenseWorld
