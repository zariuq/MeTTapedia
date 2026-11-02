import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore

/-! # Actual creation, lookup reuse, retained IDs and duplicate-row refusal -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore.Controls

def once := (Store.empty (K := Nat)).intern 7
def twice := once.1.intern 7
def extended := once.1.intern 9

theorem created_once : once.2 = (0, true) ∧ once.1.rows = {(0, 7)} := by decide +kernel
theorem repeated_is_lookup : twice.2 = (0, false) ∧ twice.1.rows = once.1.rows := by decide +kernel
theorem new_key_gets_next_id : extended.2 = (1, true) ∧ extended.1.lookup 7 = some 0 ∧ extended.1.lookup 9 = some 1 := by
  decide +kernel
theorem lookup_has_one_witness : (extended.1.query 7).card = 1 ∧ (extended.1.query 9).card = 1 := by decide +kernel
theorem missing_key_has_no_witness : extended.1.query 11 = ∅ := by decide +kernel

theorem duplicate_rows_cannot_represent_registry {K : Type*} [DecidableEq K]
    (registry : CanonicalMetadataRegistry.Registry K) (key : K) :
    ¬Represents registry {(0, key), (1, key)} := by
  intro represented
  let bad : Store K := ⟨registry, {(0, key), (1, key)}, represented⟩
  have impossible : (0 : Nat) = 1 := bad.canonical_row_unique (key := key) (by simp [bad]) (by simp [bad])
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore.Controls
