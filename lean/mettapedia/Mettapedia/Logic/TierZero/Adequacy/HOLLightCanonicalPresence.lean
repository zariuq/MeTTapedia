import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenseWorld

/-!
# One canonical private read is the existing nonbinding positive-presence ask

The equivalence holds in the actual canonical row representation and every
unrelated public/theorem frame. Presence is the core's existing count-one
guard. Its entailment does not extend the equation store or choose another
administrative witness. Duplicated private rows remain outside this contract.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalPresence

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightLicensedActivation
open HOLLightCanonicalLicenses (Key Store)
open HOLLightCanonicalLicenseWorld

theorem unique_read_iff_positive_presence (frame : Finset CoreOccurrence) (store : Store)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (key : Key) :
    (∃! occurrence, occurrence ∈ world frame store ∧
      locatedAction.E (locatedAction.apply assignment (licenses, HOLLightCanonicalLicenses.payload key))
        (locatedAction.apply assignment (label occurrence))) ↔
    Check.Holds locatedAction assignment label (world frame store)
      (.count (licenses, HOLLightCanonicalLicenses.payload key) 1) := by
  cases known : store.lookup key with
  | some index =>
      exact ⟨fun _ => canonical_count_one frame store assignment key index known,
        fun _ => successful_read_is_unique frame store assignment key index known⟩
  | none =>
      constructor
      · rintro ⟨occurrence, ⟨present, matched⟩, _⟩
        exact False.elim (missing_license_absent frame store assignment key known occurrence present matched)
      · intro guard
        change (Check.matches locatedAction assignment label (world frame store)
          (licenses, HOLLightCanonicalLicenses.payload key)).card = 1 at guard
        rw [region_is_private_query, store.query_of_absent key known] at guard
        simp at guard

theorem registered_presence_entailed (frame : Finset CoreOccurrence) (store : Store)
    (key : Key) (index : Nat) (known : store.lookup key = some index) (equations : EquationStore Value) :
    locatedAction.Entails equations (fun assignment =>
      Check.Holds locatedAction assignment label (world frame store)
        (.count (licenses, HOLLightCanonicalLicenses.payload key) 1)) := by
  intro assignment _
  exact canonical_count_one frame store assignment key index known

theorem presence_entailment_has_registered_witness (frame : Finset CoreOccurrence) (store : Store)
    (key : Key) (equations : EquationStore Value) (consistent : locatedAction.Consistent equations)
    (entailed : locatedAction.Entails equations (fun assignment =>
      Check.Holds locatedAction assignment label (world frame store)
        (.count (licenses, HOLLightCanonicalLicenses.payload key) 1))) :
    ∃ index, store.lookup key = some index := by
  obtain ⟨assignment, solved⟩ := consistent
  cases known : store.lookup key with
  | some index => exact ⟨index, rfl⟩
  | none =>
      have guard := entailed assignment solved
      change (Check.matches locatedAction assignment label (world frame store)
        (licenses, HOLLightCanonicalLicenses.payload key)).card = 1 at guard
      rw [region_is_private_query, store.query_of_absent key known] at guard
      simp at guard

end Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalPresence
