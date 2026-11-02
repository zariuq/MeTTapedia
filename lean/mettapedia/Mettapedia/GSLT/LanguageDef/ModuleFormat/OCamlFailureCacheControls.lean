import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochInvariant

/-! Typed cache rows can still be semantically false. A successful pattern
must never acquire a failure row. Genuine failure, append positions and
admission preservation are exercised separately.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.FailureCacheControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def parameter : OCaml.MatchPattern := .literal (.integer 7)
def seven : OCaml.Value := .literal (.integer 7)
def eight : OCaml.Value := .literal (.integer 8)
def good : GeneralPremise.ProviderSnapshot := GeneralPremise.ProviderAppend.appendRows provider [failureRow 0 eight]
def bad : GeneralPremise.ProviderSnapshot := GeneralPremise.ProviderAppend.appendRows provider [failureRow 0 seven]

theorem genuine_failure_sound : FailureRowsSound [parameter] good :=
  append_failure_sound [parameter] provider 0 parameter eight (initial_failure_rows_sound _) rfl (by rfl)

theorem successful_failure_row_unsound : ¬ FailureRowsSound [parameter] bad := by
  intro sound
  have failed := sound 0 parameter seven rfl (by simp [bad, GeneralPremise.ProviderAppend.appendRows])
  have matched : OCaml.matchPattern parameter seven = some [] := rfl
  rw [matched] at failed
  cases failed

theorem typed_row_alone_insufficient :
    GeneralPremise.checkProviderClosed baseLanguage (snapshot ⟨{code := #[], entry := 0}, [], baseLanguage⟩).free bad = true ∧
      ¬ FailureRowsSound [parameter] bad := by
  refine ⟨?_, successful_failure_row_unsound⟩
  apply GeneralPremise.ProviderAppend.checked_typing baseLanguage _ provider bad [failureRow 0 seven]
  · decide +kernel
  · exact failure_row_append_checked baseLanguage rfl _ provider rfl 0 seven

def program : OCaml.Program := {code := #[.literal .unit, .lambda parameter 0], entry := 1}

def epochControl : Bool := Id.run do
  match prepare program with
  | .error _ => return false
  | .ok prepared =>
    let original := plan prepared
    let updated := epochPlan prepared good
    let second := GeneralPremise.ProviderAppend.appendRows good [failureRow 0 (.literal (.integer 9))]
    return original.complete && updated.complete && (epochPlan prepared second).complete &&
      (updated.rules.map fun row => (row.declarationIndex, row.authored.name)) ==
        (original.rules.map fun row => (row.declarationIndex, row.authored.name)) &&
      second.rows[0]? == some (failureRow 0 eight) && second.rows[1]? == some (failureRow 0 (.literal (.integer 9)))

#guard epochControl
#print axioms genuine_failure_sound
#print axioms successful_failure_row_unsound
#print axioms typed_row_alone_insufficient

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.FailureCacheControls
