import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilies
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralConversionCode

/-!
# Executable codes for the authored native List and identity roots

The existing `IotaEvidenceCode` is finite syntax carrying all raw arguments
of the List nil/cons and identity-elimination equations. Decoding reconstructs
their exact endpoints, including repeated element and endpoint arguments.
No typing receipt, normalization oracle, or proposition-valued eligibility
test is hidden in the code.

Soundness and completeness concern every root of the existing declaration
package in every open ambient context. Its inherited computation is empty and
its declarations have no delta values, so the three authored iota constructors
exhaust its roots. This is conversion-evidence checking, not a total conversion
decision procedure or formation-sensitive List/J subject reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeIndexedRootConversionCode

open Presentation Presentation.Declaration
open NativeIndexedFamilies.Intrinsic

variable {n : Nat}

/-- Decode the original receipt data directly into the authored root pair. -/
def decode : IotaEvidenceCode n → Option (Tower.Tm n × Tower.Tm n)
  | .nil element motive nilCase consCase =>
      some (eliminateApp element motive nilCase consCase (nilApp element), nilCase)
  | .cons element motive nilCase consCase head tail =>
      some (eliminateApp element motive nilCase consCase (consApp element head tail),
        .app (.app (.app consCase head) tail)
          (eliminateApp element motive nilCase consCase tail))
  | .identity element point motive reflCase =>
      some (identityEliminateApp element point motive reflCase point (.refl point), reflCase)

/-- Every existing informative receipt decodes to its exact indexed endpoints. -/
theorem decode_evidence {left right : Tower.Tm n} (evidence : IotaEvidence n left right) :
    decode evidence.code = some (left, right) := by
  cases evidence <;> rfl

/-- A decoded pair is licensed by the actual native declaration package. -/
theorem decode_sound (code : IotaEvidenceCode n) {left right : Tower.Tm n}
    (decoded : decode code = some (left, right)) :
    rules.computation.step left right := by
  cases code with
  | nil element motive nilCase consCase =>
      cases Option.some.inj decoded
      exact iota_nil
  | cons element motive nilCase consCase head tail =>
      cases Option.some.inj decoded
      exact iota_cons
  | identity element point motive reflCase =>
      cases Option.some.inj decoded
      exact iota_identity

/-- No root of the actual rules is omitted, including at arbitrary open arity. -/
theorem decode_complete {left right : Tower.Tm n}
    (step : rules.computation.step left right) :
    ∃ code : IotaEvidenceCode n, decode code = some (left, right) := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta unfolding =>
      rw [rawSignature_valueOf_none] at unfolding
      cases unfolding
  | declared retained =>
      obtain ⟨evidence⟩ := retained
      exact ⟨evidence.code, decode_evidence evidence⟩

theorem root_iff_decodes {left right : Tower.Tm n} :
    rules.computation.step left right ↔
      ∃ code : IotaEvidenceCode n, decode code = some (left, right) :=
  ⟨decode_complete, fun ⟨code, decoded⟩ => decode_sound code decoded⟩

/-- The native authored roots qualify the general structural conversion checker. -/
def rootDecoder : StructuralConversionCode.RootDecoder rules.computation where
  Code := IotaEvidenceCode
  decode := decode
  sound := decode_sound
  complete := decode_complete

/-- Checking a proposed root receipt is executable equality on finite syntax. -/
def check (code : IotaEvidenceCode n) (left right : Tower.Tm n) : Bool :=
  decide (decode code = some (left, right))

theorem check_iff (code : IotaEvidenceCode n) (left right : Tower.Tm n) :
    check code left right = true ↔ decode code = some (left, right) := by
  simp [check]

theorem check_sound (code : IotaEvidenceCode n) {left right : Tower.Tm n}
    (checked : check code left right = true) : rules.computation.step left right :=
  decode_sound code ((check_iff code left right).mp checked)

theorem root_iff_checked {left right : Tower.Tm n} :
    rules.computation.step left right ↔
      ∃ code : IotaEvidenceCode n, check code left right = true := by
  simp only [check_iff, root_iff_decodes]

/-! ## Exact authored branches and corrupted claims -/

def nilCode : IotaEvidenceCode 4 := .nil (.var 3) (.var 2) (.var 1) (.var 0)

def consCode : IotaEvidenceCode 6 :=
  .cons (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def identityCode : IotaEvidenceCode 4 :=
  .identity (.var 3) (.var 2) (.var 1) (.var 0)

theorem nil_checked : check nilCode nilIotaLeft nilIotaRight = true := by decide

theorem cons_checked : check consCode consIotaLeft consIotaRight = true := by decide

theorem identity_checked : check identityCode identityIotaLeft identityIotaRight = true := by decide

/-- A changed motive is not allowed to certify the original nil equation. -/
theorem changed_motive_rejected :
    check (.nil (.var 3) (.var 0) (.var 1) (.var 0)) nilIotaLeft nilIotaRight = false := by
  decide

/-- The element parameter must agree with the element inside the constructor. -/
theorem changed_element_rejected :
    check nilCode
      (eliminateApp (.var 3) (.var 2) (.var 1) (.var 0) (nilApp (.var 2)))
      nilIotaRight = false := by decide

/-- The cons equation includes the recursive call; dropping it changes the output. -/
theorem missing_recursive_result_rejected :
    check consCode consIotaLeft
      (.app (.app (.var 2) (.var 1)) (.var 0)) = false := by decide

/-- A receipt for reflexivity at one point cannot license another endpoint. -/
theorem changed_identity_endpoint_rejected :
    check identityCode
      (identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0) (.var 1) (.refl (.var 2)))
      identityIotaRight = false := by decide

/-- The identity branch cannot claim a different result. -/
theorem changed_identity_output_rejected :
    check identityCode identityIotaLeft (.var 1) = false := by decide

/-- Constructor tags remain part of the receipt, even at the same arity. -/
theorem wrong_branch_rejected :
    check identityCode nilIotaLeft nilIotaRight = false := by decide

#print axioms decode_sound
#print axioms decode_complete
#print axioms rootDecoder
#print axioms root_iff_checked
#print axioms nil_checked
#print axioms cons_checked
#print axioms identity_checked
#print axioms changed_motive_rejected
#print axioms changed_element_rejected
#print axioms missing_recursive_result_rejected
#print axioms changed_identity_endpoint_rejected
#print axioms changed_identity_output_rejected

end NativeIndexedRootConversionCode
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
