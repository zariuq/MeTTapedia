import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

/-!
# Result-mode qualification for source-derived call-guard bodies

The result-mode certificates are isolated by source occurrence so the kernel
checks each structural translation without expanding the other fourteen.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

theorem bodyOptionAt_undefinedResult :
    bodyOptionAt ⟨10, by decide⟩ = some undefinedResultBody := by
  decide +kernel

theorem bodyOptionAt_holeResult :
    bodyOptionAt ⟨11, by decide⟩ = some holeResultBody := by
  decide +kernel

theorem bodyOptionAt_atomResult :
    bodyOptionAt ⟨12, by decide⟩ = some atomResultBody := by
  decide +kernel

theorem bodyOptionAt_checkedResult :
    bodyOptionAt ⟨13, by decide⟩ = some checkedResultBody := by
  decide +kernel

theorem bodyOptionAt_openResult :
    bodyOptionAt ⟨14, by decide⟩ = some openResultBody := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
