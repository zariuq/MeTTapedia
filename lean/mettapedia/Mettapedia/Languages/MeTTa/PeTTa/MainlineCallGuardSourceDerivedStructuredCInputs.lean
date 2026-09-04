import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

/-!
# Input-mode qualification for source-derived call-guard bodies

Each certificate evaluates one authored input-mode occurrence independently.
This makes every guarded state update visible without constructing one large
normalization proof for the complete source inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

theorem bodyOptionAt_rawInput :
    bodyOptionAt ⟨5, by decide⟩ = some rawInputBody := by
  decide +kernel

theorem bodyOptionAt_undefinedInput :
    bodyOptionAt ⟨6, by decide⟩ = some undefinedInputBody := by
  decide +kernel

theorem bodyOptionAt_holeInput :
    bodyOptionAt ⟨7, by decide⟩ = some holeInputBody := by
  decide +kernel

theorem bodyOptionAt_checkedInput :
    bodyOptionAt ⟨8, by decide⟩ = some checkedInputBody := by
  decide +kernel

theorem bodyOptionAt_openInput :
    bodyOptionAt ⟨9, by decide⟩ = some openInputBody := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
