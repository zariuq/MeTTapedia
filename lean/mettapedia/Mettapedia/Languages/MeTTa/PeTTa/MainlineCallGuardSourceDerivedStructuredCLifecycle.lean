import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

/-!
# Lifecycle qualification for source-derived call-guard bodies

Each theorem below evaluates exactly one authored source occurrence.  Keeping
these certificates separate bounds elaboration while preserving an explicit,
auditable correspondence between source rules and StructuredC bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

theorem bodyOptionAt_finish :
    bodyOptionAt ⟨0, by decide⟩ = some finishBody := by
  decide +kernel

theorem bodyOptionAt_skipHead :
    bodyOptionAt ⟨1, by decide⟩ = some skipHeadBody := by
  decide +kernel

theorem bodyOptionAt_skipArity :
    bodyOptionAt ⟨2, by decide⟩ = some skipArityBody := by
  decide +kernel

theorem bodyOptionAt_beginDeclaration :
    bodyOptionAt ⟨3, by decide⟩ = some beginDeclarationBody := by
  decide +kernel

theorem bodyOptionAt_argumentsFinished :
    bodyOptionAt ⟨4, by decide⟩ = some argumentsFinishedBody := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
