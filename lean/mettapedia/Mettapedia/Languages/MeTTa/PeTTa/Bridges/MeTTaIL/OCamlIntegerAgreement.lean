import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionBody
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandTransport

/-! Shared integer calls keep their exact dispatch, demand and bodies
after the word and OCaml service libraries are loaded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerAgreement

open Eval BridgeKit OCamlControllerSource

def allowed (head : String) : Bool := head == "gslt:integer:divmod"

theorem agreement : ProgramAgreementOn allowed integerLibrary.runtime runtime := by
  apply agreement_trans
  · apply Library.agreement_on word_checked
    intro head supported
    have same : head = "gslt:integer:divmod" := beq_iff_eq.mp supported
    subst head
    decide +kernel
  · apply Library.agreement_on checked
    intro head supported
    have same : head = "gslt:integer:divmod" := beq_iff_eq.mp supported
    subst head
    decide +kernel

#print axioms agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerAgreement
