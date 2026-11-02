import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionReadback
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompletionControls

/-! Admission checks cover ordinary module names, collisions with the
loaded controller and symbols that cannot be rendered as source. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionControls

open Mettapedia.GSLT.LanguageDef ModuleFormat.OCamlCompilation
open OCamlCompletionControls

def prepared? := prepare fallbackProgram

def accepted (name : String) : Bool :=
  match prepared? with
  | .error _ => false
  | .ok prepared => (ExecutionData.emitText? prepared name).toOption.isSome

#guard accepted "completion-program"
#guard !accepted "gslt:ml"
#guard !accepted "gslt"
#guard !accepted "bad name"
#guard !accepted "bad(name"

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionControls
