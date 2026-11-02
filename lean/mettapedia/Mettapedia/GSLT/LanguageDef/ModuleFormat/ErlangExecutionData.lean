import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Emission of the indexed Erlang step language with an ordinary typed
service-epoch controller. The controller retains completed provider plans
and full runners. Universal source/controller correspondence and full E0
admission remain separate qualification obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.ExecutionData

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def spec (prepared : Prepared) : CompleteEmission.Spec :=
  ⟨plan prepared, [], .base "ErMachineConfig", .canonical⟩

def arguments (prepared : Prepared) : List CettaWire.Term :=
  [CompletePlanWire.planTerm (plan prepared) [] [] (.base "ErMachineConfig"),
   StandardWire.commitTerm (plan prepared) .canonical (CompleteEmission.table (spec prepared)),
   InferenceCettaWire.encodePattern (initial prepared.program)]

def emitText? (prepared : Prepared) (name : String) : Except String String := do
  let .ok kernel := CompleteEmission.emitText? (spec prepared) (name ++ ":step") .classes
    | throw s!"indexed Erlang step plan has open obligations: {reprStr (plan prepared).obligations}"
  let begin := (CettaWire.Term.application "gslt:er:begin" (arguments prepared)).render
  pure (kernel ++ "\n(: " ++ name ++ ":begin (-> %Undefined%))\n" ++
    "(= (" ++ name ++ ":begin) " ++ begin ++ ")\n" ++
    "(: " ++ name ++ ":run (-> Number Number %Undefined%))\n" ++
    "(= (" ++ name ++ ":run $ticks $quantum) (let* (($initial (" ++ name ++ ":begin))" ++
    " ($finished (gslt:er:advance $ticks $quantum $initial))) (gslt:er:result $finished)))\n")

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation.ExecutionData
