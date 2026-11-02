import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary

/-! The indexed program retains the shared step module and uses an ordinary
service controller around it. Provider answers become typed finite snapshots;
the source-to-native service/controller correspondence remains a separate
proof obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ExecutionData

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def spec (prepared : Prepared) : CompleteEmission.Spec :=
  ⟨plan prepared, [], .base "MlConfig", .canonical⟩

def arguments (prepared : Prepared) : List CettaWire.Term :=
  [CompletePlanWire.planTerm (plan prepared) [] [] (.base "MlConfig"),
   StandardWire.commitTerm (plan prepared) .canonical (CompleteEmission.table (spec prepared)),
   InferenceCettaWire.encodePattern (initial prepared.program)]

def beginHead (name : String) : String := name ++ ":begin"
def runHead (name : String) : String := name ++ ":run"

def beginBody (prepared : Prepared) : Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  WireKit.apply "gslt:ml:begin" ((arguments prepared).map CettaWireAtom.encode)

def runBody (name : String) : Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  WireKit.apply "let*" [
    .expression [
      .expression [.var "initial", WireKit.apply (beginHead name) []],
      .expression [.var "finished", WireKit.apply "gslt:ml:advance" [.var "ticks", .var "quantum", .var "initial"]]],
    WireKit.apply "gslt:ml:result" [.var "finished"]]

def wrapper (prepared : Prepared) (name : String) : SpaceSemantics.Program where
  equations := [⟨beginHead name, [], beginBody prepared⟩,
    ⟨runHead name, [.var "ticks", .var "quantum"], runBody name⟩]
  declarations := [CompleteEmission.declaration (beginHead name) 0,
    .expression [.symbol ":", .symbol (runHead name),
      .expression [.symbol "->", .symbol "Number", .symbol "Number", .symbol "%Undefined%"]]]
  layout := [.declaration, .equation, .declaration, .equation]

def program (prepared : Prepared) (name : String) : SpaceSemantics.Program :=
  (CompleteEmission.program (spec prepared) (name ++ ":step") .classes).append (wrapper prepared name)

def library (prepared : Prepared) (name : String) : BridgeKit.Library :=
  ⟨OCamlControllerSource.runtime, program prepared name, [name ++ ":"]⟩

def wrapperReady (prepared : Prepared) (name : String) : Bool :=
  (library prepared name).headReady (beginHead name) &&
    ((library prepared name).equationOf (runHead name)).any (BridgeKit.Library.demandReady (library prepared name)) &&
    !argumentIsRaw (library prepared name).runtime (runHead name) 0 &&
    !argumentIsRaw (library prepared name).runtime (runHead name) 1

def emit? (prepared : Prepared) (name : String) : Except String SpaceSemantics.Program :=
  match CompleteEmission.emit? (spec prepared) (name ++ ":step") .classes with
  | .error _ => .error s!"indexed OCaml step plan is not admitted: {reprStr (plan prepared).obligations}"
  | .ok kernel =>
      if (library prepared name).check && wrapperReady prepared name then
        .ok (kernel.append (wrapper prepared name))
      else .error "OCaml module entries collide with the loaded controller or violate their call contracts"

def emitText? (prepared : Prepared) (name : String) : Except String String :=
  match emit? prepared name with
  | .error reason => .error reason
  | .ok emitted => match ReadAfterRender.renderProgram? emitted with
      | some text => .ok text
      | none => .error "OCaml module contains an unrenderable source atom"

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ExecutionData
