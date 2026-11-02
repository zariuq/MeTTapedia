import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorProcessWire
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorNetworkWire

/-! Actor-world records retain process order, in-flight message occurrences,
the fresh counter and administrative history. The program remains the
separate compilation parameter represented by each process machine plan. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorWorldWire

open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef CettaWire

def world (box : Mailbox Value → Term) (machine : MachineState → Term) (payload : Value → Term)
    (system : ActorSystem) (history : Term) : Term := .application "ErActorSystem"
  [encodeList (ErlangActorProcessWire.process box machine) system.processes,
   encodeList (ErlangActorNetworkWire.envelope payload) system.network, .natural system.nextPid, history]

def record (effect history : Term) : Term := .application "LCons" [effect, history]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorWorldWire
