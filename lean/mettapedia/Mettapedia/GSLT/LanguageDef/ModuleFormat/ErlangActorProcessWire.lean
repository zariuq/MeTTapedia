import Mettapedia.Languages.Erlang.ActorProcessStore
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-! The actor controller's local-process carrier. Mailbox and machine
representations remain explicit parameters; this layer neither evaluates
them nor identifies distinct process keys. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorProcessWire

open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef CettaWire

def process (box : Mailbox Value → Term) (machine : MachineState → Term) (entry : LocalProcess) : Term :=
  .application "ErLocal" [.natural entry.identity, box entry.mailbox, machine entry.machine]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorProcessWire
