import Mettapedia.Languages.Erlang.Network
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-! The actor adapter's envelope and delivery-result wire shapes. Payloads
remain parametric; this codec does not equate distinct message occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorNetworkWire

open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef CettaWire

def envelope {α : Type} (encode : α → Term) (message : Envelope α) : Term :=
  .application "ErEnvelope" [.natural message.key.sender, .natural message.key.receiver, encode message.payload]

def delivery {α : Type} (encode : α → Term) (result : Envelope α × List (Envelope α)) : Term :=
  .application "ErDelivery" [.natural result.1.key.sender, .natural result.1.key.receiver, encode result.1.payload,
    encodeList (envelope encode) result.2]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorNetworkWire
