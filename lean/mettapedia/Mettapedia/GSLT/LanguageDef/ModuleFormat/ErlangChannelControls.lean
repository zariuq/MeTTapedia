import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF
import Mettapedia.Languages.Erlang.NetworkControls

/-! The authored channel operations are asked about through the operational
OSLF front door. Expected queues and mailboxes come from the independent
network/mailbox model. This checks the selected-channel component, not the
complete actor scheduler or the Core Erlang source compiler. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.Erlang
open ErlangMailbox (node atom values mailbox)

structure Example where
  name : String
  source : Pattern
  expected : Pattern
  wrong : Pattern

def sourceQueue (queue : List String) : List (Envelope String) := queue.map (⟨⟨1, 0⟩, ·⟩)

def sendCase (name : String) (message : String) (queue : List String) : Example :=
  let expected := Network.channel ⟨1, 0⟩ (Network.send ⟨⟨1, 0⟩, message⟩ (sourceQueue queue));
  ⟨name, node "ErChannelSend" [pid 1, pid 0, atom message, values (queue.map atom)],
    node "ErChannelQueued" [pid 1, pid 0, values (expected.map atom)],
    node "ErChannelQueued" [pid 1, pid 0, values (("wrong" :: queue).map atom)]⟩

def deliverCase (name : String) (head : String) (tail : List String) (box : Mailbox String) : Example :=
  ⟨name, node "ErChannelDeliver" [pid 1, pid 0, values ((head :: tail).map atom), mailbox atom box],
    node "ErChannelArrived" [pid 1, pid 0, atom head, values (tail.map atom),
      mailbox atom (box.deliver head)],
    node "ErChannelArrived" [pid 1, pid 0, atom head, values (tail.map atom), mailbox atom box]⟩

def examples : List Example := [
  sendCase "channel-empty-send" "a" [],
  sendCase "channel-append-order" "c" ["a", "b"],
  sendCase "channel-send-keeps-duplicates" "a" ["a", "a"],
  deliverCase "channel-deliver-head" "a" ["b"] ⟨[], [], []⟩,
  deliverCase "channel-deliver-keeps-duplicate" "a" ["a"] ⟨[], [], []⟩,
  deliverCase "channel-deliver-retains-scanned-prefix" "new" ["later"]
    ⟨["second", "first"], ["old"], ["in-flight-earlier"]⟩]

def verdicts : List (String × Option Bool × Option Bool) := examples.map fun sample =>
  (sample.name,
    GoldOSLF.verdict (GoldOSLF.ask language provider 2 20 (GoldOSLF.reaches sample.expected) sample.source),
    GoldOSLF.verdict (GoldOSLF.ask language provider 2 20 (GoldOSLF.reaches sample.wrong) sample.source))

#eval verdicts
#guard verdicts.length == 6
#guard verdicts.all fun entry => entry.2.1 == some true && entry.2.2 == some false

def emptyChannel : Pattern := node "ErChannelDeliver"
  [pid 1, pid 0, values [], mailbox atom (Mailbox.mk [] [] [])]

def noDelivery : Option Bool := GoldOSLF.verdict
  (GoldOSLF.ask language provider 2 2 (.possibly .any .top) emptyChannel)

/- An empty selected channel has no delivery step. This is deliberately not
a statement that another channel or process cannot move. -/
#guard noDelivery == some false

def fifoSource : Pattern := node "ErChannelDeliver"
  [pid 1, pid 0, values (["a", "b"].map atom), mailbox atom (Mailbox.mk [] [] [])]
def overtaken : Pattern := node "ErChannelArrived"
  [pid 1, pid 0, atom "b", values [atom "a"], mailbox atom (Mailbox.mk [] [] ["b"])]
def fifoViolation : Option Bool := GoldOSLF.verdict
  (GoldOSLF.ask language provider 2 3 (GoldOSLF.reaches overtaken) fifoSource)
#guard fifoViolation == some false

def exhausted : Option Bool :=
  let sample := examples[1]'(by decide)
  GoldOSLF.verdict (GoldOSLF.ask language provider 2 0 (GoldOSLF.reaches sample.expected) sample.source)
#guard exhausted == none

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel.Controls
