import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQueryControls

/-! Source guards distinguish false from no answers, keep the source copy
boundary, and preserve outer alternatives and preceding effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open CollectedOnceQuerySource.Controls (program call tagged taggedPayload loaded before)

def execute (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (loaded capacity expression).map fun initial =>
    (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel initial

def answers (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).map fun result => result.1.map CollectedAnswer.value

def done (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).map fun result => match result.2 with
    | .finished _ => true | _ => false

def allocated (capacity : Nat) (expression : Atom) :=
  (execute capacity expression).map fun result => match result.2 with
    | .suspended .allocation _ => true | _ => false

def nested (node : Int) : Atom := call "let" [.var "saved", .symbol "kept",
  call "Pair" [.var "saved", source (tagged node)]]

#guard answers 8 (source (tagged 7)) == some [Effects.boolean true]
#guard answers 8 (source (tagged 9)) == some [Effects.boolean false]
#guard answers 8 (nested 7) == some [call "Pair" [.symbol "kept", Effects.boolean true]]
#guard answers 8 (nested 9) == some [call "Pair" [.symbol "kept", Effects.boolean false]]
#guard answers 8 (source (tagged 7)) 20 == some []
#guard done 8 (source (tagged 7)) 20 == some false
#guard answers 8 (source (tagged 7)) 22 == some [Effects.boolean true]
#guard done 8 (source (tagged 7)) 22 == some false
#guard done 8 (source (tagged 7)) 23 == some true
#guard done 8 (source (tagged 9)) 19 == some true
#guard allocated 1 (source (tagged 7)) == some true
#guard answers 1 (source (tagged 7)) == some []
#guard answers 1 (source (tagged 9)) == some [Effects.boolean false]

def choice (first second : Atom) := call "superpose" [.expression [first, second]]
#guard answers 8 (choice (source (tagged 7)) (call "quote" [.symbol "outside"])) ==
  some [Effects.boolean true, .symbol "outside"]
#guard answers 8 (choice (source (tagged 9)) (call "quote" [.symbol "outside"])) ==
  some [Effects.boolean false, .symbol "outside"]

def paused := (execute 8 (before (source (tagged 7))) 12).bind fun result =>
  EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 saved

#guard paused.map (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "prefix"]

def conflict : Atom := call "let" [.var "answer", Effects.boolean false,
  call "let" [.var "answer", source (tagged 7), .var "answer"]]
#guard answers 8 conflict == some []
#guard done 8 conflict == some true

#guard answers 8 (source (taggedPayload 7 (.symbol "t") (.symbol "t"))) == some [Effects.boolean true]
#guard answers 8 (source (taggedPayload 9 (.symbol "t") (.symbol "t"))) == some [Effects.boolean false]
#guard answers 8 (source (taggedPayload 7 (Effects.boolean false) (.grounded (.bool false)))) == some [Effects.boolean true]
#guard answers 8 (source (taggedPayload 7 (.grounded (.int 42)) (.grounded (.int 42)))) == some [Effects.boolean true]
#guard allocated 1 (source (taggedPayload 7 (.symbol "t") (.symbol "t"))) == some true

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource.Controls
