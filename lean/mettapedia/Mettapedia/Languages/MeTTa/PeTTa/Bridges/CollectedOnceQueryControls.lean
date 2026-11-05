import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution

/-! Source-level controls retain inherited bindings and distinguish a copied
singleton, an empty collection, refusal, duplicates and a paused caller. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def rows : List Atom := [ClosedOnceQueryExecution.pattern "sat" 1 7,
  ClosedOnceQueryExecution.pattern "sat" 1 7, ClosedOnceQueryExecution.pattern "sat" 1 8]

def tagged (node : Int) : LiteralQuerySource.Request :=
  ⟨.self, ClosedOnceQueryExecution.pattern "sat" 1 node,
    ClosedOnceQueryExecution.pattern_literal "sat" 1 node (by decide), Effects.boolean true, .grounded (.bool true), rfl⟩

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def nested (node : Int) : Atom := call "let" [.var "saved", .symbol "kept",
  call "let" [.var "packet", source (tagged node),
    call "Pair" [.var "saved", .var "packet"]]]

def loaded (capacity : Nat) (expression : Atom) :=
  loadScoped? (Allocator.empty capacity 8) rows [] []
    {bindings := [], goals := [.evaluate expression (.var "answer")], destination := .var "answer"} []

def execute (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (loaded capacity expression).map fun initial =>
    (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel initial

def answers (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).map fun result => result.1.map CollectedAnswer.value

def completed (capacity : Nat) (expression : Atom) :=
  (execute capacity expression).map fun result => match result.2 with
    | .finished _ => true | _ => false

def allocationBlocked (capacity : Nat) (expression : Atom) :=
  (execute capacity expression).map fun result => match result.2 with
    | .suspended .allocation _ => true | _ => false

def heldCopies (capacity : Nat) (expression : Atom) :=
  (execute capacity expression).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).map fun saved =>
      saved.1.cells.toList.countP (fun cell => 0 < cell.owners)

#guard answers 8 (nested 7) == some [call "Pair" [.symbol "kept", .expression [Effects.boolean true]]]
#guard completed 8 (nested 7) == some true
#guard answers 8 (nested 9) == some [call "Pair" [.symbol "kept", .expression []]]
#guard heldCopies 8 (source (tagged 7)) == some 2
#guard heldCopies 8 (source (tagged 9)) == some 1

/- Loading owns the only available identity. A positive collection needs a
second one; its request must not be replaced by an invented tuple. -/
#guard allocationBlocked 1 (source (tagged 7)) == some true
#guard answers 1 (source (tagged 7)) == some []
#guard completed 1 (source (tagged 9)) == some true
#guard answers 1 (source (tagged 9)) == some [.expression []]

def withoutOnce : Atom := call "collapse" [ClosedOnceQueryExecution.query "sat" 1 7]
#guard answers 8 withoutOnce == some [.expression [Effects.boolean true, Effects.boolean true]]
#guard heldCopies 8 withoutOnce == some 3

def before (body : Atom) : Atom := call "let" [.var "ignored", call "println!" [.symbol "prefix"], body]
def printed (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).map fun saved => saved.2.world.output

#guard printed 8 (before (nested 7)) == some [.symbol "prefix"]
#guard allocationBlocked 1 (before (source (tagged 7))) == some true
#guard printed 1 (before (source (tagged 7))) == some [.symbol "prefix"]

def paused := (execute 8 (before (nested 7)) 12).bind fun result =>
  EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 saved

#guard answers 8 (before (nested 7)) 12 == some []
#guard paused.map (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) ==
  some [call "Pair" [.symbol "kept", .expression [Effects.boolean true]]]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "prefix"]

/-- A caller's incompatible result constraint is not erased to make a
positive child query succeed. -/
def conflicting : Atom := call "let" [.var "packet", .expression [],
  call "let" [.var "packet", source (tagged 7), .var "packet"]]
#guard answers 8 conflicting == some []
#guard completed 8 conflicting == some true

def deep : Atom := call "tree" [call "leaf" [.grounded (.int (-7))],
  .expression [.grounded (.string "payload"), Effects.boolean false, .expression []]]

def deepRequest (handle : NamedSpaces.Handle) : LiteralQuerySource.Request :=
  ⟨handle, deep, (LiteralQuerySource.checkLiteral_iff deep).mp (by decide +kernel), Effects.boolean true, .grounded (.bool true), rfl⟩

def privateState : Effects.State :=
  ((NamedSpaces.Store.new [Atom.symbol "outside"] []).allocate [deep, deep]).2

def queryControl (request : LiteralQuerySource.Request) : Control where
  bindings := [(.var "saved", .symbol "kept")]
  goals := [.evaluate (source request) (.var "answer")]
  destination := .var "answer"

def sourceIn (state : Effects.State) (request : LiteralQuerySource.Request) : ScopedCursor Unit :=
  (Allocator.empty 8 8, ⟨⟨state, [], [.symbol "already-emitted"]⟩,
    [{frontier := [(queryControl request, (), [4])]}]⟩)

def runIn (state : Effects.State) (request : LiteralQuerySource.Request) :=
  (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 30 (sourceIn state request)

def valuesIn (state : Effects.State) (request : LiteralQuerySource.Request) :=
  (runIn state request).1.map CollectedAnswer.value

#guard valuesIn privateState (deepRequest (.privateSpace 0)) == [.expression [Effects.boolean true]]
#guard valuesIn privateState (deepRequest .self) == [.expression []]
#guard (EagerDFSStreaming.Scoped.readback (runIn privateState (deepRequest (.privateSpace 0))).2).map
  (fun saved => saved.2.world.output) == some [.symbol "already-emitted"]
#guard (LiteralQuerySource.prepareRead (deepRequest (.privateSpace 0)) privateState).isSome
#guard (LiteralQuerySource.prepareRead (deepRequest (.privateSpace 1)) privateState).isNone

def missingIsFault : Bool :=
  match (runIn privateState (deepRequest (.privateSpace 1))).2 with
  | .suspended (.fault .invalidSpace) _ => true
  | _ => false
#guard missingIsFault
#guard valuesIn privateState (deepRequest (.privateSpace 1)) == []

def openState : Effects.State := NamedSpaces.Store.new [call "tree" [.var "unknown"]] []
#guard (LiteralQuerySource.prepareRead (deepRequest .self) openState).isNone

def unrelatedOpen : Effects.State := NamedSpaces.Store.new [deep, call "=" [.var "x", .var "y"]] []
#guard (LiteralQuerySource.prepareRead (deepRequest .self) unrelatedOpen).isSome

#guard (LiteralQuerySource.parse (LiteralQuerySource.expression (deepRequest (.privateSpace 0)))).map
  LiteralQuerySource.Request.pattern == some deep
#guard (LiteralQuerySource.parse (LiteralQuerySource.expression (deepRequest (.privateSpace 0)))).map
  LiteralQuerySource.Request.handle == some (.privateSpace 0)
#guard (LiteralQuerySource.ofPattern .self (.symbol "leaf")).isSome
#guard (LiteralQuerySource.ofPattern .self (.grounded (.int 42))).isSome
#guard (LiteralQuerySource.ofPattern .self (.expression [])).isSome
#guard (LiteralQuerySource.ofPattern .self (call "tree" [call "cons" [.symbol "a", .expression []]])).isNone
#guard (LiteralQuerySource.ofPattern .self (call "tree" [.var "x"])).isNone
#guard (LiteralQuerySource.parse (call "once" [call "match"
  [.grounded (.custom "PeTTa.Space" "not-a-handle"), deep, Effects.boolean true]])).isNone
#guard (LiteralQuerySource.parse (call "once" [call "match"
  [call "space-expression" [], deep, Effects.boolean true]])).isNone
#guard (LiteralQuerySource.parse (call "once" [call "match"
  [.symbol "&self", deep, Effects.boolean false]])).map LiteralQuerySource.Request.payload == some (Effects.boolean false)

def taggedPayload (node : Int) (payload : Atom) (scalar : ConstantQuerySource.Scalar payload) : LiteralQuerySource.Request :=
  {tagged node with payload, scalar}

#guard answers 8 (source (taggedPayload 7 (.symbol "t") (.symbol "t"))) == some [.expression [.symbol "t"]]
#guard answers 8 (source (taggedPayload 7 (Effects.boolean false) (.grounded (.bool false)))) ==
  some [.expression [Effects.boolean false]]
#guard (LiteralQuerySource.parse (call "once" [call "match" [.symbol "&self", deep, .var "answer"]])).isNone
#guard (LiteralQuerySource.parse (call "once" [call "match"
  [.symbol "&self", deep, call "println!" [.symbol "effect"]]])).isNone
#guard (LiteralQuerySource.ofPattern .self (call "," []) (.symbol "t")).isNone
#guard (LiteralQuerySource.ofPattern .self (call "," [call "a" [], call "b" []]) (.symbol "t")).isNone
#guard (LiteralQuerySource.ofPattern .self (call "data" [call "," []]) (.symbol "t")).isSome

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource.Controls
