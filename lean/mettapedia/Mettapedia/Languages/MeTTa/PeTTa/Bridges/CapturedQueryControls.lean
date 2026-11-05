import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardControls

/-! Captured operands, genuine refusal, caller-page work and served operand
effects are checked independently of a particular root query spelling. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open CapturedQueryOperands
open CollectedOnceQuerySource.Controls (program call)

def arguments : Arguments :=
  ⟨.var "location", call "sat" [.var "formula", .var "node"], .var "payload"⟩

def bindings : Equations :=
  [(.var "location", .symbol "&self"), (.var "formula", .grounded (.int 1)),
   (.var "node", .grounded (.int 7)), (.var "payload", .symbol "t")]

def described := (capture bindings arguments).map fun captured =>
  (captured.request.handle, captured.request.pattern, captured.request.payload)

#guard described == some (.self, call "sat" [.grounded (.int 1), .grounded (.int 7)], .symbol "t")
#guard (capture [] arguments).isNone
#guard (capture [(.var "x", .symbol "a"), (.var "x", .symbol "b")] arguments).isNone

def aliasArguments : Arguments := ⟨.symbol "&self", call "pair" [.var "x", .var "x"], .symbol "t"⟩
#guard (capture [(.var "x", .var "y"), (.var "y", .grounded (.int 7))] aliasArguments).map
  (fun captured => captured.request.pattern) == some (call "pair" [.grounded (.int 7), .grounded (.int 7)])
#guard (capture [(.var "x", .var "y")] aliasArguments).isNone

def extended := (capture bindings arguments).bind fun captured =>
  (captured.extend [(.var "unrelated", .grounded (.int 42))]).map fun next => next.request.pattern
def contradictory := (capture bindings arguments).bind fun captured => captured.extend [(.var "node", .grounded (.int 8))]
#guard extended == some (call "sat" [.grounded (.int 1), .grounded (.int 7)])
#guard contradictory.isNone
#guard (capture [] ⟨call "println!" [.symbol "not-served"], .symbol "row", .symbol "t"⟩).isNone
#guard (capture [(.var "p", call "," [])] ⟨.symbol "&self", .var "p", .symbol "t"⟩).isNone

def row (node : Int) : Atom := call "sat" [.grounded (.int 1), .grounded (.int node)]

def control : Control where
  bindings := bindings
  goals := [.invoke "match" arguments.atoms (.var "answer"), .commit, .restoreCommit 0]
  destination := .var "answer"

def initial (rows : List Atom) (selected : Control := control)
    (pending : List (CollectionWork Unit) := []) : ScopedCursor Unit :=
  (Allocator.empty 8 8, ⟨⟨NamedSpaces.Store.new rows [], [], [.symbol "earlier"]⟩,
    [{frontier := (selected, (), []) :: pending}]⟩)

def late := initial [row 8, row 7, row 7]
def events (probeBudget : Nat) (input : ScopedCursor Unit) :=
  ((region (0 : Nat) program probeBudget).execute input).1.map CollectedAnswer.value
def accepted (probeBudget : Nat) (input : ScopedCursor Unit) := (checked program probeBudget input).isSome

#guard !(accepted 0 late)
#guard !(accepted 1 late)
#guard accepted 2 late
#guard events 1 late == [.symbol "t"]
#guard events 2 late == [.symbol "t"]

def openRows := initial [call "sat" [.grounded (.int 1), .var "open"]]
#guard !(accepted 8 openRows)

def conflict : ScopedCursor Unit := initial [row 7]
  {control with bindings := bindings ++ [(.var "answer", .symbol "other")]}
#guard !(accepted 8 conflict)
#guard events 8 conflict == []

def invalidBoundary := initial [row 7] {control with cutBoundary := 1}
#guard !(accepted 8 invalidBoundary)

def outside (name : String) : CollectionWork Unit :=
  ({bindings := [], goals := [], destination := .symbol name}, (), [])
def delimited := initial [row 7] {control with cutBoundary := 1} [outside "inside", outside "kept"]
def kept := (EagerDFSStreaming.Scoped.readback ((region (0 : Nat) program 8).execute delimited).2).map
  fun saved => saved.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1.destination))
#guard events 8 delimited == [.symbol "t"]
#guard kept == some [[.symbol "kept"]]

def printAfterMiss : CollectionWork Unit :=
  ({bindings := [], goals := [.invoke "println!" [.symbol "after-miss"] (.var "answer")], destination := .var "answer"}, (), [])
def miss := initial [] {control with cutBoundary := 1} [printAfterMiss]
def missOutput := (EagerDFSStreaming.Scoped.readback ((region (0 : Nat) program 1).execute miss).2).map
  fun saved => saved.2.world.output
#guard accepted 1 miss
#guard events 1 miss == [Effects.boolean true]
#guard missOutput == some [.symbol "earlier", .symbol "after-miss"]

def missingSpace := initial [row 7] {control with bindings :=
  (.var "location", Effects.handleValue (.privateSpace 0)) :: bindings.tail}
#guard !(accepted 8 missingSpace)

def dynamicGuard : Atom := call "let" [.var "formula", .grounded (.int 1),
  call "let" [.var "node", .grounded (.int 7),
  call "let" [.var "payload", .symbol "t",
  call "not" [call "==" [call "collapse" [call "once" [call "match"
    [call "let" [.var "ignored", call "println!" [.symbol "prefix"], .symbol "&self"],
     call "sat" [.var "formula", .var "node"], .var "payload"]]], .expression []]]]]]

def findAdmitted {Context : Type} : Nat → ScopedCursor Context → Option (ScopedCursor Context)
  | 0, _ => none
  | fuel + 1, source =>
      if (checked program 8 source).isSome then some source else
        match ((EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 1 source).2 with
        | .exhausted next => findAdmitted fuel next
        | _ => none

def reached := (CollectedOnceQuerySource.Controls.loaded 8 dynamicGuard).bind (findAdmitted 100)
def optimized := reached.map fun source => (region (0 : Nat) program 8).execute source
def resumed := (optimized.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map fun source =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 source

#guard reached.isSome
#guard reached.map (fun source => source.2.world.output) == some [.symbol "prefix"]
#guard optimized.map (fun result => result.1.map CollectedAnswer.value) == some []
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun source => source.2.world.output) == some [.symbol "prefix"]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion.Controls
