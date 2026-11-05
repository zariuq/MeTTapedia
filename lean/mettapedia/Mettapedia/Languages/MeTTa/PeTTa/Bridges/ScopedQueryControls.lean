import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

/-! Effectful query bodies, captured choices, alias visibility, inert values,
unserved open facts and finite-budget execution. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open SpaceSemantics

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def number (n : Int) : Atom := .grounded (.int n)

#print equations call
#print equations number

def self : Atom := .symbol "&self"
def row (n : Int) : Atom := call "row" [number n]
def mark (n : Int) : Atom := call "mark" [number n]
def program : Program := {equations := [], declarations := []}

def loaded (rows : List Atom) (expression : Atom) :=
  loadScoped? (Allocator.empty 64 16) rows [] []
    {bindings := [], goals := [.evaluate expression (.var "answer")], destination := .var "answer"} []

def execute (program : Program) (rows : List Atom) (expression : Atom) (fuel : Nat := 500) :=
  (loaded rows expression).map fun initial => (machine .relational program).run fuel initial

def answers (program : Program) (rows : List Atom) (expression : Atom) (fuel : Nat := 500) :=
  (execute program rows expression fuel).map fun result => result.1.map CollectedAnswer.value

def finalRows (program : Program) (rows : List Atom) (expression : Atom) (fuel : Nat := 500) :=
  (execute program rows expression fuel).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).bind fun saved => saved.2.world.state.read .self

def copying : Atom := call "match" [self, call "row" [.var "x"], call "add-atom" [self, call "mark" [.var "x"]]]
#guard answers program [row 7, row 7, row 8] copying == some (List.replicate 3 (Effects.boolean true))
#guard finalRows program [row 7, row 7, row 8] copying == some [row 7, row 7, row 8, mark 7, mark 7, mark 8]

-- New rows are visible later, but do not feed back into this captured match.
def selfInsertion : Atom := call "match" [self, call "row" [.var "x"], call "add-atom" [self, call "row" [.var "x"]]]
#guard answers program [row 7, row 8] selfInsertion == some (List.replicate 2 (Effects.boolean true))
#guard finalRows program [row 7, row 8] selfInsertion == some [row 7, row 8, row 7, row 8]

def presence (pattern : Atom) : Atom := call "not"
  [call "==" [call "collapse" [call "once" [call "match" [self, pattern, .symbol "t"]]], .expression []]]
def freshBody : Atom := call "if" [presence (call "mark" [.var "x"]), call "empty" [],
  call "add-atom" [self, call "mark" [.var "x"]]]
def freshCopy : Atom := call "match" [self, call "row" [.var "x"], freshBody]
#guard answers program [row 7, row 7, row 8] freshCopy == some (List.replicate 2 (Effects.boolean true))
#guard finalRows program [row 7, row 7, row 8] freshCopy == some [row 7, row 7, row 8, mark 7, mark 8]

-- Returning a variable does not execute its already captured value.
def dangerous : Atom := call "add-atom" [self, mark 99]
def retrieve : Atom := call "match" [self, call "payload" [.var "x"], .var "x"]
#guard answers program [call "payload" [dangerous]] retrieve == some [dangerous]
#guard finalRows program [call "payload" [dangerous]] retrieve == some [call "payload" [dangerous]]

def supportedCons : Atom := call "match" [self, call "cons" [.symbol "row", .var "tail"], .var "tail"]
#guard answers program [row 7, row 8] supportedCons == some [.expression [number 7], .expression [number 8]]

def incompatible : Atom := call "let" [.var "x", number 9,
  call "match" [self, call "row" [.var "x"], call "add-atom" [self, mark 99]]]
#guard answers program [row 7] incompatible == some []
#guard finalRows program [row 7] incompatible == some [row 7]

def openRow : Atom := call "row" [.var "stored"]
def literalPresence : Atom := presence (row 7)
def awaitingQuery (expression : Atom) : Bool :=
  match execute program [openRow] expression with
  | some (_, .suspended (.branch (.invoke "match" _ _)) _) => true
  | _ => false
#guard awaitingQuery copying
#guard awaitingQuery literalPresence

def precedingEffect : Atom := call "match"
  [call "let" [.var "ignored", call "add-atom" [self, mark 99], self], call "row" [.var "x"], .var "x"]
#guard awaitingQuery precedingEffect
#guard finalRows program [openRow] precedingEffect ==
  ((loaded [openRow] precedingEffect).bind fun source => source.2.world.state.read .self).map
    (fun enteredRows => enteredRows ++ [mark 99])

def paused := (execute program [row 7, row 7, row 8] copying 18).bind fun result =>
  EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved => (machine .relational program).run 500 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some [row 7, row 7, row 8, mark 7, mark 7, mark 8]

def looping : Program := {program with equations := [⟨"loop", [], call "loop" []⟩]}
def queryLoop : Atom := call "match" [self, call "row" [.var "x"], call "loop" []]
def boundedLoop : Bool :=
  match execute looping [row 7] queryLoop 30 with
  | some ([], .exhausted _) => true
  | _ => false
#guard boundedLoop

def escapedBinding : Atom := call "let" [.var "result",
  call "match" [self, call "row" [.var "x"], call "quote" [.symbol "ok"]],
  call "quote" [.expression [.var "result", .var "x"]]]
#guard answers program [row 7, row 8] escapedBinding ==
  some [.expression [.symbol "ok", number 7], .expression [.symbol "ok", number 8]]

-- Pinned PeTTa checks the primitive's result head before its mutation.
-- This profile hands the constrained call back instead of using eager effects.
def constrainedInsertion : Atom := call "let" [Effects.boolean false,
  call "add-atom" [self, mark 99], .symbol "impossible"]
def constrainedIsRetained : Bool :=
  match execute program [] constrainedInsertion with
  | some ([], .suspended (.branch (.invoke "add-atom" _ _)) _) => true
  | _ => false
#guard constrainedIsRetained
#guard finalRows program [] constrainedInsertion == some []

def referenceMutation (expression : Atom) (head : String) : Bool :=
  match execute program [] expression with
  | some ([], .suspended (.branch (.invoke requested _ _)) _) => requested == head
  | _ => false
#guard referenceMutation (call "add-atom" [self, call "=" [call "new-code" [], number 7]]) "add-atom"
#guard referenceMutation (call "add-atom" [self, call "row" [.var "unbound"]]) "add-atom"
#guard referenceMutation (call "remove-atom" [self, .symbol "primitive-row"]) "remove-atom"
#guard finalRows program [] (call "add-atom" [self, call "=" [call "new-code" [], number 7]]) == some []

def malformedSequence : Atom := call "let*" [.expression [.symbol "not-a-binding"], .symbol "unused"]
def malformedIsRetained : Bool :=
  match execute program [] malformedSequence with
  | some ([], .suspended (.branch (.invoke "let*" _ _)) _) => true
  | _ => false
#guard malformedIsRetained
#guard answers program [] (call "quote" [malformedSequence]) == some [malformedSequence]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Controls
