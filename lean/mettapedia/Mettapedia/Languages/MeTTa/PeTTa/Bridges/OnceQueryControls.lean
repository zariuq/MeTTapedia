import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource

/-! Executable scoped-source controls complement the generic cursor and
primitive-prefix proofs. The query body is literal data; no equivalence with
arbitrary effectful match bodies or a native runtime is inferred. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS.Destination
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def quote (value : Atom) : Atom := call "quote" [value]
def choice (values : List Atom) : Atom := call "superpose" [.expression values]
def once (value : Atom) : Atom := call "once" [value]
def row (state : Int) : Atom := call "sat" [.grounded (.int 1), .grounded (.int state)]
def rows : List Atom := [row 7, row 7, row 8]
def query (state : Int) : Atom := call "match" [.symbol "&self", row state, Effects.boolean true]
def program : SpaceSemantics.Program := {equations := [], declarations := []}

def loaded (expression : Atom) :=
  loadScoped? (Allocator.empty 16 8) rows [] []
    {bindings := [], goals := [.evaluate expression (.var "answer")], destination := .var "answer"} []

def execute (expression : Atom) (fuel : Nat := 120) :=
  (loaded expression).map fun source =>
    (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel source

def answers (expression : Atom) := (execute expression).map fun result => result.1.map CollectedAnswer.value
def completed (expression : Atom) := (execute expression).map fun result => match result.2 with
  | .finished _ => true | _ => false
def printed (expression : Atom) :=
  (execute expression).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).map fun saved => saved.2.world.output

#guard answers (query 7) == some [Effects.boolean true, Effects.boolean true]
#guard answers (once (query 7)) == some [Effects.boolean true]
#guard completed (once (query 7)) == some true
#guard answers (once (query 9)) == some []
#guard completed (once (query 9)) == some true
#guard answers (call "collapse" [once (query 7)]) == some [.expression [Effects.boolean true]]
#guard answers (call "collapse" [once (query 9)]) == some [.expression []]

def outside : Atom := .symbol "outside"
#guard answers (choice [once (query 7), quote outside]) == some [Effects.boolean true, outside]
#guard answers (choice [once (query 9), quote outside]) == some [outside]

def forbiddenTail : Atom := call "let" [.var "ignored", call "println!" [.symbol "forbidden"], quote outside]
def beforeOnce : Atom := call "let" [.var "ignored", call "println!" [.symbol "prefix"],
  once (choice [query 7, forbiddenTail])]

#guard answers beforeOnce == some [Effects.boolean true]
#guard printed beforeOnce == some [.symbol "prefix"]
#guard completed beforeOnce == some true

def collectThenFirst : Atom := call "index-atom"
  [call "collapse" [choice [query 7, forbiddenTail]], .grounded (.int 0)]
#guard answers collectThenFirst == some [Effects.boolean true]
#guard printed collectThenFirst == some [.symbol "forbidden"]

def paused := (execute beforeOnce 8).bind fun result => EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 saved

#guard (execute beforeOnce 8).map (fun result => match result.2 with | .exhausted _ => true | _ => false) == some true
#guard paused.map (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "prefix"]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource.Controls
