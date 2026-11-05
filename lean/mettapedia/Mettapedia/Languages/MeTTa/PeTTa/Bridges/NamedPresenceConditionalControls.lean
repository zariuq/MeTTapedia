import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedControls

/-! Executable admission and actual named conditional runs, including cut
restoration, duplicate definitions, retained callers and allocation refusal. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number)

def request := CTLUntilPublicationSource.request FlatQueryRowCodec.integers .self 10 1
def caller : Control := {
  bindings := [(.var "f", number 10), (.var "x", number 1), (.var "kept", number 9)]
  goals := [.evaluate (call "quote" [.expression [.var "branch-result", .var "kept"]]) (.var "answer")]
  destination := .var "answer"
  cutBoundary := 0 }
def later : Control := {bindings := [], goals := [.evaluate (.symbol "later") (.var "later-answer")], destination := .var "later-answer"}
def base : Input Unit := {
  program := {equations := [NamedPresenceSource.declaration request], declarations := []}
  allocator := Allocator.empty 16 8
  world := ⟨NamedSpaces.Store.new CTLUntilMixedStore.Controls.atoms [], [], []⟩
  scope := ⟨[], [], none⟩
  parents := []
  caller, context := (), origins := [4], pending := [(later, (), [88])]
  destination := .var "branch-result"
  formulaName := "f", nodeName := "x"
  yes := call "quote" [.symbol "held"]
  no := call "cut" []
  request }

#guard (prepare base).isSome

def execute (input : Input Unit) (fuel : Nat := 200) :=
  (ScopedQuerySource.machine .relational input.program).run fuel input.before
def firstControl (input : Input Unit) (fuel : Nat) :=
  ((EagerDFSStreaming.Scoped.readback (execute input fuel).2).bind fun saved => saved.2.scopes.head?).bind
    (fun scope => scope.frontier.head?.map (fun work => work.1))

-- The conditional has selected, but not yet executed, its authored branch.
#guard (execute base 26).1.isEmpty
#guard (firstControl base 26).map (fun control => control.goals.head?) == some (some (.evaluate base.no base.destination))
#guard (firstControl base 26).map Control.cutBoundary == some 0
-- The caller's cut floor is restored: its cut removes the saved sibling.
#guard (execute base).1.map CollectedAnswer.value == [.expression [Effects.boolean true, number 9]]

def held : Input Unit := {base with world := ⟨NamedSpaces.Store.new
  (CTLUntilMixedStore.Controls.atoms ++ [request.pattern, request.pattern]) [], [], []⟩}
#guard (prepare held).isSome
#guard (execute held 30).1.isEmpty
#guard (firstControl held 30).map (fun control => control.goals.head?) == some (some (.evaluate held.yes held.destination))
#guard (execute held).1.map CollectedAnswer.value == [.expression [.symbol "held", number 9], .symbol "later"]

def noCapacity : Input Unit := {held with allocator := Allocator.empty 0 8}
def copyRefused : Bool := match (execute noCapacity 30).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard (prepare noCapacity).isSome
#guard copyRefused
#guard (execute noCapacity 30).1.isEmpty

def duplicated : Input Unit := {held with program := {held.program with
  equations := [NamedPresenceSource.declaration request, NamedPresenceSource.declaration request]}}
#guard (prepare duplicated).map (fun certificate => certificate.alternatives.length) == some 1
#guard (execute duplicated).1.map CollectedAnswer.value ==
  [.expression [.symbol "held", number 9], .expression [.symbol "held", number 9], .symbol "later"]

def wrongRequest : Input Unit := {base with request := CTLUntilPublicationSource.request FlatQueryRowCodec.integers .self 11 1}
#guard (prepare wrongRequest).isNone
def wrongBody : Input Unit := {base with program := {base.program with equations := [⟨"in", [.var "f", .var "x"], .symbol "invented"⟩]}}
#guard (prepare wrongBody).isNone

def noncanonicalFirst : Input Unit := {held with
  no := call "quote" [.symbol "not-held"]
  program := {held.program with equations :=
    [⟨"in", [.var "f", .var "x"], .symbol "invented"⟩, NamedPresenceSource.declaration request]}}
#guard (prepare noncanonicalFirst).isNone
#guard (execute noncanonicalFirst).1.map CollectedAnswer.value ==
  [.expression [.symbol "not-held", number 9], .expression [.symbol "held", number 9], .symbol "later"]

def rawArguments : Input Unit := {base with program := {base.program with declarations :=
  [call ":" [.symbol "in", call "->" [.symbol "Atom", .symbol "Atom", .symbol "Bool"]]]}}
#guard Eval.argumentIsRaw rawArguments.program "in" 0
#guard Eval.argumentIsRaw rawArguments.program "in" 1
#guard (prepare rawArguments).isNone
#guard (execute rawArguments).1.map CollectedAnswer.value == (execute base).1.map CollectedAnswer.value

def renamed : Input Unit := {base with
  caller := {caller with bindings := [(.var "formula-captured", number 10), (.var "node-captured", number 1), (.var "kept", number 9)]}
  formulaName := "formula-captured", nodeName := "node-captured"}
#guard (prepare renamed).isSome
#guard (execute renamed).1.map CollectedAnswer.value == (execute base).1.map CollectedAnswer.value

#print axioms ScopedCallOperands.preparation
#print axioms NamedPresenceSource.return_to_branch
#print axioms source_prefix
#print axioms NamedPresenceAdmission.evidence_constructed
#print axioms NamedPresenceAdmission.prepare_canonical

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional.Controls
