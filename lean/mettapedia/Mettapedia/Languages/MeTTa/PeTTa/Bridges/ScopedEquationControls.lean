import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairControls

/-! Named entry retains duplicate clauses, captured data and caller work.
Constrained outputs remain a reference boundary, not an eager effect. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Equations.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS.Destination
open SpaceSemantics
open ScopedQuerySource.Controls (call number self dangerous mark)

def echo : Equation := ⟨"echo", [.var "value"], .var "value"⟩
def program : Program := {equations := [⟨"unrelated", [], number 0⟩, echo, echo], declarations := []}
def older : List Goal := [.evaluate (call "quote" [.expression [.var "out", .var "caller"]]) (.var "answer")]
def control : Control := {
  bindings := [(.var "captured", dangerous), (.var "caller", .symbol "retained")]
  goals := .invoke "echo" [.var "captured"] (.var "out") :: older
  destination := .var "answer"
  cutBoundary := 7 }
def initial : ScopedCursor Unit :=
  (Allocator.empty 8 8, ⟨⟨NamedSpaces.Store.new [] [], [], []⟩, [⟨[(control, (), [8])], [], none⟩]⟩)
def selected := ClauseChoice.choices program
  (protectControl control (collectionSupport initial.2)) "echo" [dangerous] (.var "out") older

theorem complete_frontier : ClauseChoice.Frontier program
    (protectControl control (collectionSupport initial.2)) "echo" [dangerous] (.var "out") older
    (List.range program.equations.length) selected :=
  (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl

#guard selected.map Prod.fst == [1, 2]
#guard selected.length == 2
#guard selected.all (fun row => row.2.destination == control.destination)
#guard selected.all (fun row => (predicateEntry 0 row.2).goals.drop 1 == .restoreCommit 7 :: older)

def result := (machine .relational program).run 40 initial
#guard result.1.map CollectedAnswer.value ==
  List.replicate 2 (.expression [dangerous, .symbol "retained"])
#guard result.1.map CollectedAnswer.occurrences == [[8, 1], [8, 2]]
#guard (EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some []

-- A bound result is not silently admitted through the unconstrained theorem.
def constrained : ScopedCursor Unit :=
  (initial.1, ⟨initial.2.world, [⟨[({control with
    bindings := control.bindings ++ [(.var "out", .symbol "not-the-payload")]}, (), [8])], [], none⟩]⟩)
def retained : Bool := match (machine .relational program).run 40 constrained with
  | ([], .suspended (.branch (.invoke "echo" _ _)) saved) =>
      saved.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1.bindings)) ==
        constrained.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1.bindings)) &&
      saved.2.world.state.read .self == some []
  | _ => false
#guard retained

namespace NamedGuard

open GuardedInsertionPairSource.Controls.SeparateSpaces (request)
def guard : Equation := NamedPresenceSource.declaration request
def program : Program := {equations := [guard], declarations := []}
def caller : Control := {
  bindings := [(.var "tag", number 1), (.var "node", number 7)]
  goals := [.invoke "in" [.var "tag", .var "node"] (.var "out"),
    .evaluate (call "quote" [.expression [.var "out", .var "node"]]) (.var "answer")]
  destination := .var "answer" }
def execute (state : Effects.State) (capacity : Nat := 8) :=
  (machine .relational program).run 100
    (Allocator.empty capacity 8, ⟨⟨state, [], []⟩,
      [(⟨[(caller, (), [4])], [], none⟩ : CollectionScope Unit)]⟩)

#guard (execute GuardedInsertionPairSource.Controls.SeparateSpaces.initial).1.map CollectedAnswer.value ==
  [.expression [Effects.boolean false, number 7]]
#guard (execute GuardedInsertionPairSource.Controls.SeparateSpaces.held).1.map CollectedAnswer.value ==
  [.expression [Effects.boolean true, number 7]]

def refused : Bool := match (execute GuardedInsertionPairSource.Controls.SeparateSpaces.held 0).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard refused
#guard (execute GuardedInsertionPairSource.Controls.SeparateSpaces.initial 0).1.map CollectedAnswer.value ==
  [.expression [Effects.boolean false, number 7]]

end NamedGuard

#print axioms enter
#print axioms selected_body
#print axioms NamedPresenceSource.call_prefix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Equations.Controls
