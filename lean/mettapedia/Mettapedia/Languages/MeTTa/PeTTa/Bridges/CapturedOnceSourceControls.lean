import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedCollectedOnceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls

/-! Captured pattern source entry, principal support and unchanged refusals. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number program)

def request (n : Int) : LiteralQuerySource.Request :=
  ⟨.self, ClosedOnceQueryExecution.pattern "sat" 1 n,
    ClosedOnceQueryExecution.pattern_literal "sat" 1 n (by decide), .symbol "t", .symbol "t", rfl⟩
def raw : Atom := call "sat" [.var "tag", .var "captured_node_name"]
def frame (n : Int) : ClosedOnceQueryFrame.Frame :=
  ⟨[(.var "tag", number 1), (.var "captured_node_name", number n)], "answer", ∅, 0⟩
def rows : List Atom := [(request 7).pattern, (request 7).pattern, (request 8).pattern]

def execute (context : ClosedOnceQueryFrame.Frame) (facts : List Atom) (fuel : Nat := 80) :=
  (ScopedQuerySource.machine .relational program).run fuel
    (ClosedOnceQueryFrame.placed (Allocator.empty 8 8) ⟨NamedSpaces.Store.new facts [], [], []⟩
      (⟨[], [], none⟩ : CollectionScope Unit) [] (initial context (request 7) raw) () [4] [])

-- The same authored query executes under different incoming variable frames.
theorem same_code_different_capture : source (request 7) raw = source (request 9) raw := rfl
#guard (execute (frame 7) rows).1.map CollectedAnswer.value == [.symbol "t"]
#guard (execute (frame 9) rows).1.map CollectedAnswer.value == []

def aliased : ClosedOnceQueryFrame.Frame :=
  {(frame 7) with bindings := [(.var "tag", number 1),
    (.var "captured_node_name", .var "shared"), (.var "shared", number 7)]}
#guard (execute aliased rows).1.map CollectedAnswer.value == [.symbol "t"]

def openFacts : List Atom := [(request 7).pattern, call "sat" [number 1, .var "stored"]]
def retainedRaw : Bool := match (execute (frame 7) openFacts).2 with
  | .suspended (.branch (.invoke "match" [_, patternCode, _] _)) _ => patternCode == raw
  | _ => false
#guard retainedRaw

-- Keeping the reached equations keeps allocation support; erasing them does not.
theorem retained_bindings_keep_location :
    location (frame 7) (request 7) raw 0 = location (frame 7) (request 7) (request 7).pattern 0 := by decide +kernel
theorem erasing_bindings_changes_location :
    location (frame 7) (request 7) raw 0 ≠
      location {(frame 7) with bindings := []} (request 7) (request 7).pattern 0 := by decide +kernel

def invented : Environment := fun name =>
  if name = "tag" then encode (number 1)
  else if name = "captured_node_name" then encode (number 7)
  else .var name

theorem arbitrary_model_is_not_a_principal_certificate :
    Solves invented [] ∧ read invented raw = (request 7).pattern ∧
      ¬(encode raw).freeVars ⊆ Mettapedia.Logic.LP.eqVars (equations []) := by
  refine ⟨by simp [Solves], ?_, ?_⟩
  · decide +kernel
  · decide +kernel

def collectedExecute (capacity : Nat) (context : ClosedOnceQueryFrame.Frame) (facts : List Atom) (fuel : Nat := 80) :=
  (ScopedQuerySource.machine .relational program).run fuel
    (ClosedOnceQueryFrame.placed (Allocator.empty capacity 8) ⟨NamedSpaces.Store.new facts [], [], []⟩
      (⟨[], [], none⟩ : CollectionScope Unit) []
      {(initial context (request 7) raw) with goals :=
        [.evaluate (CapturedCollectedOnceSource.source (request 7) raw) (.var context.output)]} () [4] [])

#guard (collectedExecute 8 (frame 7) rows).1.map CollectedAnswer.value == [.expression [.symbol "t"]]
#guard (collectedExecute 8 (frame 9) rows).1.map CollectedAnswer.value == [.expression []]
#guard (collectedExecute 8 aliased rows).1.map CollectedAnswer.value == [.expression [.symbol "t"]]

def copyingRefused : Bool := match (collectedExecute 0 (frame 7) rows).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard copyingRefused
#guard (collectedExecute 0 (frame 7) rows).1.isEmpty
#guard (collectedExecute 0 (frame 9) rows).1.map CollectedAnswer.value == [.expression []]

def paused := EagerDFSStreaming.Scoped.readback (collectedExecute 8 (frame 7) rows 11).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 80 saved
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [.expression [.symbol "t"]]

#print axioms source_prefix
#print axioms CapturedPatternSupport.source_names_bound
#print axioms CapturedPatternSupport.location_eq_literal
#print axioms CapturedPatternSupport.answer_eq_literal
#print axioms CapturedCollectedOnceSource.source_return_boundary

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource.Controls
