import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSourceControls

/-! Captured guards select one body; aliased mutation outputs remain logical
variables, while constrained outputs retain reference execution before effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number self mark program)
open CapturedOnceSource.Controls (request raw frame rows aliased openFacts)

def yes : Atom := call "add-atom" [self, mark 1]
def no : Atom := call "add-atom" [self, mark 0]

def execute (capacity : Nat) (context : ClosedOnceQueryFrame.Frame) (facts : List Atom)
    (yesBody : Atom := yes) (noBody : Atom := no) (fuel : Nat := 200) :=
  (ScopedQuerySource.machine .relational program).run fuel
    (ClosedOnceQueryFrame.placed (Allocator.empty capacity 8) ⟨NamedSpaces.Store.new facts [], [], []⟩
      (⟨[], [], none⟩ : CollectionScope Unit) []
      (conditionalEntry {bindings := context.bindings, goals := [], destination := .var context.output}
        (.var context.output) (request 7) raw yesBody noBody) () [4] [])

def finalRows (capacity : Nat) (context : ClosedOnceQueryFrame.Frame) (facts : List Atom)
    (yesBody : Atom := yes) (noBody : Atom := no) :=
  (EagerDFSStreaming.Scoped.readback (execute capacity context facts yesBody noBody).2).bind
    fun saved => saved.2.world.state.read .self

#guard (execute 8 (frame 7) rows).1.map CollectedAnswer.value == [Effects.boolean true]
#guard finalRows 8 (frame 7) rows == some (rows ++ [mark 1])
#guard finalRows 8 (frame 9) rows == some (rows ++ [mark 0])
#guard finalRows 8 aliased rows == some (rows ++ [mark 1])
#guard finalRows 0 (frame 7) rows == some rows
#guard finalRows 0 (frame 9) rows == some (rows ++ [mark 0])

def copyRefused : Bool := match (execute 0 (frame 7) rows).2 with
  | .suspended .allocation _ => true
  | _ => false
#guard copyRefused

def bad : Atom := call "add-atom" [.symbol "missing-space", mark 99]
#guard (execute 8 (frame 7) rows (.symbol "kept") bad).1.map CollectedAnswer.value == [.symbol "kept"]
#guard (execute 8 (frame 9) rows bad (.symbol "missing")).1.map CollectedAnswer.value == [.symbol "missing"]

def retainedRaw : Bool := match (execute 8 (frame 7) openFacts).2 with
  | .suspended (.branch (.invoke "match" [_, patternCode, _] _)) _ => patternCode == raw
  | _ => false
#guard retainedRaw

def paused := EagerDFSStreaming.Scoped.readback (execute 8 aliased rows yes no 15).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 200 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [mark 1])

def aliasBindings : Equations := [(.var "result", .var "alias")]
theorem alias_is_not_syntactically_fresh : ¬ClosedOnceQueryFrame.FreshFor "result" aliasBindings := by
  intro fresh
  have absent := (fresh (.var "result", .var "alias") (by simp [aliasBindings])).1
  simp [encode, Mettapedia.Logic.LP.Term.freeVars] at absent

theorem alias_still_accepts_the_closed_result :
    refine aliasBindings (Effects.boolean true) (.var "result") =
      some (aliasBindings ++ [(Effects.boolean true, .var "result")]) := by
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, (fun _ => encode (Effects.boolean true)), ?_, ?_⟩
  · simp [Solves, aliasBindings, EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  · simp [EagerDFS.Destination.read, encode, Effects.boolean, Mettapedia.Logic.LP.Subst.applyTerm, decode]

theorem a_constrained_alias_does_not :
    refine (aliasBindings ++ [(.var "alias", Effects.boolean false)]) (Effects.boolean true) (.var "result") = none := by
  cases computed : refine (aliasBindings ++ [(.var "alias", Effects.boolean false)]) (Effects.boolean true) (.var "result") with
  | none => rfl
  | some next =>
      obtain ⟨_, environment, solved, result⟩ := (refine_iff _ _ _ _).mp computed
      have aliasedEq := solved (.var "result", .var "alias") (by simp [aliasBindings])
      have bound := solved (.var "alias", Effects.boolean false) (by simp)
      rw [PresenceGuardSource.read_boolean] at bound result
      exact (by decide : Effects.boolean true ≠ Effects.boolean false) (result.trans (aliasedEq.trans bound)) |>.elim

def aliasedMutation : Atom := call "let" [.var "ignored", .var "shared",
  call "let" [.var "ignored", call "add-atom" [self, mark 99],
    call "quote" [.expression [.var "ignored", .var "shared"]]]]
#guard ScopedQuerySource.Controls.answers program rows aliasedMutation ==
  some [.expression [Effects.boolean true, Effects.boolean true]]
#guard ScopedQuerySource.Controls.finalRows program rows aliasedMutation == some (rows ++ [mark 99])

#print axioms source_guard_prefix
#print axioms conditional_prefix
#print axioms ScopedMutationSource.refine_unbound
#print axioms ScopedMutationSource.primitive_prefix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource.Controls
