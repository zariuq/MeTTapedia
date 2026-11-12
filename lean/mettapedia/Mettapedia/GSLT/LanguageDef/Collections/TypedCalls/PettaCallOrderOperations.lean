import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder

/-!
# Actual typed operations preserve scope-depth order

Row entry uses the reached source depth and the existing bounds on older
frames. Every later frame update keeps that depth; return removes only the
top frame. No service success, returned value or typing result is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem active_bounds {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (bounded : PettaFrameScopes.Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    PettaFrameScopes.CallsAt source.2.scopes.length context := by
  have held : PettaFrameScopes.Scoped (current :: parents) := scopes ▸ bounded
  simpa only [scopes, List.length_cons] using held.head (control, context, origins) (frontier ▸ List.mem_cons_self)

theorem row_work {User : Type} (control : DControl) (context : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (ordered : Ordered context) (bounded : PettaFrameScopes.CallsAt depth context) :
    Ordered (rowWork control context origins depth head arguments destination older row occurrence).2.1 :=
  push ordered _ (fun frame member => (bounded frame member).2)

theorem enter_rows_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (good : Safe source)
    (bounded : PettaFrameScopes.Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (enterRows operations source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact PettaContextFacts.call_keeps source _ good
  · exact PettaContextFacts.call_keeps source _ good
  · dsimp only
    split
    · apply PettaContextFacts.silent_keeps
      apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
      intro ordered item member
      obtain ⟨⟨row, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
      exact row_work control context origins source.2.scopes.length head arguments destination older row occurrence
        ordered (active_bounds source current parents control context origins pending bounded scopes frontier)
    · exact PettaContextFacts.call_keeps source _ good

theorem next_argument_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (nextArgument operations source current parents control context origins pending frame outside) := by
  cases remaining : frame.remaining with
  | nil =>
      simp only [nextArgument, remaining]
      apply PettaContextFacts.silent_keeps
      apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
      intro ordered item member
      cases List.mem_singleton.mp member
      exact update ordered calls {frame with remaining := [], phase := .body} rfl
  | cons parameter rest =>
      rcases parameter with ⟨formal, argument⟩
      by_cases raw : demand formal = .raw
      · simp only [nextArgument, remaining, if_pos raw]
        apply PettaContextFacts.silent_keeps
        apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
        intro ordered item member
        cases List.mem_singleton.mp member
        exact update ordered calls
          {frame with remaining := rest, ready := frame.ready ++ [argument], index := frame.index + 1} rfl
      · simp only [nextArgument, remaining, if_neg raw]
        apply PettaContextFacts.silent_keeps
        apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
        intro ordered item member
        cases List.mem_singleton.mp member
        exact update ordered calls
          {frame with remaining := rest, phase := .argument formal (.var (freshName (protect operations source control context) 0))} rfl

theorem argument_guard_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (formal : Ty String) (slot value : Atom) (good : Safe source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (consumeArgument operations source current parents control context origins pending frame outside formal slot value) := by
  unfold consumeArgument
  split
  · exact PettaContextFacts.call_keeps source _ good
  · apply PettaContextFacts.silent_keeps
    apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
    intro ordered item member
    obtain ⟨⟨store, _occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
    exact update ordered calls
      {frame with ready := frame.ready ++ [slot], store := store, index := frame.index + 1, phase := .nextArgument} rfl

theorem result_guard_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (value : Atom) (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (consumeBody operations source current parents control context origins pending frame outside value) := by
  unfold consumeBody
  split
  · exact PettaContextFacts.call_keeps source _ good
  · apply PettaContextFacts.silent_keeps
    apply PettaContextFacts.install_keeps source current parents control context origins pending _ good scopes frontier
    intro ordered item member
    obtain ⟨⟨_store, _occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
    exact pop ordered calls

theorem delegate_keeps {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (good : Safe source) (bounded : PettaFrameScopes.Bounded source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (delegate operations .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact PettaContextFacts.source_keeps (@Ordered User) .eagerValue program source good
    | exact enter_rows_keeps operations source current parents control context origins pending _ _ _ _ good bounded scopes frontier
    | split

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder
