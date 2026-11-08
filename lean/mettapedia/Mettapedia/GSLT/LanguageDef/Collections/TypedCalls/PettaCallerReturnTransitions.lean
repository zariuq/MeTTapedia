import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnView

/-!
# Return-invariant preservation through actual typed transition phases

Each phase installs the exact work list returned by its existing operation.
Guard refusal, unserved guards and repeated successful stores remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnTransitions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay PettaCallerReturnFrames

def Preserves {User : Type} (inputs : User → Atom) (action : Step User) : Prop :=
  ∀ source ∈ PettaOccurrenceBinding.retained action, PettaCallerReturnView.Holds inputs source

theorem silent_preserves {User : Type} {inputs : User → Atom} (source : State User)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs (.silent source) := by
  simpa only [Preserves, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using held

theorem call_preserves {User : Type} {inputs : User → Atom} (source : State User) (request : Request)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs (.call request source) := by
  simpa only [Preserves, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using held

theorem enter_rows_preserves {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (held : PettaCallerReturnView.Holds inputs source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    Preserves inputs (enterRows services source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact call_preserves _ _ held
  · exact call_preserves _ _ held
  · dsimp only
    split
    · apply silent_preserves
      apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
      intro captured work member
      obtain ⟨⟨row, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
      exact PettaCallerReturnPhases.row_work_holds inputs services source control context origins head arguments
        destination older row occurrence captured atCall ordinary
    · exact call_preserves _ _ held

theorem next_argument_preserves {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (held : PettaCallerReturnView.Holds inputs source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Preserves inputs (nextArgument services source current parents control context origins pending frame outside) := by
  unfold nextArgument
  split
  · apply silent_preserves
    apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
    intro captured work member
    cases List.mem_singleton.mp member
    exact PettaCallerReturnPhases.ready_body_holds inputs services source control context frame outside (calls ▸ captured)
  · split
    · apply silent_preserves
      apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
      intro captured work member
      cases List.mem_singleton.mp member
      exact PettaCallerReturnPhases.raw_argument_holds inputs services source control context frame outside _ _ (calls ▸ captured)
    · apply silent_preserves
      apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
      intro captured work member
      cases List.mem_singleton.mp member
      exact PettaCallerReturnPhases.evaluated_argument_holds inputs services source control context frame outside _ _ _ _ (calls ▸ captured)

theorem argument_guard_preserves {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : PettaCallerReturnView.Holds inputs source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Preserves inputs (consumeArgument services source current parents control context origins pending frame outside formal slot value) := by
  unfold consumeArgument
  split
  · exact call_preserves _ _ held
  · apply silent_preserves
    apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
    intro captured
    exact PettaCallerReturnPhases.argument_continuations_hold inputs services source control context origins frame outside slot _ (calls ▸ captured)

theorem result_guard_preserves {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (held : PettaCallerReturnView.Holds inputs source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Preserves inputs (consumeBody services source current parents control context origins pending frame outside value) := by
  unfold consumeBody
  split
  · exact call_preserves _ _ held
  · apply silent_preserves
    apply PettaCallerReturnView.install_preserves inputs source current parents control context origins pending _ held scopes frontier
    intro captured
    exact PettaCallerReturnPhases.body_continuations_hold inputs services source control context origins frame outside _ (calls ▸ captured)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnTransitions
