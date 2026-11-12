import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentState

/-!
# The real row and guard operations preserve argument progress

The row operation's arity test earns exact zip alignment. Raw arguments are
appended at their source position. Evaluated arguments occupy one pending
position, and each served guard alternative appends that slot before the next
argument or body can start. Refusal and missing service do not invent a frame.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem enter_rows_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (good : Safe source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (enterRows operations source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact call_keeps source _ good
  · exact call_keeps source _ good
  · dsimp only
    split
    · rename_i arities
      apply silent_keeps
      apply install_keeps source current parents control context origins pending _ good scopes frontier
      intro held item member
      obtain ⟨⟨row, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
      have rowMember := List.fst_mem_of_mem_zipIdx present
      have arity : row.parameters.length = arguments.length := by
        simpa only [beq_iff_eq] using List.all_eq_true.mp arities row rowMember
      exact row_work_calls control context origins source.2.scopes.length head arguments destination older
        row occurrence arity held
    · exact call_keeps source _ good

theorem next_argument_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .nextArgument) :
    Keeps (nextArgument operations source current parents control context origins pending frame outside) := by
  have aligned := active_frame source current parents control context origins pending frame outside good scopes frontier calls
  cases remaining : frame.remaining with
  | nil =>
      simp only [nextArgument, remaining]
      apply silent_keeps
      apply install_keeps source current parents control context origins pending _ good scopes frontier
      intro held item member
      cases List.mem_singleton.mp member
      apply held.update calls
      simpa only [remaining] using body_ready aligned phase remaining
  | cons parameter rest =>
      rcases parameter with ⟨formal, argument⟩
      by_cases raw : demand formal = .raw
      · simp only [nextArgument, remaining, if_pos raw]
        apply silent_keeps
        apply install_keeps source current parents control context origins pending _ good scopes frontier
        intro held item member
        cases List.mem_singleton.mp member
        apply held.update calls
        simpa only [← phase] using raw_advance aligned phase formal argument rest remaining
      · simp only [nextArgument, remaining, if_neg raw]
        apply silent_keeps
        apply install_keeps source current parents control context origins pending _ good scopes frontier
        intro held item member
        cases List.mem_singleton.mp member
        exact held.update calls _ (begin_argument aligned phase formal argument _ rest remaining)

theorem argument_continuations_keep {User : Type} (operations : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat) (frame : CallFrame)
    (outside : List CallFrame) (formal : Ty String) (slot : Atom) (stores : List Store)
    (held : Calls context) (calls : context.calls = frame :: outside)
    (phase : frame.phase = .argument formal slot) :
    ∀ item ∈ argumentContinuations operations source control context origins frame outside slot stores,
      Calls item.2.1 := by
  intro item member
  obtain ⟨⟨store, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
  exact held.update calls _
    (guarded_advance (held frame (calls ▸ List.mem_cons_self)) formal slot phase store)

theorem argument_guard_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (formal : Ty String) (slot value : Atom) (good : Safe source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .argument formal slot) :
    Keeps (consumeArgument operations source current parents control context origins pending frame outside formal slot value) := by
  unfold consumeArgument
  split
  · exact call_keeps source _ good
  · apply silent_keeps
    apply install_keeps source current parents control context origins pending _ good scopes frontier
    intro held
    exact argument_continuations_keep operations source control context origins frame outside formal slot _ held calls phase

theorem result_guard_keeps {User : Type} (operations : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (value : Atom) (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (consumeBody operations source current parents control context origins pending frame outside value) := by
  unfold consumeBody
  split
  · exact call_keeps source _ good
  · apply silent_keeps
    apply install_keeps source current parents control context origins pending _ good scopes frontier
    intro held item member
    obtain ⟨⟨_store, _occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
    exact held.pop calls

theorem delegate_keeps {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (delegate operations .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact source_keeps .eagerValue program source good
    | exact enter_rows_keeps operations source current parents control context origins pending _ _ _ _ good scopes frontier
    | split

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
