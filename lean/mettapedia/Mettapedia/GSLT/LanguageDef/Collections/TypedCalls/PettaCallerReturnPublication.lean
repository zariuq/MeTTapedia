import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMachine

/-!
# Publication consumes only the owning typed-frame boundary

Return-view preservation alone does not say which control may publish. The
root-depth condition below is a concrete stack-coordinate condition, not an
assumed answer equation. Under it, an actual typed-overlay publication comes
from a root occurrence with no suspended typed callers, and its reached record
therefore earns the input-alias observation.

Deriving this condition over every source-generated run requires the stronger
indexed scope/frame invariant; it is not inferred from the return view here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def RootDepths {User : Type} (source : State User) : Prop :=
  ∀ current control context origins pending,
    source.2.scopes = [current] → current.frontier = (control, context, origins) :: pending →
    ∀ frame ∈ context.calls, frame.scopeDepth = 1

def rootDepthCheck {User : Type} (source : State User) : Bool :=
  match source.2.scopes with
  | [current] => match current.frontier with
      | (_, context, _) :: _ => context.calls.all fun frame => frame.scopeDepth == 1
      | [] => true
  | _ => true

theorem rootDepthCheck_iff {User : Type} (source : State User) :
    rootDepthCheck source = true ↔ RootDepths source := by
  constructor
  · intro checked current control context origins pending scopes frontier frame member
    simp only [rootDepthCheck, scopes, frontier] at checked
    exact of_decide_eq_true (by simpa using List.all_eq_true.mp checked frame member)
  · intro bounded
    cases scopes : source.2.scopes with
    | nil => simp [rootDepthCheck, scopes]
    | cons current parents =>
        cases parents with
        | cons parent parents => simp [rootDepthCheck, scopes]
        | nil =>
            cases frontier : current.frontier with
            | nil => simp [rootDepthCheck, scopes, frontier]
            | cons item pending =>
                rcases item with ⟨control, context, origins⟩
                simp only [rootDepthCheck, scopes, frontier]
                apply List.all_eq_true.mpr
                intro frame member
                simpa using bounded current control context origins pending scopes frontier frame member

private theorem lift_publish {User : Type} (action : Bridges.ScopedQuerySource.Action (Context User))
    (events : List CollectedAnswer) (after : State User)
    (published : liftSource action = .publish events after) : action = .publish events after := by
  cases action <;> cases published
  rfl

theorem publication_is_source {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source after : State User) (events : List CollectedAnswer)
    (published : PettaOccurrenceOverlay.step services .eagerValue program source = .publish events after) :
    Bridges.ScopedQuerySource.ownedStep .eagerValue program source = .publish events after := by
  unfold PettaOccurrenceOverlay.step at published
  repeat' first
    | exact lift_publish _ events after published
    | (unfold delegate at published)
    | (unfold enterRows at published)
    | (unfold nextArgument at published)
    | (unfold consumeArgument at published)
    | (unfold consumeBody at published)
    | (cases published)
    | (split at published <;> try dsimp only at published)

theorem published_packets_read_input {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (source after : State User) (events : List CollectedAnswer)
    (valid : PettaCallerReturnMachine.Invariant inputs source) (depths : RootDepths source)
    (published : PettaOccurrenceOverlay.step services .eagerValue program source = .publish events after) :
    ∀ packet ∈ events,
      ∃ user environment, resolve packet.bindings = some environment ∧ packet.value = read environment (inputs user) := by
  have owned := publication_is_source services program source after events published
  have raw := Bridges.ScopedQueryBinding.owned_publication_is_raw .eagerValue program source after events owned
  have derived := (Source.scoped_step_iff_source .eagerValue program source valid.1 _).mp raw
  obtain ⟨root, roots⟩ := Bridges.ScopedReturnPublication.source_publication_is_root derived valid.1 events rfl
  obtain ⟨current, parents, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, terminal, resolved, emitted, records, output, _solved⟩ :=
    scope_published_origin .eagerValue program source after events raw
  have shape : current :: parents = [root] := scopes.symm.trans roots
  cases shape
  have noCalls : context.calls = [] := by
    cases calls : context.calls with
    | nil => rfl
    | cons frame outside =>
        have depth := depths root control context origins pending roots frontier frame (calls ▸ List.mem_cons_self)
        simp only [PettaOccurrenceOverlay.step, roots, frontier, calls, List.length_cons, List.length_nil,
          depth] at published
        cases phase : frame.phase <;>
          simp only [phase, terminal, List.isEmpty_nil, if_true, resolved] at published
        all_goals repeat' first
          | (cases published)
          | (unfold nextArgument at published)
          | (unfold consumeArgument at published)
          | (unfold consumeBody at published)
          | (split at published <;> try dsimp only at published)
  have held := PettaCallerReturnView.root_work inputs source root roots valid.2
    (control, context, origins) (frontier ▸ List.mem_cons_self)
  have localHeld : PettaCallerReturnFrames.Frames (inputs context.user) control [] := by
    simpa only [PettaCallerReturnPhases.WorkHolds, noCalls] using held
  have aliasRead := localHeld.no_calls
  have actual := Bridges.ScopedReturnLocal.terminal_alias_observation (inputs context.user)
    (⟨source.2.world, control, context⟩ : Cursor (Context User)) aliasRead terminal environment resolved
  intro packet member
  rw [emitted] at member
  cases List.mem_singleton.mp member
  exact ⟨context.user, environment, by simpa only [records] using resolved, output.trans actual⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPublication
