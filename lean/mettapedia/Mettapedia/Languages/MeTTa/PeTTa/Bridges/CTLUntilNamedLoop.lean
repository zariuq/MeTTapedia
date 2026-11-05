import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls

/-!
# Actual named EU-loop entry with a retained fresh result

The complete clause scan selects the authored loop equation. Source-local
names are freshened against the live protection boundary, while the caller's
fresh output remains its original slot. Operand and caller equations are
retained; no formal-only replacement frame is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedLoop

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)

def definition : ScopedClosedEquationSource.Definition :=
  ⟨"eu-loop", ["f", "a", "k"], ScopedQuerySource.CTLUntilDriverControls.loopBody, by decide⟩

theorem declaration_exact : definition.declaration = ScopedQuerySource.CTLUntilDriverControls.loopEquation := rfl

def sourceNames : List String := ["f", "a", "k", "k1", "n", "d"]

private theorem source_name_in_clause (name : String) (member : name ∈ sourceNames) :
    name ∈ ClauseChoice.names (ClauseChoice.clauseAtoms definition.declaration) := by
  simp only [sourceNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure Call (Context : Type) where
  program : SpaceSemantics.Program
  state : NamedGuardedCandidateBatch.State Context
  control : Control
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  arguments : List Atom
  root : String
  older : List Goal
  occurrence : Nat

variable {Context Label : Type}

def Call.activeScope (call : Call Context) : CollectionScope Context :=
  {call.state.scope with frontier := (call.control, call.context, call.origins) :: call.pending}
def Call.protectedControl (call : Call Context) : Control :=
  protectControl call.control (collectionSupport ⟨call.state.world, call.activeScope :: call.state.parents⟩)
def Call.name (call : Call Context) (name : String) : String :=
  ScopedClosedEquationSource.formal call.protectedControl call.occurrence definition name
def Call.selected (call : Call Context) (values : List Atom) : Control :=
  ScopedClosedEquationSource.selected call.protectedControl call.occurrence definition values (.var call.root) call.older
def Call.bodyCaller (call : Call Context) (values : List Atom) : Control :=
  {call.selected values with
    goals := .restoreCommit call.control.cutBoundary :: call.older
    cutBoundary := call.pending.length}
def Call.before (call : Call Context) : ScopedCursor Context :=
  placed call.state.allocator call.state.world call.state.scope call.state.parents
    call.control call.context call.origins call.pending

theorem names_distinct (call : Call Context) (retained : call.root ∈ call.protectedControl.support) :
    [call.name "f", call.name "a", call.name "k", call.name "k1", call.name "n", call.name "d", call.root].Nodup := by
  have distinct : (sourceNames.map call.name).Nodup := by
    apply (by decide : sourceNames.Nodup).map_on
    intro first firstMember second secondMember same
    exact ClauseChoice.rename_injective_on call.protectedControl call.occurrence _
      (source_name_in_clause first firstMember) (source_name_in_clause second secondMember) same
  have apart : call.root ∉ sourceNames.map call.name := by
    rintro member
    obtain ⟨original, _, same⟩ := List.mem_map.mp member
    apply ClauseChoice.rename_fresh call.protectedControl call.occurrence
      (ClauseChoice.clauseAtoms definition.declaration) original
    change call.name original ∈ call.protectedControl.support
    rw [same]
    exact retained
  have appended : (sourceNames.map call.name ++ [call.root]).Nodup :=
    List.nodup_append.mpr ⟨distinct, by simp, by
      intro old member value valueMember same
      have valueEq : value = call.root := by simpa using valueMember
      exact apart ((same.trans valueEq) ▸ member)⟩
  exact appended

def Call.names (call : Call Context) (retained : call.root ∈ call.protectedControl.support) : CTLUntilLoopSource.Names :=
  ⟨call.name "f", call.name "a", call.name "k", call.name "k1", call.name "n", call.name "d", call.root,
    names_distinct call retained⟩

def values (codec : Codec Label) (label holds : Label) (round : Nat) : List Atom :=
  [codec.encode label, codec.encode holds, number round]

structure Evidence (codec : Codec Label) (label holds : Label) (round : Nat) (call : Call Context) where
  atCall : call.control.goals = .invoke "eu-loop" call.arguments (.var call.root) :: call.older
  principal : Environment
  resolved : resolve call.control.bindings = some principal
  readings : call.arguments.map (read principal) = values codec label holds round
  rootFresh : FreshFor call.root call.control.bindings
  row : call.program.equations[call.occurrence]? = some definition.declaration
  otherHeads : ∀ index equation, call.program.equations[index]? = some equation →
    index ≠ call.occurrence → equation.head ≠ "eu-loop"

theorem Evidence.root_retained {codec : Codec Label} {label holds : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label holds round call) : call.root ∈ call.protectedControl.support := by
  rw [Call.protectedControl, protectControl_support]
  apply Finset.mem_union_left
  apply ScopedClosedEquationSource.call_destination_retained call.control "eu-loop" call.arguments (.var call.root) call.older evidence.atCall
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem values_closed (codec : Codec Label) (label holds : Label) (round : Nat)
    (value : Atom) (member : value ∈ values codec label holds round) (environment : Environment) :
    read environment value = value := by
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact LiteralQuerySource.read_literal _ (codec.literal label) environment
  · exact LiteralQuerySource.read_literal _ (codec.literal holds) environment
  · exact CTLUntilSourceCapture.number_closed round environment

theorem fresh_body (call : Call Context) (retained : call.root ∈ call.protectedControl.support) :
    ClauseChoice.freshBody call.protectedControl call.occurrence definition.declaration =
      CTLUntilLoopSource.body (call.names retained) := by
  simp [ClauseChoice.freshBody, definition, ScopedClosedEquationSource.Definition.declaration,
    ScopedQuerySource.CTLUntilDriverControls.loopBody, ScopedQuerySource.Controls.call,
    ScopedQuerySource.Controls.number, CTLUntilLoopSource.body, CTLUntilLoopSource.app,
    CTLUntilLoopSource.increment, CTLUntilLoopSource.roundCall, CTLUntilLoopSource.cleanupCall,
    CTLUntilLoopSource.branch, CTLUntilLoopSource.recurse, Call.names, Call.name,
    ScopedClosedEquationSource.formal, HE.Spec.Type.RuntimeRefinement.renameTypeVars, number]

theorem entered_body (call : Call Context) (retained : call.root ∈ call.protectedControl.support)
    (arguments : List Atom) :
    predicateEntry call.pending.length (call.selected arguments) =
      CTLUntilLoopSource.entry (call.bodyCaller arguments) (call.names retained) := by
  simp only [Call.selected, ScopedClosedEquationSource.selected, predicateEntry]
  rw [fresh_body call retained]
  rfl

theorem enter_prefix {codec : Codec Label} {label holds : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label holds round call) :
    (ScopedQuerySource.machine .relational call.program).run 1 call.before =
      ([], .exhausted (placed call.state.allocator call.state.world call.state.scope call.state.parents
        (CTLUntilLoopSource.entry (call.bodyCaller (values codec label holds round)) (call.names evidence.root_retained))
        call.context (call.origins ++ [call.occurrence]) call.pending)) := by
  have length : call.arguments.length = definition.formals.length := by
    have measured := congrArg List.length evidence.readings
    simpa [values, definition] using measured
  have closed : ∀ argument ∈ call.arguments, ∀ environment,
      read environment (read evidence.principal argument) = read evidence.principal argument := by
    intro argument member environment
    apply values_closed codec label holds round _ ?_ environment
    rw [← evidence.readings]
    exact List.mem_map.mpr ⟨argument, member, rfl⟩
  have entry := ScopedClosedEquationSource.enter .relational call.program call.state.allocator call.state.world
    call.activeScope call.state.parents call.control call.context call.origins call.pending definition call.occurrence
    call.arguments (.var call.root) call.older evidence.principal call.root rfl evidence.atCall evidence.resolved
    (ClosedOnceQueryFrame.fresh_read _ _ _ evidence.rootFresh evidence.resolved) length closed
    (by decide) (by decide) (by decide) evidence.row evidence.otherHeads
  dsimp only at entry
  rw [evidence.readings] at entry
  change (ScopedQuerySource.machine .relational call.program).run 1 call.before =
    ([], .exhausted (placed call.state.allocator call.state.world call.activeScope call.state.parents
      (predicateEntry call.pending.length (call.selected (values codec label holds round))) call.context
      (call.origins ++ [call.occurrence]) call.pending)) at entry
  rw [entered_body call evidence.root_retained] at entry
  simpa only [Call.activeScope, placed] using entry

theorem root_fresh_after_entry {codec : Codec Label} {label holds : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label holds round call) :
    FreshFor call.root (call.bodyCaller (values codec label holds round)).bindings :=
  ScopedClosedEquationSource.selected_retained_fresh call.protectedControl call.occurrence definition
    (values codec label holds round) (.var call.root) call.older call.root evidence.rootFresh evidence.root_retained
    (values_closed codec label holds round)

theorem body_frame {codec : Codec Label} {label holds : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label holds round call) :
    Nonempty (CTLUntilLoopSource.InitialFrame codec label holds round (call.names evidence.root_retained)
      (call.bodyCaller (values codec label holds round))) := by
  obtain ⟨principal, resolved⟩ := resolve_complete (ScopedClosedEquationSource.selected_consistent
    call.protectedControl call.occurrence definition (values codec label holds round) (.var call.root) call.older
    rfl (values_closed codec label holds round) ⟨evidence.principal, resolve_sound evidence.resolved⟩)
  have readings := ScopedClosedEquationSource.selected_readings call.protectedControl call.occurrence definition
    (values codec label holds round) (.var call.root) call.older principal (values_closed codec label holds round)
    (resolve_sound resolved)
  change [read principal (.var (call.name "f")), read principal (.var (call.name "a")), read principal (.var (call.name "k"))] =
    [codec.encode label, codec.encode holds, number round] at readings
  simp only [List.cons.injEq, and_true] at readings
  refine ⟨⟨principal, resolved, readings.1, readings.2.1, readings.2.2, ?_⟩⟩
  intro name member
  change name ∈ [call.name "k1", call.name "n", call.name "d", call.root] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ScopedClosedEquationSource.local_fresh call.protectedControl call.occurrence definition
      (values codec label holds round) (.var call.root) call.older "k1" (by decide) (by decide) (values_closed codec label holds round)
  · exact ScopedClosedEquationSource.local_fresh call.protectedControl call.occurrence definition
      (values codec label holds round) (.var call.root) call.older "n" (by decide) (by decide) (values_closed codec label holds round)
  · exact ScopedClosedEquationSource.local_fresh call.protectedControl call.occurrence definition
      (values codec label holds round) (.var call.root) call.older "d" (by decide) (by decide) (values_closed codec label holds round)
  · exact root_fresh_after_entry evidence

theorem body_inherits (call : Call Context) (arguments : List Atom) (environment : Environment)
    (solved : Solves environment (call.bodyCaller arguments).bindings) : Solves environment call.control.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ member)

#print axioms enter_prefix
#print axioms root_fresh_after_entry
#print axioms body_frame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedLoop
