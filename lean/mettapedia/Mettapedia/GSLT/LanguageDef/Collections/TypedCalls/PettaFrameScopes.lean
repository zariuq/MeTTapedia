import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPublication

/-!
# Typed call frames belong to their retained source scopes

Active work carries positive frame depths bounded by its current scope depth.
A collection's saved caller is bounded by the parent depth, not by the child's
depth. The indexed scope tree keeps these distinct through push and resumption.
This is a structural invariant of the existing typed/source state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

def CallsAt {User : Type} (depth : Nat) (context : Context User) : Prop :=
  ∀ frame ∈ context.calls, 0 < frame.scopeDepth ∧ frame.scopeDepth ≤ depth

theorem CallsAt.weaken {User : Type} {small large : Nat} {context : Context User}
    (bounded : CallsAt small context) (monotone : small ≤ large) : CallsAt large context := by
  intro frame member
  exact ⟨(bounded frame member).1, (bounded frame member).2.trans monotone⟩

theorem CallsAt.empty {User : Type} (depth : Nat) (user : User) : CallsAt depth (⟨user, []⟩ : Context User) := by
  intro frame impossible
  cases impossible

theorem CallsAt.push {User : Type} {depth : Nat} {context : Context User}
    (bounded : CallsAt depth context) (frame : CallFrame)
    (positive : 0 < frame.scopeDepth) (within : frame.scopeDepth ≤ depth) :
    CallsAt depth {context with calls := frame :: context.calls} := by
  intro other member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨positive, within⟩
  · exact bounded other member

theorem CallsAt.update_top {User : Type} {depth : Nat} {context : Context User}
    {frame : CallFrame} {outside : List CallFrame} (bounded : CallsAt depth context)
    (calls : context.calls = frame :: outside) (updated : CallFrame)
    (same : updated.scopeDepth = frame.scopeDepth) :
    CallsAt depth {context with calls := updated :: outside} := by
  intro other member
  rcases List.mem_cons.mp member with rfl | member
  · rw [same]
    exact bounded frame (calls ▸ List.mem_cons_self)
  · exact bounded other (calls ▸ List.mem_cons_of_mem _ member)

theorem CallsAt.pop {User : Type} {depth : Nat} {context : Context User}
    {frame : CallFrame} {outside : List CallFrame} (bounded : CallsAt depth context)
    (calls : context.calls = frame :: outside) : CallsAt depth {context with calls := outside} := by
  intro other member
  exact bounded other (calls ▸ List.mem_cons_of_mem _ member)

inductive Scoped {User : Type} : List (Scope User) → Prop where
  | root (frontier : List (Work User)) (collected : List CollectedAnswer)
      (works : ∀ item ∈ frontier, CallsAt 1 item.2.1) :
      Scoped [⟨frontier, collected, none⟩]
  | nested (frontier : List (Work User)) (collected : List CollectedAnswer)
      (caller : CollectionCaller (Context User)) (parents : List (Scope User))
      (outer : Scoped parents)
      (works : ∀ item ∈ frontier, CallsAt (parents.length + 1) item.2.1)
      (saved : CallsAt parents.length caller.2.2.1) :
      Scoped (⟨frontier, collected, some caller⟩ :: parents)

theorem Scoped.nonempty {User : Type} {scopes : List (Scope User)} (bounded : Scoped scopes) : scopes ≠ [] := by
  cases bounded <;> simp

theorem Scoped.valid {User : Type} {scopes : List (Scope User)} (bounded : Scoped scopes) :
    EagerDFS.ScopesValid scopes := by
  induction bounded with
  | root frontier collected works => exact .root _ _
  | nested frontier collected caller parents outer works saved ih => exact .nested _ _ _ ih

theorem Scoped.head {User : Type} {current : Scope User} {parents : List (Scope User)}
    (bounded : Scoped (current :: parents)) :
    ∀ item ∈ current.frontier, CallsAt (parents.length + 1) item.2.1 := by
  cases bounded with
  | root frontier collected works => exact works
  | nested frontier collected caller parents outer works saved => exact works

theorem Scoped.replace_head {User : Type} {current : Scope User} {parents : List (Scope User)}
    (bounded : Scoped (current :: parents)) (frontier : List (Work User)) (collected : List CollectedAnswer)
    (works : ∀ item ∈ frontier, CallsAt (parents.length + 1) item.2.1) :
    Scoped ({current with frontier, collected} :: parents) := by
  cases bounded with
  | root old collected prior => exact .root frontier _ works
  | nested old collected caller parents outer prior saved => exact .nested frontier _ caller parents outer works saved

theorem Scoped.replace_active {User : Type} {current : Scope User} {parents : List (Scope User)}
    (bounded : Scoped (current :: parents)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending generated : List (Work User)) (collected : List CollectedAnswer)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (produced : CallsAt (parents.length + 1) context →
      ∀ item ∈ generated, CallsAt (parents.length + 1) item.2.1) :
    Scoped ({current with frontier := generated ++ pending, collected} :: parents) := by
  apply bounded.replace_head
  intro item member
  rcases List.mem_append.mp member with generated | retained
  · exact produced (bounded.head _ (frontier ▸ List.mem_cons_self)) item generated
  · exact bounded.head item (frontier ▸ List.mem_cons_of_mem _ retained)

theorem Scoped.push {User : Type} {current : Scope User} {parents : List (Scope User)}
    (bounded : Scoped (current :: parents)) (child : Scope User)
    (caller : CollectionCaller (Context User)) (pending : List (Work User))
    (atCaller : child.caller = some caller)
    (pendingBound : ∀ item ∈ pending, CallsAt (parents.length + 1) item.2.1)
    (childBound : ∀ item ∈ child.frontier, CallsAt (parents.length + 2) item.2.1)
    (saved : CallsAt (parents.length + 1) caller.2.2.1) :
    Scoped (child :: {current with frontier := pending} :: parents) := by
  cases child with
  | mk frontier collected stored =>
      dsimp only at atCaller
      subst stored
      exact .nested frontier collected caller _ (bounded.replace_head pending current.collected pendingBound)
        childBound saved

theorem Scoped.resume {User : Type} {child parent : Scope User} {parents : List (Scope User)}
    (bounded : Scoped (child :: parent :: parents)) (caller : CollectionCaller (Context User))
    (atCaller : child.caller = some caller) (work : Work User)
    (returned : CallsAt (parents.length + 1) caller.2.2.1 → CallsAt (parents.length + 1) work.2.1) :
    Scoped ({parent with frontier := work :: parent.frontier} :: parents) := by
  cases bounded with
  | nested frontier collected saved rest outer works held =>
      cases Option.some.inj atCaller
      apply outer.replace_head
      intro item member
      rcases List.mem_cons.mp member with rfl | previous
      · exact returned held
      · exact outer.head item previous

def Bounded {User : Type} (source : State User) : Prop := Scoped source.2.scopes

theorem root_depths {User : Type} (source : State User) (bounded : Bounded source) :
    PettaCallerReturnPublication.RootDepths source := by
  intro current control context origins pending scopes frontier frame member
  have root : Scoped [current] := scopes ▸ bounded
  have limits := root.head (control, context, origins) (frontier ▸ List.mem_cons_self) frame member
  dsimp only [List.length_nil] at limits
  omega

theorem row_work_bound {User : Type} (depth : Nat) (control : DControl) (context : Context User)
    (origins : List Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat) (positive : 0 < depth)
    (bounded : CallsAt depth context) :
    CallsAt depth (rowWork control context origins depth head arguments destination older row occurrence).2.1 :=
  bounded.push _ positive (Nat.le_refl _)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopes
