import Mettapedia.Data.ScopedString
import Mettapedia.Languages.MeTTa.PeTTa.PrivateCode
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixes

/-!
# Scoped requests at the unifying evaluator's source boundary

Source spellings are arbitrary strings. Both requests and subsequent clause
uses therefore need activation identities. This module scopes a request before
entering the existing machine and retains its actual allocation counter between
requests. It does not restart an exhausted computation or implement evaluation.

The raw `Unifying.start` is useful for internal machine controls but is not a
fresh source boundary. This construction addresses entry and counter retention.
The existing machine supplies separate copy boundaries for parsing, input,
enumerated stored rows and assignment. A whole-configuration support invariant
and open-answer readout remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ScopedSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open Mettapedia.Machines
open Unifying

@[simp] theorem freshName_eq_encode (scope : Nat) (name : String) :
    freshName scope name = Mettapedia.ScopedString.encode scope name := rfl

theorem freshName_equal_iff (left right : Nat) (first second : String) :
    freshName left first = freshName right second ↔ left = right ∧ first = second :=
  Mettapedia.ScopedString.encode_equal_iff left right first second

theorem rename_freeVars (scope : Nat) : ∀ term : Atom,
    atomFreeVars (rename scope term) = (atomFreeVars term).map (freshName scope)
  | .var _ => rfl
  | .symbol _ | .grounded _ => rfl
  | .expression items => list items
where
  list : ∀ items : List Atom,
      atomFreeVars.atomFreeVarsList (rename.renameList scope items) =
        (atomFreeVars.atomFreeVarsList items).map (freshName scope)
    | [] => rfl
    | first :: rest => by
        simp only [rename.renameList,atomFreeVars.atomFreeVarsList,List.map_append,
          rename_freeVars scope first,list rest]

/-- Every logical identity has been allocated below the next use number. -/
def Allocated (next : Nat) (term : Atom) : Prop :=
  ∀ key ∈ atomFreeVars term, Mettapedia.ScopedString.Before next key

theorem renamed_allocated (scope : Nat) (term : Atom) :
    Allocated (scope + 1) (rename scope term) := by
  intro key present
  rw [rename_freeVars] at present
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp present
  exact Mettapedia.ScopedString.new_identity_before_next scope original

theorem allocated_mono {first later : Nat} (ordered : first ≤ later) {term : Atom}
    (allocated : Allocated first term) : Allocated later term := by
  intro key present
  exact Mettapedia.ScopedString.before_mono ordered (allocated key present)

/-- A later clause cannot alias any variable of an admitted earlier term,
including source spellings which already contain numeric suffixes. -/
theorem later_scope_is_apart {earlier later : Nat} (ordered : earlier ≤ later)
    {term : Atom} (allocated : Allocated earlier term) (key : String) :
    freshName later key ∉ atomFreeVars term := by
  intro present
  exact Mettapedia.ScopedString.new_identity_is_fresh
    (Mettapedia.ScopedString.before_mono ordered (allocated _ present)) key rfl

/-- A source request allocates one scope. Public rows and private clauses are
templates; their variables receive scopes when the existing selector uses them. -/
def enter (scope : Nat) (code : List SpaceSemantics.Equation) (state : Effects.State)
    (expression : Atom) : Configuration :=
  {state,control := .evaluate [] (rename scope expression),uses := scope + 1,privateCode := code}

theorem entry_is_allocated (scope : Nat) (expression : Atom) :
    Allocated (scope + 1) (rename scope expression) := renamed_allocated scope expression

theorem entry_and_later_clause_are_apart (scope later : Nat) (expression : Atom)
    (ordered : scope < later) (key : String) :
    freshName later key ∉ atomFreeVars (rename scope expression) :=
  later_scope_is_apart (by omega) (entry_is_allocated scope expression) key

theorem transition_uses_mono {registry : SpaceSemantics.Program} {before after : Configuration}
    (edge : Transition registry before after) : before.uses ≤ after.uses := by
  cases edge <;> simp

theorem transitions_uses_mono {registry : SpaceSemantics.Program} {before after : Configuration}
    (path : Relation.ReflTransGen (Transition registry) before after) : before.uses ≤ after.uses := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.le_refl _
  | head edge _ ih => exact (transition_uses_mono edge).trans ih

/-- Execute the existing steps once and retain their endpoint, including the
allocation supply, handlers, store, I/O and private code. -/
def endpoint (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration) : Configuration :=
  BoundedDeterministicRun.run (step registry) fuel source

theorem endpoint_observation (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration) :
    run registry 0 (endpoint registry fuel source) = run registry fuel source :=
  (run_as_bounded registry fuel source).symm

theorem endpoint_uses_mono (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration) :
    source.uses ≤ (endpoint registry fuel source).uses :=
  transitions_uses_mono (bounded_endpoint_reachable registry fuel source)

theorem endpoint_keeps_privateCode (registry : SpaceSemantics.Program) (fuel : Nat)
    (source : Configuration) : (endpoint registry fuel source).privateCode = source.privateCode :=
  transitions_keep_privateCode (bounded_endpoint_reachable registry fuel source)

/-- The next request uses the reached supply rather than resetting it. This
operation is used only after a completed request in `requests` below. -/
def next (source : Configuration) (expression : Atom) : Configuration :=
  {source with control := .evaluate [] (rename source.uses expression),frames := [],uses := source.uses + 1}

theorem next_keeps_world (source : Configuration) (expression : Atom) :
    (next source expression).state = source.state ∧
    (next source expression).input = source.input ∧
    (next source expression).output = source.output ∧
    (next source expression).privateCode = source.privateCode := ⟨rfl,rfl,rfl,rfl⟩

theorem next_scope_is_later (registry : SpaceSemantics.Program) (fuel scope : Nat)
    (code : List SpaceSemantics.Equation) (state : Effects.State) (expression : Atom) :
    scope < (endpoint registry fuel (enter scope code state expression)).uses := by
  have allocated := endpoint_uses_mono registry fuel (enter scope code state expression)
  exact lt_of_lt_of_le (Nat.lt_succ_self scope) allocated

/-- Successive requests retain the reached world and scope supply. A suspended
or faulty request terminates this list; its full configuration remains in its
outcome for resumption. No fallback re-executes the earlier request. -/
def requests (program : SpaceSemantics.Program) (fuel : Nat) :
    Configuration → List Atom → List Outcome
  | _, [] => []
  | source, expression :: rest =>
      let initial := next source expression
      let registry := LiveEquations.atState program initial.state
      let saved := endpoint registry fuel initial
      match run registry 0 saved with
      | .complete state answers input output =>
          .complete state answers input output :: requests program fuel saved rest
      | stopped => [stopped]

end Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
