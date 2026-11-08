import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnLocal

/-!
# Source alias-return entry and the separate ground-read boundary

Fresh clause entry earns an output/input alias obligation even when the
input is open. Groundness is used only to compare the reached input read to
the earlier read. Neither fact says that typing observations remain stable
under changes to declarations, spaces, or other query dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open ScopedReturnLocal (AliasHolds)

theorem selected_variable_alias_contract (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument : Atom) (formalName : String) (inspectionFuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some (.var formalName))
    (target : control.destination = destination)
    (checked : ScopedReturnSyntax.checksSurfaceReturn (.var formalName) inspectionFuel equation.body = true) :
    AliasHolds argument next := by
  let rename := ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)
  have fields := ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected
  refine ⟨rename formalName, ?_, Or.inr ?_⟩
  · intro environment solved
    simpa only [renameTypeVars, rename] using
      ScopedReturnEntry.fresh_recipe_read control head arguments destination older occurrence equation next index
        argument (.var formalName) selected actual formal environment solved
  · rw [fields.1, target, fields.2.2.1]
    apply ScopedReturnObligation.Pending.evaluation
    simpa only [renameTypeVars, ClauseChoice.freshBody, rename] using
      (ScopedReturnSyntax.checksSurfaceReturn_sound (.var formalName) inspectionFuel equation.body checked).rename rename

theorem predicate_entry_alias (argument : Atom) (next : Control) (body destination : Atom)
    (older : List Goal) (retained : Nat) (entered : AliasHolds argument next)
    (atBody : next.goals = .evaluate body destination :: older) :
    AliasHolds argument (predicateEntry retained next) := by
  obtain ⟨name, holds⟩ := entered
  refine ⟨name, holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · right
    change ScopedReturnObligation.Pending (.var name) next.destination (predicateEntry retained next).goals
    simp only [predicateEntry, atBody]
    rcases pending.head_or_tail _ _ atBody with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      exact .evaluation _ _ returns
    · exact tail.prepend [.evaluate body destination, .restoreCommit next.cutBoundary] rfl

/-- Logical refinement plus an actual earlier ground read stabilizes the
term's read. This is not a theorem about a typing observer or its world. -/
theorem ground_entry_read_retained {before after : Equations} {initial reached : Environment}
    (resolved : resolve before = some initial) (extended : RefinementTransport.Extends before after)
    (solved : Solves reached after) (argument : Atom)
    (ground : (encode (read initial argument)).isGround) :
    read reached argument = read initial argument := by
  have absorbed := resolve_read_preserved_by_extension resolved extended reached solved argument
  rw [ProtectedSlots.read_ground reached _ ground] at absorbed
  exact absorbed.symm

theorem terminal_ground_entry_observation {Context : Type} (argument : Atom) (cursor : Cursor Context)
    (holds : AliasHolds argument cursor.control) (terminal : cursor.control.goals = [])
    (before : Equations) (initial reached : Environment)
    (entry : resolve before = some initial)
    (extended : RefinementTransport.Extends before cursor.control.bindings)
    (resolved : resolve cursor.control.bindings = some reached)
    (ground : (encode (read initial argument)).isGround) :
    read reached cursor.control.destination = read initial argument := by
  rw [ScopedReturnLocal.terminal_alias_observation argument cursor holds terminal reached resolved]
  exact ground_entry_read_retained entry extended (resolve_sound resolved) argument ground

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry
