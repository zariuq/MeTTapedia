import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch

/-!
# Authored compound return bodies at actual fresh clause entry

The body is inspected in the existing return-position grammar. The selected
clause's own renamer transports both that grammar and its constructor recipe.
Actual head matching earns the relation to the actual input. No completed
body evaluation, result list or independently chosen fresh recipe is given.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open DestinationDataRecipe
open DestinationDataReturnState

theorem selected_return_entry (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (occurrence : Nat)
    (equation : SpaceSemantics.Equation) (next : Control) (index : Nat) (argument recipe : Atom)
    (inspectionFuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (data : Recipe program recipe)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true)
    (root : control.destination = destination) : AliasHolds program argument next := by
  let fresh := ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)
  have fields := ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected
  refine ⟨renameTypeVars fresh recipe, DestinationDataEntry.rename_recipe data fresh, ?_, .inr (.inl ?_)⟩
  · intro environment solved
    exact ScopedReturnEntry.fresh_recipe_read control head arguments destination older occurrence equation next index
      argument recipe selected actual formal environment solved
  · rw [fields.1, root, fields.2.2.1]
    exact .evaluation _ older ((ScopedReturnSyntax.checksSurfaceReturn_sound recipe inspectionFuel equation.body checked).rename fresh)

/-- The caller's commitment delimiter is actual source work, not an extra
typing or return equation. -/
theorem selected_predicate_entry (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (occurrence retained : Nat)
    (equation : SpaceSemantics.Equation) (next : Control) (index : Nat) (argument recipe : Atom)
    (inspectionFuel : Nat)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe)
    (data : Recipe program recipe)
    (checked : ScopedReturnSyntax.checksSurfaceReturn recipe inspectionFuel equation.body = true)
    (root : control.destination = destination) : AliasHolds program argument (predicateEntry retained next) := by
  let fresh := ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)
  have fields := ClauseChoice.attempt_preserves_caller control head arguments destination older occurrence equation next selected
  refine ⟨renameTypeVars fresh recipe, DestinationDataEntry.rename_recipe data fresh, ?_, .inr (.inl ?_)⟩
  · intro environment solved
    exact ScopedReturnEntry.fresh_recipe_read control head arguments destination older occurrence equation next index
      argument recipe selected actual formal environment solved
  · change ScopedReturnObligation.Pending (renameTypeVars fresh recipe) next.destination
      (predicateEntry retained next).goals
    simp only [predicateEntry, fields.2.2.1, fields.1, root]
    exact .evaluation _ _ ((ScopedReturnSyntax.checksSurfaceReturn_sound recipe inspectionFuel equation.body checked).rename fresh)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnEntry
