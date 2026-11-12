import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry

/-!
# Return aliases retain the original operand recipe

Materializing an operand at entry does not freeze its later observation.
The actual resolver and extension of its equations justify replacing that
materialized operand by the original recipe in a return-alias contract.
No groundness or stability of a typing query is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnReadRecipe

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnLocal (AliasHolds)

theorem alias_observation_congr (control : Control) (left right : Atom)
    (same : ∀ environment, Solves environment control.bindings →
      read environment left = read environment right)
    (held : AliasHolds left control) : AliasHolds right control := by
  obtain ⟨name, protectedRead, returning⟩ := held
  refine ⟨name, ?_, ?_⟩
  · intro environment solved
    exact (protectedRead environment solved).trans (same environment solved)
  · rcases returning with realized | pending
    · left
      intro environment solved
      exact (realized environment solved).trans (same environment solved)
    · exact .inr pending

theorem original_recipe_alias (before : Equations) (environment : Environment)
    (resolved : resolve before = some environment) (control : Control) (recipe : Atom)
    (extended : RefinementTransport.Extends before control.bindings)
    (held : AliasHolds (read environment recipe) control) : AliasHolds recipe control :=
  alias_observation_congr control (read environment recipe) recipe
    (fun candidate solved => resolve_read_preserved_by_extension resolved extended candidate solved recipe) held

/-- Every actual selected body extends the caller's equations. This is a
property of source selection, not an assumed body result. -/
theorem equation_work_extends {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat) :
    ∀ item ∈ equationWork program control boundary context origins head arguments destination older retained,
      RefinementTransport.Extends control.bindings item.1.bindings := by
  intro item member
  obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨equation, _row, attempted⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp selected
  have fields := ClauseChoice.attempt_preserves_caller (protectControl control boundary) head arguments destination
    older choice.1 equation choice.2 attempted
  change RefinementTransport.Extends control.bindings choice.2.bindings
  rw [fields.2.2.2]
  exact RefinementTransport.append_extends _ _

namespace Controls

private def slot : Atom := .var "later"
private def number : Atom := .grounded (.int 4)

theorem open_entry_recipe_has_no_fixed_value :
    (resolve []).map (fun environment => read environment slot) = some slot := by cbv

theorem later_binding_changes_the_observation :
    (resolve [(slot, number)]).map (fun environment => read environment slot) = some number := by cbv

theorem a_variable_recipe_is_not_a_constant_observation : slot ≠ number := by decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnReadRecipe
