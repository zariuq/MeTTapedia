import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.CategoryTheory.RunAccount
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Accounts of operational realization blocks

The free execution category already retains ordered primitive transitions.
A realization expands one source transition into a selected target path.
Its path functor restricts the existing run accounts, including the account
that counts every primitive transition. Block lengths bound complete paths,
and staged expansion reads the same target account as direct expansion.

These paths retain states and proposition-valued step evidence. Distinct
authored occurrences require the separate occurrence-path interface; elapsed
time and physical resource consumption require their own valuations.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

/-- The existing run account of the number of actual primitive transitions. -/
def transitionAccount (theory : GSLT) :
    Mettapedia.Effects.RunAccount (ExecutionObject theory) (Multiplicative Nat) where
  of path := Multiplicative.ofAdd path.length
  of_id _ := rfl
  of_comp first second :=
    congrArg Multiplicative.ofAdd (Route.length_append first second)

namespace OperationalRealization

variable {source middle target : GSLT}

/-- Expanding source edges to blocks extends to the existing path categories. -/
def pathFunctor (realization : OperationalRealization source target) :
    ExecutionObject source ⥤ ExecutionObject target where
  obj := realization.mapTerm
  map := realization.mapRoute
  map_id _ := rfl
  map_comp first second := realization.mapRoute_append first second

/-- Count the complete selected target block, including administrative steps. -/
def blockAccount (realization : OperationalRealization source target) :
    Mettapedia.Effects.RunAccount (ExecutionObject source) (Multiplicative Nat) :=
  (transitionAccount target).comap realization.pathFunctor

theorem blockAccount_comp (earlier : OperationalRealization source middle)
    (later : OperationalRealization middle target)
    {first last : source.Term} (path : ExecutionPath source first last) :
    ((earlier.comp later).blockAccount).of path =
      Multiplicative.ofAdd (later.mapRoute (earlier.mapRoute path)).length := by
  change Multiplicative.ofAdd ((earlier.comp later).mapRoute path).length = _
  exact congrArg (fun run => Multiplicative.ofAdd run.length)
    (mapRoute_comp earlier later path)

/-- A per-transition lower and upper bound applies to every retained path. -/
theorem mapRoute_length_bounds (realization : OperationalRealization source target)
    (lower upper : Nat)
    (perStep : ∀ {first last} (step : source.Step first last),
      lower ≤ (realization.mapStep step).length ∧
        (realization.mapStep step).length ≤ upper)
    {first last : source.Term} (path : ExecutionPath source first last) :
    lower * path.length ≤ (realization.mapRoute path).length ∧
      (realization.mapRoute path).length ≤ upper * path.length := by
  induction path with
  | refl => simp only [mapRoute, Route.length, Nat.mul_zero, le_refl, and_self]
  | cons step rest ih =>
      have bounds := perStep step.down
      have concatenation := Route.length_append (realization.mapStep step.down)
        (realization.mapRoute rest)
      change lower * (rest.length + 1) ≤
          ((realization.mapStep step.down).append (realization.mapRoute rest)).length ∧
        ((realization.mapStep step.down).append (realization.mapRoute rest)).length ≤
          upper * (rest.length + 1)
      rw [concatenation, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
      exact ⟨by omega, by omega⟩

/-- Constant expansion per selected primitive gives exact multiplicative cost. -/
theorem mapRoute_length_exact (realization : OperationalRealization source target)
    (factor : Nat)
    (perStep : ∀ {first last} (step : source.Step first last),
      (realization.mapStep step).length = factor)
    {first last : source.Term} (path : ExecutionPath source first last) :
    (realization.mapRoute path).length = factor * path.length := by
  have bounds := realization.mapRoute_length_bounds factor factor
    (fun step => ⟨Nat.le_of_eq (perStep step).symm, Nat.le_of_eq (perStep step)⟩) path
  exact Nat.le_antisymm bounds.2 bounds.1

end OperationalRealization

end Mettapedia.GSLT.IndexedOperational
