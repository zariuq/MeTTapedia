import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAsks

/-!
# Information in a contextual interaction

Equality belongs to the declared term interpretation. A store records
constraints; refinement restricts its solutions, and asks observe every
future-family solution without adding a constraint. Representation changes
must preserve those future solutions, not just one returned assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S}
  {Γ : Ctx S} {sort : S.Srt}

/-- The information obligation of a selected firing retains its whole guard list. -/
structure Admitted
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (checks : List (Check (Term (signature S captures) Γ sort))) : Prop where
  solvable : ContextualFrameUnifier.Solvable problem
  checks : ∀ check ∈ checks, ContextualGuardSemantics.Ask locals problem rows world check

/-- A stronger contextual store admits no new solutions in any later frame. -/
def Refines (stronger weaker : EquationStore (Term (signature S captures) Γ sort)) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future),
    ContextualFrameUnifier.Models candidate stronger → ContextualFrameUnifier.Models candidate weaker

def Equivalent (first second : EquationStore (Term (signature S captures) Γ sort)) : Prop :=
  Refines first second ∧ Refines second first

theorem refines_refl (problem : EquationStore (Term (signature S captures) Γ sort)) :
    Refines problem problem := fun _ _ _ model => model

theorem refines_trans {first second third : EquationStore (Term (signature S captures) Γ sort)}
    (one : Refines first second) (two : Refines second third) : Refines first third :=
  fun future declarations candidate model => two future declarations candidate
    (one future declarations candidate model)

theorem append_refines (problem extra : EquationStore (Term (signature S captures) Γ sort)) :
    Refines (problem ++ extra) problem := by
  intro Future future candidate model
  exact ((ContextualFrameUnifier.models_append candidate problem extra).mp model).1

theorem equivalent_append {first second : EquationStore (Term (signature S captures) Γ sort)}
    (same : Equivalent first second) (extra : EquationStore (Term (signature S captures) Γ sort)) :
    Equivalent (first ++ extra) (second ++ extra) := by
  constructor
  · intro Future future candidate model
    obtain ⟨old, added⟩ := (ContextualFrameUnifier.models_append candidate first extra).mp model
    exact (ContextualFrameUnifier.models_append candidate second extra).mpr
      ⟨same.1 Future future candidate old, added⟩
  · intro Future future candidate model
    obtain ⟨old, added⟩ := (ContextualFrameUnifier.models_append candidate second extra).mp model
    exact (ContextualFrameUnifier.models_append candidate first extra).mpr
      ⟨same.2 Future future candidate old, added⟩

theorem tells_idempotent (problem extra : EquationStore (Term (signature S captures) Γ sort)) :
    Equivalent ((problem ++ extra) ++ extra) (problem ++ extra) := by
  refine ⟨append_refines _ _, ?_⟩
  intro Future future candidate model
  exact (ContextualFrameUnifier.models_append candidate (problem ++ extra) extra).mpr
    ⟨model, ((ContextualFrameUnifier.models_append candidate problem extra).mp model).2⟩

theorem tells_commute (problem first second : EquationStore (Term (signature S captures) Γ sort)) :
    Equivalent ((problem ++ first) ++ second) ((problem ++ second) ++ first) := by
  constructor <;> intro Future future candidate model
  · obtain ⟨⟨old, left⟩, right⟩ :=
      (and_congr_left (fun _ => ContextualFrameUnifier.models_append candidate problem first)).mp
        ((ContextualFrameUnifier.models_append candidate (problem ++ first) second).mp model)
    exact (ContextualFrameUnifier.models_append candidate (problem ++ second) first).mpr
      ⟨(ContextualFrameUnifier.models_append candidate problem second).mpr ⟨old, right⟩, left⟩
  · obtain ⟨⟨old, right⟩, left⟩ :=
      (and_congr_left (fun _ => ContextualFrameUnifier.models_append candidate problem second)).mp
        ((ContextualFrameUnifier.models_append candidate (problem ++ second) first).mp model)
    exact (ContextualFrameUnifier.models_append candidate (problem ++ first) second).mpr
      ⟨(ContextualFrameUnifier.models_append candidate problem first).mpr ⟨old, left⟩, right⟩

theorem ask_of_refines {first second : EquationStore (Term (signature S captures) Γ sort)}
    (refinement : Refines first second)
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {check : Check (Term (signature S captures) Γ sort)}
    (asked : ContextualGuardSemantics.Ask locals second rows world check) :
    ContextualGuardSemantics.Ask locals first rows world check :=
  fun Future future candidate model => asked Future future candidate
    (refinement Future future candidate model)

theorem admitted_refinement {first second : EquationStore (Term (signature S captures) Γ sort)}
    (refinement : Refines first second)
    (solvable : ContextualFrameUnifier.Solvable first)
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {checks : List (Check (Term (signature S captures) Γ sort))}
    (admitted : Admitted locals second rows world checks) : Admitted locals first rows world checks :=
  ⟨solvable, fun check member => ask_of_refines locals refinement (admitted.checks check member)⟩

theorem admitted_equivalent {first second : EquationStore (Term (signature S captures) Γ sort)}
    (same : Equivalent first second)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (checks : List (Check (Term (signature S captures) Γ sort))) :
    Admitted locals first rows world checks ↔ Admitted locals second rows world checks := by
  constructor
  · intro admitted
    obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
    exact ⟨⟨Future, future, candidate, same.1 Future future candidate model⟩,
      fun check member => ask_of_refines locals same.2 (admitted.checks check member)⟩
  · intro admitted
    obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
    exact ⟨⟨Future, future, candidate, same.2 Future future candidate model⟩,
      fun check member => ask_of_refines locals same.1 (admitted.checks check member)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation
