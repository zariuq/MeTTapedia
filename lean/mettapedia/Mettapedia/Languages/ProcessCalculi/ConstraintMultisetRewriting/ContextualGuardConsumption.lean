import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep

/-!
# Selected schema instances justify exact absence transport

A model of an actual opening supplies a local guard witness without changing
its captures. If a selected equation guarantees a row matches, asking for
absence after that physical row is erased is exactly asking for count one
before its consumption. The equation store remains in both conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardConsumption

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualActivatedStep
open ContextualGuardMatching
open ContextualGuardSemantics

universe u
variable {S : Signature} {Local Shared Next : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S) {next : Next → MetaArity S}

theorem opened_view_matches (scope : Nat) (candidate : Assignment (target locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualStoredRows.Row locals captures Γ sort) :
    Matches locals candidate
      (instantiate candidate (ContextualFreshening.termAt locals captures scope
        (ContextualStoredRows.asTemplate locals captures row)))
      (row.map locals (ContextualSelectionViews.capturedTarget locals captures)) := by
  cases row with
  | shared value =>
      exact congrArg (instantiate candidate)
        (ContextualStoredRows.viewAt_eq_freshening locals captures scope (.shared value)).symm
  | schema body =>
      let localBodies : Assignment locals next :=
        fun identity => candidate (.inl (ScopedVar.at scope identity))
      have components : instanceAssignment locals localBodies (generator next)
          (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) =
          Assignment.compose candidate (ContextualFreshening.assignment locals captures scope) := by
        funext identity
        cases identity with
        | inl identity => exact (instantiate_generator candidate (.inl (ScopedVar.at scope identity))).symm
        | inr identity =>
            change instantiate (generator next)
                (instantiate candidate (generator (target locals captures) (.inr identity))) =
              instantiate candidate (generator (target locals captures) (.inr identity))
            exact instantiate_identity _
      refine ⟨Extension.identity next, localBodies, ?_⟩
      change instantiate (instanceAssignment locals localBodies (generator next) candidate)
          (instantiate (ContextualStoredRows.liftCaptures locals
            (ContextualSelectionViews.capturedTarget locals captures)) body) =
        instantiate (generator next)
          (instantiate candidate (ContextualFreshening.termAt locals captures scope body))
      rw [instantiate_identity, instantiated_transported_body, components]
      exact Assignment.instantiate_compose candidate (ContextualFreshening.assignment locals captures scope) body

theorem selected_equation_matches (scope : Nat) (candidate : Assignment (target locals captures) next)
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S (target locals captures)) Γ sort))
    (row : ContextualStoredRows.Row locals captures Γ sort)
    (pattern : Term (signature S (target locals captures)) Γ sort)
    (selected : (pattern, ContextualFreshening.termAt locals captures scope
      (ContextualStoredRows.asTemplate locals captures row)) ∈ problem)
    (solved : ContextualFrameUnifier.Models candidate problem) :
    Matches locals candidate (instantiate candidate pattern)
      (row.map locals (ContextualSelectionViews.capturedTarget locals captures)) := by
  have same := solved _ selected
  exact Eq.mpr (congrArg (fun value => Matches locals candidate value
    (row.map locals (ContextualSelectionViews.capturedTarget locals captures))) same)
    (opened_view_matches locals captures scope candidate row)

theorem ask_after_erase_iff_exact_count [DecidableEq O]
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S (target locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S (target locals captures)) Γ sort) (occurrence : O) (scope : Nat)
    (present : occurrence ∈ world)
    (selected : (pattern, ContextualFreshening.termAt locals captures scope
      (ContextualStoredRows.asTemplate locals captures (rows occurrence))) ∈ problem) :
    Ask locals problem (ContextualGuardedStep.guardRows locals captures rows)
        (world.erase occurrence) (.absent pattern) ↔
      Ask locals problem (ContextualGuardedStep.guardRows locals captures rows) world (.count pattern 1) := by
  constructor
  · intro admitted Later later candidate solved
    exact (absent_after_erase_iff_count_one locals candidate
      (ContextualGuardedStep.guardRows locals captures rows) world pattern occurrence present
      (selected_equation_matches locals captures scope candidate problem (rows occurrence) pattern selected solved)).mp
      (admitted Later later candidate solved)
  · intro admitted Later later candidate solved
    exact (absent_after_erase_iff_count_one locals candidate
      (ContextualGuardedStep.guardRows locals captures rows) world pattern occurrence present
      (selected_equation_matches locals captures scope candidate problem (rows occurrence) pattern selected solved)).mpr
      (admitted Later later candidate solved)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardConsumption
