import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseViewModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceAdmission

/-!
# Clause guards depend on shared bindings and conditional row observations

Guard terms may already be evaluated in the model family while stored rows
retain their own captured declarations. This presentation separates the two
without changing absence, counts or the original world being observed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses ContextualClauseViewModels ContextualPrefixModels

variable {S : Signature} {Query Local Shared Next Extra O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

noncomputable def evaluatedRegion (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S next) Γ sort) : Finset O := by
  classical
  exact world.filter fun occurrence => Matches locals captures candidate pattern (rows occurrence)

def EvaluatedHolds (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (world : Finset O) :
    Check (Term (signature S next) Γ sort) → Prop
  | .equal first second => first = second
  | .absent pattern => ∀ occurrence ∈ world, ¬ Matches locals captures candidate pattern (rows occurrence)
  | .count pattern cardinality => (evaluatedRegion locals captures candidate rows world pattern).card = cardinality

theorem source_value (candidate : Assignment (family queries locals captures) next)
    (value : Term (signature S (queryFamily queries captures)) Γ sort) :
    instantiate candidate (queryView queries locals captures value) =
      instantiate (valuation queries captures (queryBodies queries locals captures candidate)
        (caller queries locals captures candidate)) value := by
  rw [queryView, ← Assignment.instantiate_compose, query_square]

theorem source_holds (candidate : Assignment (family queries locals captures) next)
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    ContextualConditionalGuards.Holds locals candidate
        (ContextualConditionalSourceAdmission.sourceRows queries locals captures rows) world
        (check.map (queryView queries locals captures)) ↔
      EvaluatedHolds locals captures (caller queries locals captures candidate) rows world
        (check.map (instantiate (valuation queries captures (queryBodies queries locals captures candidate)
          (caller queries locals captures candidate)))) := by
  cases check with
  | equal first second => simp only [Check.map, ContextualConditionalGuards.Holds, EvaluatedHolds, source_value]
  | absent pattern =>
      simp only [Check.map, ContextualConditionalGuards.Holds, EvaluatedHolds,
        ContextualConditionalSourceAdmission.sourceRows, matches_map_iff, captures_square, source_value]
  | count pattern cardinality =>
      have regions : ContextualConditionalGuards.region locals candidate
          (ContextualConditionalSourceAdmission.sourceRows queries locals captures rows) world
          (queryView queries locals captures pattern) =
        evaluatedRegion locals captures (caller queries locals captures candidate) rows world
          (instantiate (valuation queries captures (queryBodies queries locals captures candidate)
            (caller queries locals captures candidate)) pattern) := by
        classical
        ext occurrence
        simp only [ContextualConditionalGuards.mem_region, evaluatedRegion, Finset.mem_filter,
          ContextualConditionalSourceAdmission.sourceRows, matches_map_iff, captures_square, source_value]
      simp only [Check.map, ContextualConditionalGuards.Holds, EvaluatedHolds]
      rw [regions]

theorem evaluated_inclusion_iff (unused : Extra → MetaArity S) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S next) Γ sort)) :
    EvaluatedHolds locals captures (Assignment.compose (inclusion unused next) candidate) rows world
        (check.map (instantiate (inclusion unused next))) ↔
      EvaluatedHolds locals captures candidate rows world check := by
  cases check with
  | equal first second =>
      exact ⟨fun same => inclusion_injective unused next _ _ same, congrArg (instantiate (inclusion unused next))⟩
  | absent pattern =>
      simp only [Check.map, EvaluatedHolds, ContextualConditionalNaturality.matches_inclusion_iff]
  | count pattern cardinality =>
      have regions : evaluatedRegion locals captures (Assignment.compose (inclusion unused next) candidate)
          rows world (instantiate (inclusion unused next) pattern) =
        evaluatedRegion locals captures candidate rows world pattern := by
        classical
        ext occurrence
        simp only [evaluatedRegion, Finset.mem_filter, ContextualConditionalNaturality.matches_inclusion_iff]
      simp only [Check.map, EvaluatedHolds]
      rw [regions]

variable {Left Right : Type} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {frame : Extension captures}
    {leftRows : O → Row lefts captures Γ sort} {rightRows : O → Row rights frame.declarations Γ sort}
    (agree : RowsAgree lefts rights captures frame leftRows rightRows)

include agree

theorem matches_iff (candidate : Assignment frame.declarations next)
    (pattern : Term (signature S next) Γ sort) (occurrence : O) :
    Matches lefts captures (Assignment.compose candidate frame.assignment) pattern (leftRows occurrence) ↔
      Matches rights frame.declarations candidate pattern (rightRows occurrence) := by
  rw [ContextualConditionalRealizations.matches_iff, ContextualConditionalRealizations.matches_iff]
  apply exists_congr
  intro extension
  simpa only [Assignment.compose_associative] using
    agree _ extension.declarations (Assignment.compose extension.assignment candidate)
      (instantiate extension.assignment pattern) occurrence

theorem evaluated_iff (candidate : Assignment frame.declarations next) (world : Finset O)
    (check : Check (Term (signature S next) Γ sort)) :
    EvaluatedHolds lefts captures (Assignment.compose candidate frame.assignment) leftRows world check ↔
      EvaluatedHolds rights frame.declarations candidate rightRows world check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern => simp only [EvaluatedHolds, matches_iff captures agree]
  | count pattern cardinality =>
      have regions : evaluatedRegion lefts captures (Assignment.compose candidate frame.assignment)
          leftRows world pattern = evaluatedRegion rights frame.declarations candidate rightRows world pattern := by
        classical
        ext occurrence
        simp only [evaluatedRegion, Finset.mem_filter, matches_iff captures agree]
      simp only [EvaluatedHolds]
      rw [regions]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews
