import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldClauseModels

/-!
# Source clause admission depends on exposed world observations

All-future guards are transferred at the original world, using joint model
coverage and conditional row agreement. Fresh extensions preserve both
positive matches and their absence, so coverage does not weaken a negative
guard or identify an unfinished search with a negative answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows ContextualConditionalRealizations

variable {S : Signature} {Local Shared Next O : Type} (locals : Local → MetaArity S)
    (captures : Shared → MetaArity S) {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem evaluated_extension_iff (extension : Extension next) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S next) Γ sort)) :
    EvaluatedHolds locals captures (Assignment.compose extension.assignment candidate) rows world
        (check.map (instantiate extension.assignment)) ↔ EvaluatedHolds locals captures candidate rows world check := by
  cases check with
  | equal first second =>
      exact ⟨fun same => extension.instantiate_injective same, congrArg (instantiate extension.assignment)⟩
  | absent pattern => simp only [Check.map, EvaluatedHolds, matches_extension_iff]
  | count pattern cardinality =>
      have regions : evaluatedRegion locals captures (Assignment.compose extension.assignment candidate) rows world
          (instantiate extension.assignment pattern) = evaluatedRegion locals captures candidate rows world pattern := by
        classical
        ext occurrence
        simp only [evaluatedRegion, Finset.mem_filter, matches_extension_iff]
      simp only [Check.map, EvaluatedHolds]
      rw [regions]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses ContextualClauseGuardViews

variable {S : Signature} {Public Query Left Right O Next : Type}
    {exposed : Public → MetaArity S} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualClauseSourceState.World rights O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}
    {next : Next → MetaArity S} {leftModel : Assignment left.declarations next}
    {rightModel : Assignment right.declarations next}

theorem Related.evaluated_iff (related : Related left leftEnv right rightEnv leftModel rightModel)
    (physical : left.present = right.present) (check : Check (Term (signature S next) Γ sort)) :
    EvaluatedHolds lefts left.declarations leftModel left.rows left.present check ↔
      EvaluatedHolds rights right.declarations rightModel right.rows right.present check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern =>
      constructor
      · intro absent occurrence member matched
        have present : occurrence ∈ left.present := by rwa [physical]
        exact absent occurrence present ((related.current_rows pattern occurrence present).mpr matched)
      · intro absent occurrence member matched
        exact absent occurrence (by rwa [← physical]) ((related.current_rows pattern occurrence member).mp matched)
  | count pattern cardinality =>
      have regions : evaluatedRegion lefts left.declarations leftModel left.rows left.present pattern =
          evaluatedRegion rights right.declarations rightModel right.rows right.present pattern := by
        classical
        ext occurrence
        simp only [evaluatedRegion, Finset.mem_filter]
        constructor
        · rintro ⟨present, matched⟩
          exact ⟨by rwa [← physical], (related.current_rows pattern occurrence present).mp matched⟩
        · rintro ⟨present, matched⟩
          have member : occurrence ∈ left.present := by rwa [physical]
          exact ⟨member, (related.current_rows pattern occurrence member).mpr matched⟩
      simp only [EvaluatedHolds]
      rw [regions]

theorem Related.prepared_check (related : Related left leftEnv right rightEnv leftModel rightModel)
    (queries : Query → MetaArity S) (query : Assignment queries next)
    (check : Check (Term (signature S (queryFamily queries exposed)) Γ sort)) :
    (check.map (instantiate (ContextualStoredRows.liftCaptures queries rightEnv))).map
        (instantiate (valuation queries right.declarations query rightModel)) =
      (check.map (instantiate (ContextualStoredRows.liftCaptures queries leftEnv))).map
        (instantiate (valuation queries left.declarations query leftModel)) := by
  cases check <;> simp only [Check.map, related.clause_value queries query]

theorem check_future (queries : Query → MetaArity S) (query : Assignment queries next)
    (candidate : Assignment left.declarations next) (extension : Extension next)
    (check : Check (Term (signature S (queryFamily queries exposed)) Γ sort)) :
    (check.map (instantiate (ContextualStoredRows.liftCaptures queries leftEnv))).map
        (instantiate (valuation queries left.declarations (Assignment.compose extension.assignment query)
          (Assignment.compose extension.assignment candidate))) =
      ((check.map (instantiate (ContextualStoredRows.liftCaptures queries leftEnv))).map
        (instantiate (valuation queries left.declarations query candidate))).map (instantiate extension.assignment) := by
  cases check <;> simp only [Check.map, valuation_future, Assignment.instantiate_compose]

theorem asks_forward [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort))
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (takePresent : picked.taken.toFinset ⊆ left.present) (readPresent : picked.read.toFinset ⊆ left.present)
    (check : Check (Term (signature S (queryFamily queries exposed)) Γ sort))
    (asked : ContextualConditionalGuards.Ask lefts
      (ContextualConditionalSourceProblem.problem queries lefts left.declarations picked
        (preparedRule queries leftEnv code) left.rows left.equations)
      (ContextualConditionalSourceAdmission.sourceRows queries lefts left.declarations left.rows) left.present
      ((check.map (instantiate (ContextualStoredRows.liftCaptures queries leftEnv))).map
        (queryView queries lefts left.declarations))) :
    ContextualConditionalGuards.Ask rights
      (ContextualConditionalSourceProblem.problem queries rights right.declarations picked
        (preparedRule queries rightEnv code) right.rows right.equations)
      (ContextualConditionalSourceAdmission.sourceRows queries rights right.declarations right.rows) right.present
      ((check.map (instantiate (ContextualStoredRows.liftCaptures queries rightEnv))).map
        (queryView queries rights right.declarations)) := by
  intro Future future candidate model
  obtain ⟨extension, other, solved, related, queryEqual⟩ := transfer_clause_model equivalent.symm queries picked code
    takeShape readShape (by rwa [← equivalent.physical]) (by rwa [← equivalent.physical]) candidate model
  have held := (source_holds queries lefts left.declarations other left.rows left.present _).mp
    (asked _ _ other solved)
  rw [queryEqual, related.prepared_check queries _] at held
  have extended := (related.evaluated_iff equivalent.physical.symm _).mpr held
  rw [check_future] at extended
  have original := (evaluated_extension_iff rights right.declarations extension _ right.rows right.present _).mp extended
  exact (source_holds queries rights right.declarations candidate right.rows right.present _).mpr original

theorem admitted_forward [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort))
    (admitted : ContextualConditionalSourceAdmission.Admitted queries lefts left.declarations picked
      (preparedRule queries leftEnv code) left.rows left.equations left.present) :
    ContextualConditionalSourceAdmission.Admitted queries rights right.declarations picked
      (preparedRule queries rightEnv code) right.rows right.equations right.present := by
  have takeShape : code.take.length = picked.taken.length := by
    simpa only [preparedRule, RuleInstance.map, List.length_map] using admitted.take_shape
  have readShape : code.read.length = picked.read.length := by
    simpa only [preparedRule, RuleInstance.map, List.length_map] using admitted.read_shape
  refine ⟨admitted.take_distinct, admitted.output_distinct, ?_, ?_, ?_,
    (by rw [← equivalent.physical]; exact admitted.taken_present),
    (by rw [← equivalent.physical]; exact admitted.read_present), admitted.apart,
    (by rw [← equivalent.physical]; exact admitted.fresh), ?_, ?_⟩
  · simpa only [preparedRule, RuleInstance.map, List.length_map] using takeShape
  · simpa only [preparedRule, RuleInstance.map, List.length_map] using readShape
  · simpa only [preparedRule, RuleInstance.map, List.length_map] using admitted.output_shape
  · obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
    obtain ⟨extension, other, solved, _, _⟩ := transfer_clause_model equivalent queries picked code
      takeShape readShape admitted.taken_present admitted.read_present candidate model
    exact ⟨_, extension.declarations, other, solved⟩
  · intro check member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact asks_forward equivalent queries picked code takeShape readShape admitted.taken_present admitted.read_present original
      (admitted.checks _ (List.mem_map.mpr ⟨original, present, rfl⟩))

theorem admitted_iff [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort)) :
    ContextualConditionalSourceAdmission.Admitted queries rights right.declarations picked
        (preparedRule queries rightEnv code) right.rows right.equations right.present ↔
      ContextualConditionalSourceAdmission.Admitted queries lefts left.declarations picked
        (preparedRule queries leftEnv code) left.rows left.equations left.present :=
  ⟨admitted_forward equivalent.symm queries picked code, admitted_forward equivalent queries picked code⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
