import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualMatchedClauseModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews

/-!
# Complete clause models transfer through exposed world environments

The authored rule uses one exposed environment. Each world supplies its
own interpretation of those captures. Model transfer preserves the shared
query assignment and the related old-world interpretation, while fresh
row witnesses remain private to each port.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses

variable {S : Signature} {Public Query Left Right O Next : Type}
    {exposed : Public → MetaArity S} (queries : Query → MetaArity S)
    {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

def preparedRule {V : Type} {declaration : V → MetaArity S}
    (environment : Assignment exposed declaration)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort)) :=
  code.map (instantiate (ContextualStoredRows.liftCaptures queries environment))

def preparedPlan {V : Type} {declaration : V → MetaArity S}
    (environment : Assignment exposed declaration)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort)) :
    ContextualPublication.Plan (Term (signature S (queryFamily queries declaration)) Γ sort) :=
  ⟨preparedRule queries environment plan.rule, plan.reusable, by
    change plan.reusable.length = (plan.rule.produce.map _).length
    rw [List.length_map]
    exact plan.shape⟩

variable {queries} {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualClauseSourceState.World rights O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}
    {next : Next → MetaArity S} {leftModel : Assignment left.declarations next}
    {rightModel : Assignment right.declarations next}

theorem Related.clause_value (related : Related left leftEnv right rightEnv leftModel rightModel)
    (queries : Query → MetaArity S) (query : Assignment queries next)
    (value : Term (signature S (queryFamily queries exposed)) Γ sort) :
    instantiate (valuation queries right.declarations query rightModel)
        (instantiate (ContextualStoredRows.liftCaptures queries rightEnv) value) =
      instantiate (valuation queries left.declarations query leftModel)
        (instantiate (ContextualStoredRows.liftCaptures queries leftEnv) value) := by
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    valuation_capture_map, valuation_capture_map, related.bindings]

theorem transfer_clause_model [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort))
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (takePresent : picked.taken.toFinset ⊆ left.present) (readPresent : picked.read.toFinset ⊆ left.present)
    (candidate : Assignment (family queries lefts left.declarations) next)
    (model : ContextualResidual.Models candidate
      (ContextualConditionalSourceProblem.problem queries lefts left.declarations picked
        (preparedRule queries leftEnv code) left.rows left.equations)) :
    ∃ extension : Extension next, ∃ other : Assignment (family queries rights right.declarations) extension.declarations,
      ContextualResidual.Models other
        (ContextualConditionalSourceProblem.problem queries rights right.declarations picked
          (preparedRule queries rightEnv code) right.rows right.equations) ∧
      Related left leftEnv right rightEnv
        (Assignment.compose extension.assignment (caller queries lefts left.declarations candidate))
        (caller queries rights right.declarations other) ∧
      queryBodies queries rights right.declarations other =
        Assignment.compose extension.assignment (queryBodies queries lefts left.declarations candidate) := by
  let witness := witness_of_model queries lefts left.declarations picked (preparedRule queries leftEnv code)
    left.rows left.equations
    (by simpa only [preparedRule, RuleInstance.map, List.length_map] using takeShape)
    (by simpa only [preparedRule, RuleInstance.map, List.length_map] using readShape) candidate model
  obtain ⟨earlier, rightModel, related⟩ := equivalent.forward _ next witness.capture witness.previous
  let query := Assignment.compose earlier.assignment witness.query
  have tells : ContextualFrameUnifier.Models (valuation queries right.declarations query rightModel)
      (preparedRule queries rightEnv code).tell := by
    have leftTells := ContextualFrameUnifier.models_compose witness.tells earlier.assignment
    rw [← valuation_future] at leftTells
    change ContextualFrameUnifier.Models (valuation queries left.declarations query
      (Assignment.compose earlier.assignment witness.capture))
      (ContextualFrameUnifier.mapProblem (ContextualStoredRows.liftCaptures queries leftEnv) code.tell) at leftTells
    rw [ContextualFrameUnifier.models_mapProblem, valuation_capture_map] at leftTells
    change ContextualFrameUnifier.Models (valuation queries right.declarations query rightModel)
      (ContextualFrameUnifier.mapProblem (ContextualStoredRows.liftCaptures queries rightEnv) code.tell)
    rw [ContextualFrameUnifier.models_mapProblem, valuation_capture_map, ← related.bindings]
    exact leftTells
  have taken : ∀ port : Fin picked.taken.length, Matches rights right.declarations rightModel
      (instantiate (valuation queries right.declarations query rightModel)
        ((preparedRule queries rightEnv code).take.get
          ⟨port.val, by simpa only [preparedRule, RuleInstance.map, List.length_map, takeShape] using port.isLt⟩))
      (right.rows (picked.taken.get port)) := by
    intro port
    change Matches _ _ _ (instantiate _ ((code.take.map _).get
      ⟨port.val, by simpa only [List.length_map, takeShape] using port.isLt⟩)) _
    erw [List.get_eq_getElem, List.getElem_map, related.clause_value queries query]
    apply (related.current_rows _ _ (takePresent (List.mem_toFinset.mpr (List.get_mem _ _)))).mp
    change Matches _ _ _ (instantiate
      (valuation queries left.declarations (Assignment.compose earlier.assignment witness.query)
        (Assignment.compose earlier.assignment witness.capture)) _) _
    rw [valuation_future, Assignment.instantiate_compose]
    have row := (witness.taken port).matches lefts left.declarations
    change Matches _ _ _ (instantiate _ ((code.take.map _).get
      ⟨port.val, by simpa only [List.length_map, takeShape] using port.isLt⟩)) _ at row
    erw [List.get_eq_getElem, List.getElem_map] at row
    exact (matches_extension_iff lefts left.declarations earlier _ _ _).mpr row
  have read : ∀ port : Fin picked.read.length, Matches rights right.declarations rightModel
      (instantiate (valuation queries right.declarations query rightModel)
        ((preparedRule queries rightEnv code).read.get
          ⟨port.val, by simpa only [preparedRule, RuleInstance.map, List.length_map, readShape] using port.isLt⟩))
      (right.rows (picked.read.get port)) := by
    intro port
    change Matches _ _ _ (instantiate _ ((code.read.map _).get
      ⟨port.val, by simpa only [List.length_map, readShape] using port.isLt⟩)) _
    erw [List.get_eq_getElem, List.getElem_map, related.clause_value queries query]
    apply (related.current_rows _ _ (readPresent (List.mem_toFinset.mpr (List.get_mem _ _)))).mp
    change Matches _ _ _ (instantiate
      (valuation queries left.declarations (Assignment.compose earlier.assignment witness.query)
        (Assignment.compose earlier.assignment witness.capture)) _) _
    rw [valuation_future, Assignment.instantiate_compose]
    have row := (witness.read port).matches lefts left.declarations
    change Matches _ _ _ (instantiate _ ((code.read.map _).get
      ⟨port.val, by simpa only [List.length_map, readShape] using port.isLt⟩)) _ at row
    erw [List.get_eq_getElem, List.getElem_map] at row
    exact (matches_extension_iff lefts left.declarations earlier _ _ _).mpr row
  obtain ⟨later, other, solved, queryFixed, capturesFixed⟩ :=
    ContextualMatchedClauseModels.model_from_matches queries rights right.declarations picked
      (preparedRule queries rightEnv code) right.rows right.equations
      (by simpa only [preparedRule, RuleInstance.map, List.length_map] using takeShape)
      (by simpa only [preparedRule, RuleInstance.map, List.length_map] using readShape)
      query rightModel related.right_model tells taken read
  refine ⟨earlier.trans later, other, solved, ?_, ?_⟩
  · erw [capturesFixed]
    erw [Extension.trans_assignment, ← Assignment.compose_associative]
    exact related.future later
  · erw [Extension.trans_assignment, ← Assignment.compose_associative]
    exact queryFixed

theorem transferred_value (queries : Query → MetaArity S) (extension : Extension next)
    (first : Assignment (family queries lefts left.declarations) next)
    (second : Assignment (family queries rights right.declarations) extension.declarations)
    (related : Related left leftEnv right rightEnv
      (Assignment.compose extension.assignment (caller queries lefts left.declarations first))
      (caller queries rights right.declarations second))
    (queryEqual : queryBodies queries rights right.declarations second =
      Assignment.compose extension.assignment (queryBodies queries lefts left.declarations first))
    (value : Term (signature S (queryFamily queries exposed)) Γ sort) :
    instantiate second (queryView queries rights right.declarations
        (instantiate (ContextualStoredRows.liftCaptures queries rightEnv) value)) =
      instantiate extension.assignment (instantiate first (queryView queries lefts left.declarations
        (instantiate (ContextualStoredRows.liftCaptures queries leftEnv) value))) := by
  erw [ContextualClauseGuardViews.source_value, queryEqual, related.clause_value queries _,
    valuation_future, Assignment.instantiate_compose]
  rw [ContextualClauseGuardViews.source_value]

theorem clause_instances_forward [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort))
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (takePresent : picked.taken.toFinset ⊆ left.present) (readPresent : picked.read.toFinset ⊆ left.present)
    (value : Term (signature S (queryFamily queries exposed)) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances
        (ContextualConditionalSourceProblem.problem queries lefts left.declarations picked
          (preparedRule queries leftEnv code) left.rows left.equations)
        (queryView queries lefts left.declarations
          (instantiate (ContextualStoredRows.liftCaptures queries leftEnv) value)) next pattern →
      ContextualPublication.SourceInstances
        (ContextualConditionalSourceProblem.problem queries rights right.declarations picked
          (preparedRule queries rightEnv code) right.rows right.equations)
        (queryView queries rights right.declarations
          (instantiate (ContextualStoredRows.liftCaptures queries rightEnv) value)) next pattern := by
  rintro ⟨earlier, candidate, model, same⟩
  obtain ⟨later, other, solved, related, queryEqual⟩ := transfer_clause_model equivalent queries picked code
    takeShape readShape takePresent readPresent candidate model
  refine ⟨earlier.trans later, other, solved, ?_⟩
  erw [Extension.trans_assignment, Assignment.instantiate_compose]
  exact (transferred_value queries later candidate other related queryEqual value).trans
    (congrArg (instantiate later.assignment) same)

theorem clause_instances_iff [DecidableEq O] (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries exposed)) Γ sort))
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (takePresent : picked.taken.toFinset ⊆ left.present) (readPresent : picked.read.toFinset ⊆ left.present)
    (value : Term (signature S (queryFamily queries exposed)) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances
        (ContextualConditionalSourceProblem.problem queries rights right.declarations picked
          (preparedRule queries rightEnv code) right.rows right.equations)
        (queryView queries rights right.declarations
          (instantiate (ContextualStoredRows.liftCaptures queries rightEnv) value)) next pattern ↔
      ContextualPublication.SourceInstances
        (ContextualConditionalSourceProblem.problem queries lefts left.declarations picked
          (preparedRule queries leftEnv code) left.rows left.equations)
        (queryView queries lefts left.declarations
          (instantiate (ContextualStoredRows.liftCaptures queries leftEnv) value)) next pattern := by
  constructor
  · exact clause_instances_forward equivalent.symm queries picked code takeShape readShape
      (by rwa [← equivalent.physical]) (by rwa [← equivalent.physical]) value pattern
  · exact clause_instances_forward equivalent queries picked code takeShape readShape takePresent readPresent value pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
