import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses

/-!
# Subsequent clause models across a capture frame

Simultaneous row realizations preserve the query's shared assignment.
Private row banks may differ. The capture extension supplies a conservative
future for the forward comparison; unused private arities are supplied by
explicit assignments into actual captured declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseViewModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses ContextualPrefixModels

variable {S : Signature} {Query Left Right Shared Next O : Type}
    (queries : Query → MetaArity S) (lefts : Left → MetaArity S)
    (rights : Right → MetaArity S) (captures : Shared → MetaArity S)
    (frame : Extension captures) {Γ : Ctx S} {sort : S.Srt}

def RowsAgree (leftRows : O → Row lefts captures Γ sort)
    (rightRows : O → Row rights frame.declarations Γ sort) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S)
    (candidate : Assignment frame.declarations future)
    (pattern : Term (signature S future) Γ sort) (occurrence : O),
      Realizes lefts captures (Assignment.compose candidate frame.assignment) pattern (leftRows occurrence) ↔
        Realizes rights frame.declarations candidate pattern (rightRows occurrence)

def mappedRule (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort)) :=
  code.map (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment))

theorem mapped_value {next : Next → MetaArity S} (query : Assignment queries next)
    (candidate : Assignment frame.declarations next)
    (value : Term (signature S (queryFamily queries captures)) Γ sort) :
    instantiate (valuation queries frame.declarations query candidate)
      (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment) value) =
    instantiate (valuation queries captures query (Assignment.compose candidate frame.assignment)) value := by
  rw [← Assignment.instantiate_compose, valuation_capture_map]

theorem lifted_value {next : Next → MetaArity S} (query : Assignment queries next)
    (candidate : Assignment captures next)
    (value : Term (signature S (queryFamily queries captures)) Γ sort) :
    instantiate (valuation queries frame.declarations
      (Assignment.compose (inclusion frame.complementDeclarations next) query) (frame.liftModel candidate))
      (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment) value) =
    instantiate (inclusion frame.complementDeclarations next)
      (instantiate (valuation queries captures query candidate) value) := by
  rw [mapped_value, frame.liftModel_square, valuation_future, Assignment.instantiate_compose]

variable {queries lefts rights captures frame}
    {picked : Selection O}
    {code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort)}
    {leftRows : O → Row lefts captures Γ sort} {rightRows : O → Row rights frame.declarations Γ sort}
    {before : ContextualResidual.Problem captures}
    {takeShape : code.take.length = picked.taken.length} {readShape : code.read.length = picked.read.length}
    (agree : RowsAgree lefts rights captures frame leftRows rightRows)

include agree

theorem witness_to_left {next : Next → MetaArity S}
    (provider : Assignment lefts frame.declarations)
    (witness : Witness queries rights frame.declarations picked (mappedRule queries captures frame code) rightRows
      (ContextualResidual.mapProblem frame.assignment before)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using takeShape)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using readShape) next) :
    ∃ translated : Witness queries lefts captures picked code leftRows before takeShape readShape next,
      translated.query = witness.query ∧ translated.capture = Assignment.compose witness.capture frame.assignment := by
  refine ⟨⟨witness.query, Assignment.compose witness.capture frame.assignment,
    Assignment.compose witness.capture provider,
    (ContextualResidual.models_mapProblem _ _ _).mp witness.previous, ?_, ?_, ?_⟩, rfl, rfl⟩
  · have tells := (ContextualFrameUnifier.models_mapProblem _ _ _).mp witness.tells
    rwa [valuation_capture_map] at tells
  · intro port
    apply (agree _ next witness.capture _ (picked.taken.get port)).mpr
    have row := witness.taken port
    change Realizes _ _ _ (instantiate _ ((code.take.map _).get
      ⟨port.val, by simpa only [List.length_map, takeShape] using port.isLt⟩)) _ at row
    erw [List.get_eq_getElem, List.getElem_map] at row
    erw [mapped_value] at row
    exact row
  · intro port
    apply (agree _ next witness.capture _ (picked.read.get port)).mpr
    have row := witness.read port
    change Realizes _ _ _ (instantiate _ ((code.read.map _).get
      ⟨port.val, by simpa only [List.length_map, readShape] using port.isLt⟩)) _ at row
    erw [List.get_eq_getElem, List.getElem_map] at row
    erw [mapped_value] at row
    exact row

theorem witness_to_right {next : Next → MetaArity S}
    (provider : Assignment rights frame.declarations)
    (witness : Witness queries lefts captures picked code leftRows before takeShape readShape next) :
    ∃ translated : Witness queries rights frame.declarations picked (mappedRule queries captures frame code) rightRows
      (ContextualResidual.mapProblem frame.assignment before)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using takeShape)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using readShape)
      (extended frame.complementDeclarations next),
      translated.query = Assignment.compose (inclusion frame.complementDeclarations next) witness.query ∧
      translated.capture = frame.liftModel witness.capture := by
  refine ⟨⟨Assignment.compose (inclusion frame.complementDeclarations next) witness.query,
    frame.liftModel witness.capture, Assignment.compose (frame.liftModel witness.capture) provider,
    (ContextualConditionalNaturality.models_liftModel_iff frame witness.capture before).mpr witness.previous,
    ?_, ?_, ?_⟩, rfl, rfl⟩
  · apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
    rw [valuation_capture_map, frame.liftModel_square, valuation_future]
    exact ContextualFrameUnifier.models_compose witness.tells (inclusion frame.complementDeclarations next)
  · intro port
    change Realizes _ _ _ (instantiate _ ((code.take.map _).get
      ⟨port.val, by simpa only [List.length_map, takeShape] using port.isLt⟩)) _
    erw [List.get_eq_getElem, List.getElem_map]
    erw [lifted_value]
    apply (agree _ _ (frame.liftModel witness.capture) _ (picked.taken.get port)).mp
    rw [frame.liftModel_square]
    exact (witness.taken port).future lefts captures (inclusion frame.complementDeclarations next)
  · intro port
    change Realizes _ _ _ (instantiate _ ((code.read.map _).get
      ⟨port.val, by simpa only [List.length_map, readShape] using port.isLt⟩)) _
    erw [List.get_eq_getElem, List.getElem_map]
    erw [lifted_value]
    apply (agree _ _ (frame.liftModel witness.capture) _ (picked.read.get port)).mp
    rw [frame.liftModel_square]
    exact (witness.read port).future lefts captures (inclusion frame.complementDeclarations next)

theorem solvable_iff (leftProvider : Assignment lefts frame.declarations)
    (rightProvider : Assignment rights frame.declarations)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length) :
    ContextualConditionalExecution.Solvable
      (ContextualConditionalSourceProblem.problem queries rights frame.declarations picked
        (mappedRule queries captures frame code) rightRows (ContextualResidual.mapProblem frame.assignment before)) ↔
    ContextualConditionalExecution.Solvable
      (ContextualConditionalSourceProblem.problem queries lefts captures picked code leftRows before) := by
  rw [ContextualClauseWitnesses.solvable_iff queries rights frame.declarations picked _ _ _
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using takeShape)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using readShape),
    ContextualClauseWitnesses.solvable_iff queries lefts captures picked _ _ _ takeShape readShape]
  constructor
  · rintro ⟨Future, future, ⟨witness⟩⟩
    obtain ⟨translated, _, _⟩ := witness_to_left agree leftProvider witness
    exact ⟨Future, future, ⟨translated⟩⟩
  · rintro ⟨Future, future, ⟨witness⟩⟩
    obtain ⟨translated, _, _⟩ := witness_to_right agree rightProvider witness
    exact ⟨_, _, ⟨translated⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseViewModels
