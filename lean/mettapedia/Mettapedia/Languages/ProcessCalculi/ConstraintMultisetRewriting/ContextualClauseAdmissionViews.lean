import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseGuardViews

/-!
# Subsequent clause admission is invariant under the state comparison

The comparison includes a joint model for every selected port and all
future models used by guards. It preserves physical selections and their
original observation world, rather than merely comparing isolated answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmissionViews

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses ContextualClauseViewModels
open ContextualClauseGuardViews ContextualPrefixModels

variable {S : Signature} {Query Left Right Shared Next O : Type}
    (queries : Query → MetaArity S) (captures : Shared → MetaArity S)
    (frame : Extension captures) {Γ : Ctx S} {sort : S.Srt}

theorem mapped_check {next : Next → MetaArity S} (query : Assignment queries next)
    (candidate : Assignment frame.declarations next)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    (check.map (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment))).map
        (instantiate (valuation queries frame.declarations query candidate)) =
      check.map (instantiate (valuation queries captures query (Assignment.compose candidate frame.assignment))) := by
  cases check <;> simp only [Check.map, mapped_value]

theorem lifted_check {next : Next → MetaArity S} (query : Assignment queries next)
    (candidate : Assignment captures next)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    (check.map (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment))).map
        (instantiate (valuation queries frame.declarations
          (Assignment.compose (inclusion frame.complementDeclarations next) query) (frame.liftModel candidate))) =
      (check.map (instantiate (valuation queries captures query candidate))).map
        (instantiate (inclusion frame.complementDeclarations next)) := by
  cases check <;> simp only [Check.map, lifted_value]

variable {queries captures frame}
    {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {leftRows : O → Row lefts captures Γ sort} {rightRows : O → Row rights frame.declarations Γ sort}
    {picked : Selection O} {code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort)}
    {before : ContextualResidual.Problem captures} {world : Finset O}
    (agree : RowsAgree lefts rights captures frame leftRows rightRows)

include agree

theorem ask_iff (leftProvider : Assignment lefts frame.declarations) (rightProvider : Assignment rights frame.declarations)
    (takeShape : code.take.length = picked.taken.length)
    (readShape : code.read.length = picked.read.length)
    (check : Check (Term (signature S (queryFamily queries captures)) Γ sort)) :
    ContextualConditionalGuards.Ask rights
        (ContextualConditionalSourceProblem.problem queries rights frame.declarations picked
          (mappedRule queries captures frame code) rightRows (ContextualResidual.mapProblem frame.assignment before))
        (ContextualConditionalSourceAdmission.sourceRows queries rights frame.declarations rightRows) world
        ((check.map (instantiate (ContextualStoredRows.liftCaptures queries frame.assignment))).map
          (queryView queries rights frame.declarations)) ↔
      ContextualConditionalGuards.Ask lefts
        (ContextualConditionalSourceProblem.problem queries lefts captures picked code leftRows before)
        (ContextualConditionalSourceAdmission.sourceRows queries lefts captures leftRows) world
        (check.map (queryView queries lefts captures)) := by
  constructor
  · intro asked Future future candidate model
    let witness := witness_of_model queries lefts captures picked code leftRows before takeShape readShape candidate model
    obtain ⟨translated, queryEqual, captureEqual⟩ := witness_to_right agree rightProvider witness
    obtain ⟨native, nativeModel, nativeQuery, nativeCapture⟩ := translated.gives_model queries rights frame.declarations
    have held := (source_holds queries rights frame.declarations native rightRows world _).mp
      (asked _ _ native nativeModel)
    rw [nativeQuery, nativeCapture, queryEqual, captureEqual, lifted_check] at held
    have source := (evaluated_iff captures agree (frame.liftModel witness.capture) world _).mpr held
    rw [frame.liftModel_square] at source
    have original := (evaluated_inclusion_iff lefts captures frame.complementDeclarations witness.capture
      leftRows world _).mp source
    exact (source_holds queries lefts captures candidate leftRows world check).mpr original
  · intro asked Future future candidate model
    let witness := witness_of_model queries rights frame.declarations picked (mappedRule queries captures frame code)
      rightRows (ContextualResidual.mapProblem frame.assignment before)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using takeShape)
      (by simpa only [mappedRule, RuleInstance.map, List.length_map] using readShape) candidate model
    obtain ⟨translated, queryEqual, captureEqual⟩ :=
      witness_to_left (takeShape := takeShape) (readShape := readShape) agree leftProvider witness
    obtain ⟨source, sourceModel, sourceQuery, sourceCapture⟩ := translated.gives_model queries lefts captures
    have held := (source_holds queries lefts captures source leftRows world check).mp
      (asked _ _ source sourceModel)
    rw [sourceQuery, sourceCapture, queryEqual, captureEqual] at held
    have native := (evaluated_iff captures agree witness.capture world _).mp held
    apply (source_holds queries rights frame.declarations candidate rightRows world _).mpr
    rw [mapped_check]
    exact native

theorem admitted_iff (leftProvider : Assignment lefts frame.declarations) (rightProvider : Assignment rights frame.declarations)
    [DecidableEq O] :
    ContextualConditionalSourceAdmission.Admitted queries rights frame.declarations picked
        (mappedRule queries captures frame code) rightRows (ContextualResidual.mapProblem frame.assignment before) world ↔
      ContextualConditionalSourceAdmission.Admitted queries lefts captures picked code leftRows before world := by
  constructor
  · intro admitted
    have takeShape : code.take.length = picked.taken.length := by
      simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.take_shape
    have readShape : code.read.length = picked.read.length := by
      simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.read_shape
    refine ⟨admitted.take_distinct, admitted.output_distinct, takeShape, readShape, ?_,
      admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_, ?_⟩
    · simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.output_shape
    · exact (ContextualClauseViewModels.solvable_iff agree leftProvider rightProvider takeShape readShape).mp admitted.solvable
    · intro check member
      apply (ask_iff agree leftProvider rightProvider takeShape readShape check).mp
      apply admitted.checks _
      exact List.mem_map.mpr ⟨check, member, rfl⟩
  · intro admitted
    refine ⟨admitted.take_distinct, admitted.output_distinct, ?_, ?_, ?_, admitted.taken_present,
      admitted.read_present, admitted.apart, admitted.fresh, ?_, ?_⟩
    · simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.take_shape
    · simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.read_shape
    · simpa only [mappedRule, RuleInstance.map, List.length_map] using admitted.output_shape
    · exact (ContextualClauseViewModels.solvable_iff agree leftProvider rightProvider
        admitted.take_shape admitted.read_shape).mpr admitted.solvable
    · intro check member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (ask_iff agree leftProvider rightProvider admitted.take_shape admitted.read_shape original).mpr
        (admitted.checks original present)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmissionViews
