import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedJoinControls

/-!
# A computed join feeds a second source clause

The first clause computes and publishes answer 7. The second uses the
returned binding and reads the published schema twice. Both reads preserve
its latent equations. A conflicting second demand for 9 cannot fire.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencingControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations ContextualClauseWitnesses
open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries origin symbol located)
open ContextualComputedJoinControls (world plan picked sourceAnswer problem model source_model source_admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance

abbrev afterFirst := ContextualClauseSourceState.target queries locals world plan picked
abbrev rowLocals := ContextualClauseSourceState.resultLocals queries locals world
abbrev nextActor := queryFamily captures origin

def retainedAnswer : SchematicReach.Closed nextActor := generator nextActor (.inr (.inl true))

def code : RuleInstance (SchematicReach.Closed nextActor) :=
  ⟨[], [located 9 retainedAnswer, located 9 retainedAnswer], [], [.equal retainedAnswer (symbol 7)], [located 10 retainedAnswer]⟩

def nextPlan : ContextualPublication.Plan (SchematicReach.Closed nextActor) := ⟨code, [true], rfl⟩
def selection : Selection Nat := ⟨[], [4, 4], [5]⟩

private theorem published_row : afterFirst.rows 4 =
    ContextualConditionalPublication.ordinary locals origin origin ⟨problem, located 9 sourceAnswer⟩ := by
  exact ContextualClauseSourceState.produced_at source_admitted ⟨0, by decide +kernel⟩

def privateImages : Assignment rowLocals captures
  | .inl impossible => nomatch impossible
  | .inr name => model captures name

private theorem published_realizes_seven :
    Realizes rowLocals origin (model captures) (located 9 (symbol 7)) (afterFirst.rows 4) := by
  rw [published_row]
  apply (realizes_ordinary_iff locals origin origin (model captures) (fun name => nomatch name)
    ⟨problem, located 9 sourceAnswer⟩ (located 9 (symbol 7))).mpr
  exact ⟨model captures, source_model captures, rfl⟩

def joinedWitness : Witness captures rowLocals origin selection code afterFirst.rows afterFirst.equations rfl rfl captures := by
  refine ⟨(fun name => nomatch name), model captures, privateImages, source_model captures,
    (by intro equation member; cases member), ?_, ?_⟩
  · intro port
    exact Fin.elim0 port
  · intro port
    fin_cases port <;> exact published_realizes_seven

theorem source_next_admitted : ContextualConditionalSourceAdmission.Admitted captures rowLocals origin
    selection code afterFirst.rows afterFirst.equations afterFirst.present := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · obtain ⟨candidate, model, _, _⟩ := joinedWitness.gives_model captures rowLocals origin
    exact ⟨Empty, captures, candidate, model⟩
  · intro check member
    have only := List.mem_singleton.mp member
    subst check
    intro Future future candidate model
    let witness := witness_of_model captures rowLocals origin selection code afterFirst.rows afterFirst.equations
      rfl rfl candidate model
    have answer := ContextualComputedJoinControls.every_source_model_answers_seven future witness.capture witness.previous
    change instantiate candidate (queryView captures rowLocals origin retainedAnswer) = symbol 7
    rw [ContextualClauseGuardViews.source_value]
    exact answer

theorem source_next_preserves_the_returned_answer
    {Future : Type} (future : Future → MetaArity base)
    (candidate : Assignment (family captures rowLocals origin) future)
    (solved : ContextualResidual.Models candidate
      (ContextualConditionalSourceProblem.problem captures rowLocals origin selection code afterFirst.rows afterFirst.equations)) :
    instantiate candidate (queryView captures rowLocals origin (located 10 retainedAnswer)) = located 10 (symbol 7) := by
  let witness := witness_of_model captures rowLocals origin selection code afterFirst.rows afterFirst.equations rfl rfl candidate solved
  have answer := ContextualComputedJoinControls.every_source_model_answers_seven future witness.capture witness.previous
  rw [ContextualClauseGuardViews.source_value]
  change located 10 (instantiate witness.capture sourceAnswer) = located 10 (symbol 7)
  erw [answer]

def conflictingCode : RuleInstance (SchematicReach.Closed nextActor) :=
  ⟨[], [located 9 retainedAnswer, located 9 (symbol 9)], [], [], [located 10 retainedAnswer]⟩

def conflictingPlan : ContextualPublication.Plan (SchematicReach.Closed nextActor) := ⟨conflictingCode, [true], rfl⟩

theorem a_conflicting_second_read_cannot_fire :
    ¬ ContextualConditionalSourceAdmission.Admitted captures rowLocals origin selection conflictingCode
      afterFirst.rows afterFirst.equations afterFirst.present := by
  intro admitted
  obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
  let witness := witness_of_model captures rowLocals origin selection conflictingCode afterFirst.rows afterFirst.equations
    rfl rfl candidate model
  have row := witness.read ⟨1, by decide +kernel⟩
  change Realizes rowLocals origin witness.capture (located 9 (symbol 9)) (afterFirst.rows 4) at row
  rw [published_row] at row
  obtain ⟨images, conditions, same⟩ := (realizes_ordinary_iff locals origin origin witness.capture
    (fun name => nomatch name) ⟨problem, located 9 sourceAnswer⟩ (located 9 (symbol 9))).mp row
  have answer := ContextualComputedJoinControls.every_source_model_answers_seven future images conditions
  change located 9 (instantiate images sourceAnswer) = located 9 (symbol 9) at same
  erw [answer] at same
  have bodies := (SchematicReach.place_injective same).2
  have impossible : (7 : Nat) = 9 := DataOperator.symbol.inj
    (Sum.inl.inj (Sum.inl.inj (Term.op.inj bodies).1))
  omega

theorem native_next_models_preserve_the_returned_answer
    (first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked)
    {Future : Type} (future : Future → MetaArity base)
    (candidate : Assignment (family captures
      (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
      first.firing.target.declarations) future)
    (solved : ContextualResidual.Models candidate
      (ContextualConditionalSourceProblem.problem captures
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
        first.firing.target.declarations selection
        (ContextualClauseSequencing.nextPlan (before := world) (occupied := ∅) first captures nextPlan).rule
        first.firing.target.rows first.firing.target.equations)) :
    instantiate candidate (queryView captures
      (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
      first.firing.target.declarations
      (instantiate (ContextualStoredRows.liftCaptures captures first.sourceFrame.assignment)
        (located 10 retainedAnswer))) = located 10 (symbol 7) := by
  rw [ContextualClauseStateRefinement.information_exact (before := world) (occupied := ∅) first] at solved
  let witness := witness_of_model captures _ first.firing.target.declarations selection
    (ContextualClauseSequencing.nextPlan (before := world) (occupied := ∅) first captures nextPlan).rule
    first.firing.target.rows _ rfl rfl candidate solved
  have agree : ContextualClauseViewModels.RowsAgree rowLocals _ origin first.sourceFrame
      afterFirst.rows first.firing.target.rows := fun _ next images pattern occurrence =>
    ContextualClauseRealizationRefinement.all_rows (before := world) (occupied := ∅) first occurrence next images pattern
  obtain ⟨source, queryEqual, captureEqual⟩ := ContextualClauseViewModels.witness_to_left
    (takeShape := rfl) (readShape := rfl) agree
    (ContextualClauseRealizationRefinement.sourceImages (before := world) (occupied := ∅)
      first (generator first.firing.target.declarations)) witness
  obtain ⟨images, model, queryFixed, captureFixed⟩ := source.gives_model captures rowLocals origin
  have exactValue := source_next_preserves_the_returned_answer future images model
  rw [ContextualClauseGuardViews.source_value, queryFixed, captureFixed, queryEqual, captureEqual] at exactValue
  erw [ContextualClauseGuardViews.source_value]
  exact (ContextualClauseViewModels.mapped_value captures origin first.sourceFrame
    witness.query witness.capture (located 10 retainedAnswer)).trans exactValue

theorem the_second_native_output_is_exactly_seven
    (first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked) :
    let _ : DecidableEq first.firing.update.Variables := first.firing.update.equality
    ∀ (following : ContextualConditionalClauses.Compiled captures
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
        (before := first.firing.target)
        (ContextualClauseSequencing.nextPlan (before := world) (occupied := ∅) first captures nextPlan) selection)
      (Next : Type) (next : Next → MetaArity base)
      (candidate : Assignment following.firing.target.declarations next) (pattern : SchematicReach.Closed next),
      Matches (ContextualPublication.privateFamily
        (ContextualClauseFrames.bank captures
          (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration))
        following.firing.update.declaration) following.firing.target.declarations candidate pattern
        (following.firing.target.rows 5) ↔ pattern = located 10 (symbol 7) := by
  let _ := first.firing.update.equality
  dsimp only
  intro following Next next candidate pattern
  have kinds := following.intents
  change [following.firing.reusable 5] = [true] at kinds
  apply (following.ordinary_body_instances ⟨0, by decide +kernel⟩ (List.cons.inj kinds).1 next candidate pattern).trans
  constructor
  · rintro ⟨extension, images, model, same⟩
    have exactValue := native_next_models_preserve_the_returned_answer first extension.declarations images model
    apply extension.instantiate_injective
    exact same.symm.trans exactValue
  · intro same
    subst pattern
    obtain ⟨Future, future, images, model⟩ := following.source_admitted.solvable
    let extension := ContextualGuardMatching.Extension.withLocals future next
    let embed := ContextualStoredRows.privateSource future next
    refine ⟨extension, Assignment.compose embed images, ContextualResidual.models_compose model embed, ?_⟩
    erw [Assignment.instantiate_compose]
    erw [native_next_models_preserve_the_returned_answer first future images model]
    rfl

theorem the_actual_compiler_refuses_the_conflicting_second_read
    (first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked) :
    let _ : DecidableEq first.firing.update.Variables := first.firing.update.equality
    ¬ Nonempty (ContextualConditionalClauses.Compiled captures
      (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
      (before := first.firing.target)
      (ContextualClauseSequencing.nextPlan (before := world) (occupied := ∅) first captures conflictingPlan) selection) := by
  let _ := first.firing.update.equality
  dsimp only
  rintro ⟨following⟩
  exact a_conflicting_second_read_cannot_fire
    ((ContextualClauseSequencing.next_admitted_iff (before := world) (occupied := ∅)
      first captures conflictingCode selection).mp following.source_admitted)

theorem the_actual_compiler_executes_the_two_clauses (firstFuel nextFuel : Nat) :
    ∃ first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked,
      first.firing.fuel = firstFuel ∧
      let _ : DecidableEq first.firing.update.Variables := first.firing.update.equality
      ∃ following : ContextualConditionalClauses.Compiled captures
          (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
          (before := first.firing.target)
          (ContextualClauseSequencing.nextPlan (before := world) (occupied := ∅) first captures nextPlan) selection,
        following.firing.fuel = nextFuel ∧ following.firing.target.present = {0, 1, 2, 4, 5} := by
  obtain ⟨first, firstBudget⟩ := ContextualConditionalClauses.realize queries locals
    (before := world.native ∅) plan picked source_admitted firstFuel
  let _ := first.firing.update.equality
  obtain ⟨following, nextBudget⟩ :=
    (ContextualClauseSequencing.next_compilation_iff (before := world) (occupied := ∅)
      first captures nextPlan selection nextFuel).mpr source_next_admitted
  refine ⟨first, firstBudget, following, nextBudget, ?_⟩
  rw [following.physical_result, first.physical_result]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencingControls
