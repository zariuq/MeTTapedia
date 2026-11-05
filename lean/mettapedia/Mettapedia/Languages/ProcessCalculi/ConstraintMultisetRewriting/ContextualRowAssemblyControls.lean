import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedRowAssembly
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls

/-!
# Complete assembled rows retain birth conditions and computed answers

The open-schema body keeps its earlier answer 2 while the caller becomes 1.
Its actual zero-budget result retains a pending equation. A second body
computes a key through stored code, consumes a token and reads its answer
twice; its assembled conditional output cannot invent answer 9.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowAssemblyControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualSourceSchedules

namespace CapturedCondition

open ContextualPrefixPublicationControls (DataOperator base captures none symbol box)

abbrev Variables (_ : Bool) := Unit
def declarations (index : Bool) (_ : Unit) : MetaArity base := if index then ([()], ()) else ([], ())
abbrev source := ContextualSelectionViews.source (declarations false) captures
def privateValue : Term (signature base source) [] () := generator source (.inl ())
def capturedValue : Term (signature base source) [] () := generator source (.inr ())
def row : Row (declarations false) captures [] () :=
  ⟨.schema (box privateValue), [(observe privateValue, observe capturedValue)]⟩
def caller (n : Nat) : Assignment captures none := fun _ => symbol n

theorem the_capture_allows_seven : Matches (declarations false) captures (caller 7) (box (symbol 7)) row := by
  refine ⟨ContextualGuardMatching.Extension.identity none, (fun _ => symbol 7), ?_, ?_⟩
  · intro equation member
    have only : equation = (observe privateValue, observe capturedValue) := List.mem_singleton.mp member
    subst equation
    rfl
  · rfl

theorem the_capture_rejects_an_unrelated_seven :
    ¬ Matches (declarations false) captures (caller 9) (box (symbol 7)) row := by
  rintro ⟨extension, images, model, same⟩
  let assignment := ContextualGuardMatching.instanceAssignment (declarations false) images extension.assignment (caller 9)
  have bound : instantiate assignment privateValue = instantiate assignment capturedValue :=
    (ContextualResidual.models_observed_iff assignment privateValue capturedValue).mp model
  have captured : instantiate assignment capturedValue = symbol 9 := by
    erw [capturedValue, instantiate_generator]
    rfl
  have pinned := bound.trans captured
  change box (instantiate assignment privateValue) = box (symbol 7) at same
  rw [pinned] at same
  have arguments := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
  have impossible : (9 : Nat) = 7 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments).1)
  omega

def packed := ContextualConditionalRowPacking.pack Variables declarations captures false row

/-- The unused second family has arity one; packing supplies it without changing the captured reference. -/
theorem packed_capture_keeps_the_condition :
    Matches (ContextualConditionalRowPacking.family Variables declarations) captures (caller 7) (box (symbol 7)) packed ∧
      ¬ Matches (ContextualConditionalRowPacking.family Variables declarations) captures (caller 9) (box (symbol 7)) packed := by
  exact ⟨(ContextualConditionalRowPacking.matches_iff Variables declarations captures false row (caller 7) _).mpr
      the_capture_allows_seven,
    fun matched => the_capture_rejects_an_unrelated_seven
      ((ContextualConditionalRowPacking.matches_iff Variables declarations captures false row (caller 9) _).mp matched)⟩

def forgettingConditions : Row (declarations false) captures [] () := ⟨row.value, []⟩

theorem dropping_the_condition_invents_an_answer :
    Matches (declarations false) captures (caller 9) (box (symbol 7)) forgettingConditions := by
  refine ⟨ContextualGuardMatching.Extension.identity none, (fun _ => symbol 7), ?_, rfl⟩
  intro equation member
  cases member

end CapturedCondition

namespace EarlierSchema

open ContextualPrefixPublicationControls (DataOperator base none symbol box firstLocals afterFirst afterSecond
  secondPlan secondSelection secondX second_information the_callers_variable_is_one the_earlier_schema_still_matches_two)
open ContextualScheduleControls.EarlierSchema (body compiled_accepts)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := inferInstanceAs (DecidableEq DataOperator)

def zero : ComputedAssembly body 0 := by
  let _ := afterSecond.equality
  exact ⟨compiled_accepts, ContextualFrameWorklist.identity body.compile.problem, rfl⟩

theorem the_actual_zero_budget_keeps_a_pending_equation : zero.update.remaining.length = 1 := by
  change body.compile.problem.length = 1
  have current : body.compile.problem =
      ContextualClauseSourceState.information none firstLocals afterFirst secondPlan secondSelection := body.assembled_information
  rw [current, second_information]
  rfl

theorem the_earlier_schema_still_accepts_two {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment zero.family next) :
    Matches body.rowFamily zero.family candidate (box (symbol 2)) (zero.world.rows (.inr (0, 0))) := by
  have key : (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current 0 =
      Sum.inr (0, 0) := by with_unfolding_all rfl
  rw [← key]
  exact (zero.row_instances 0 next candidate _).mpr
    (the_earlier_schema_still_matches_two next (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource zero.update)))

theorem the_current_caller_still_equals_one {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment zero.family next) (model : ContextualResidual.Models candidate zero.world.equations) :
    instantiate candidate (instantiate (ContextualComputedFreshFrame.includeSource zero.update) secondX) = symbol 1 := by
  rw [← Assignment.instantiate_compose]
  exact the_callers_variable_is_one next _ ((zero.information_iff next candidate).mp model)

theorem the_only_public_row_has_its_created_name : zero.world.present = {Sum.inr (0, 0)} := by
  exact zero.physical_result.trans (by decide +kernel)

end EarlierSchema

namespace ComputedBody

open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries origin symbol located)
open ContextualComputedJoinControls (world)
open ContextualClauseSequencingControls (afterFirst rowLocals nextPlan selection source_next_admitted retainedAnswer)
open ContextualScheduleControls.ComputedBody (body compiled_accepts)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance
local instance : DecidableEq world.Names := world.equality

theorem actual_computed_data_exists_at_every_budget (fuel : Nat) : Nonempty (ComputedAssembly body fuel) :=
  compute_assembly body compiled_accepts fuel

theorem source_output_accepts_seven {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment (ContextualConjunctiveQueries.family captures rowLocals origin) next) :
    Matches (ContextualClauseSourceState.resultLocals captures rowLocals afterFirst)
      (ContextualConjunctiveQueries.family captures rowLocals origin) candidate (located 10 (symbol 7))
      ((ContextualClauseSourceState.target captures rowLocals afterFirst nextPlan selection).rows 5) := by
  with_unfolding_all apply (ContextualClauseSourceState.ordinary_output_instances
    (queries := captures) (locals := rowLocals) (before := afterFirst) (plan := nextPlan) (picked := selection)
    source_next_admitted ⟨0, by decide +kernel⟩ rfl next candidate _).mpr
  obtain ⟨Future, future, images, model⟩ := source_next_admitted.solvable
  let extension := ContextualGuardMatching.Extension.withLocals future next
  let lifted := Assignment.compose (ContextualStoredRows.privateSource future next) images
  have conditions := ContextualResidual.models_compose model (ContextualStoredRows.privateSource future next)
  refine ⟨extension, lifted, conditions, ?_⟩
  change instantiate lifted (ContextualConjunctiveQueries.queryView captures rowLocals origin (located 10 retainedAnswer)) =
    located 10 (symbol 7)
  exact ContextualClauseSequencingControls.source_next_preserves_the_returned_answer extension.declarations lifted conditions

theorem the_assembled_output_accepts_seven {fuel : Nat} (result : ComputedAssembly body fuel)
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment result.family next) :
    Matches body.rowFamily result.family candidate (located 10 (symbol 7))
      (result.world.rows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current 5)) := by
  apply (result.row_instances 5 next candidate _).mpr
  exact source_output_accepts_seven next _

theorem the_assembled_output_excludes_nine {fuel : Nat} (result : ComputedAssembly body fuel)
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment result.family next) :
    ¬ Matches body.rowFamily result.family candidate (located 10 (symbol 9))
      (result.world.rows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current 5)) := by
  intro matched
  have source := (result.row_instances 5 next candidate _).mp matched
  obtain ⟨extension, images, model, same⟩ :=
    (ContextualClauseSourceState.ordinary_output_instances source_next_admitted ⟨0, by decide +kernel⟩ rfl next _ _).mp source
  have seven := ContextualClauseSequencingControls.source_next_preserves_the_returned_answer extension.declarations images model
  change instantiate images (ContextualConjunctiveQueries.queryView captures rowLocals origin (located 10 retainedAnswer)) =
    located 10 (symbol 9) at same
  have conflict := seven.symm.trans same
  have different := (SchematicReach.place_injective conflict).2
  have impossible : (7 : Nat) = 9 := DataOperator.symbol.inj
    (Sum.inl.inj (Sum.inl.inj (Term.op.inj different).1))
  omega

end ComputedBody

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowAssemblyControls
