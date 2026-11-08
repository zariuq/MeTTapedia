import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAtomicIdentityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowAssemblyControls

/-!
# Production lookup preserves earlier schemas and the latest recycled output

The controls exercise the compiled native output forms rather than looking
up final source row payloads. A four-clause body consumes and recreates the
same source occurrence twice; its last creation is the surviving output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSourceSchedules ContextualConditionalRows

namespace SeparateOutputs

open ContextualPrefixPublicationControls (DataOperator base none symbol box)
open ContextualUniformBirthControls.TwoOutputs

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

theorem first_lookup : body.productionIndex 0 = some firstIndex := by decide +kernel
theorem second_lookup : body.productionIndex 1 = some secondIndex := by decide +kernel
theorem no_fabricated_production : body.productionIndex 42 = Option.none := by decide +kernel

theorem compiled_rows_keep_both_conditions (fuel : Nat) :
    ∃ result : UniformComputed body fuel, ∀ (Next : Type) (next : Next → MetaArity base)
      (candidate : Assignment result.family next),
      Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 2)) (result.compiledRow 0) ∧
      Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 1)) (result.compiledRow 1) ∧
      ¬ Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 2)) (result.compiledRow 1) := by
  obtain ⟨result, answers⟩ := the_same_update_preserves_both_outputs fuel
  have firstRow : result.compiledRow 0 = result.birthRow none firstIndex := by
    simp only [UniformComputed.compiledRow]
    with_unfolding_all rfl
  have secondRow : result.compiledRow 1 = result.birthRow none secondIndex := by
    simp only [UniformComputed.compiledRow]
    with_unfolding_all rfl
  refine ⟨result, ?_⟩
  intro Next next candidate
  rw [firstRow, secondRow]
  exact answers Next next candidate

end SeparateOutputs

namespace RecycledTwice

open ContextualPrefixPublicationControls (DataOperator base none symbol)
open ContextualAtomicIdentityControls (initial final finalLocals body admitted_body)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)
local instance : DecidableEq initial.Names := initial.equality
local instance : DecidableEq ContextualAtomicIdentityControls.middle.Names := ContextualAtomicIdentityControls.middle.equality
local instance : DecidableEq final.Names := final.equality

def consumeCode : RuleInstance (Term (signature base (ContextualConjunctiveQueries.queryFamily none final.declarations)) [] ()) :=
  ⟨[symbol 2], [], [], [], []⟩
def consumePlan : ContextualPublication.Plan
    (Term (signature base (ContextualConjunctiveQueries.queryFamily none final.declarations)) [] ()) :=
  ⟨consumeCode, [], rfl⟩
def consumed : Selection Nat := ⟨[0], [], []⟩
abbrev middle := ContextualClauseSourceState.target none finalLocals final consumePlan consumed
local instance : DecidableEq middle.Names := middle.equality
abbrev middleLocals := ContextualClauseSourceState.resultLocals none finalLocals final

def produceCode : RuleInstance (Term (signature base (ContextualConjunctiveQueries.queryFamily none middle.declarations)) [] ()) :=
  ⟨[], [], [], [], [symbol 3]⟩
def producePlan : ContextualPublication.Plan
    (Term (signature base (ContextualConjunctiveQueries.queryFamily none middle.declarations)) [] ()) :=
  ⟨produceCode, [false], rfl⟩
def produced : Selection Nat := ⟨[], [], [0]⟩
abbrev last := ContextualClauseSourceState.target none middleLocals middle producePlan produced
abbrev lastLocals := ContextualClauseSourceState.resultLocals none middleLocals middle

theorem consume_information : ContextualClauseSourceState.information none finalLocals final consumePlan consumed =
    [(observe (symbol 1), observe (symbol 1)), (observe (symbol 2), observe (symbol 2))] := by
  with_unfolding_all rfl

theorem consume_admitted : ContextualClauseSourceState.Admitted none finalLocals final consumePlan consumed := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, middle.declarations, generator middle.declarations, ?_⟩
    change ContextualResidual.Models _ (ContextualClauseSourceState.information none finalLocals final consumePlan consumed)
    rw [consume_information]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    cases member

theorem produce_information : ContextualClauseSourceState.information none middleLocals middle producePlan produced =
    [(observe (symbol 1), observe (symbol 1)), (observe (symbol 2), observe (symbol 2))] := by
  with_unfolding_all rfl

theorem produce_admitted : ContextualClauseSourceState.Admitted none middleLocals middle producePlan produced := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, last.declarations, generator last.declarations, ?_⟩
    change ContextualResidual.Models _ (ContextualClauseSourceState.information none middleLocals middle producePlan produced)
    rw [produce_information]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    cases member

def program : Schedule base Nat [] () initial last :=
  .snoc (.snoc body none consumePlan consumed) none producePlan produced

theorem admitted : program.Admitted := ⟨⟨admitted_body, consume_admitted⟩, produce_admitted⟩
def firstIndex : program.BirthIndex := ⟨0, by decide +kernel⟩
def lastIndex : program.BirthIndex := ⟨1, by decide +kernel⟩

theorem the_latest_creation_is_selected : program.productionIndex 0 = some lastIndex := by decide +kernel
theorem the_earlier_creation_is_not_selected : program.productionIndex 0 ≠ some firstIndex := by decide +kernel
theorem the_physical_output_is_the_last_creation :
    program.net.effect.made = {Sum.inr (3, 0)} := by decide +kernel

theorem source_row_instances {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment last.declarations next) (pattern : Term (signature base next) [] ()) :
    Matches lastLocals last.declarations candidate pattern (last.rows 0) ↔ pattern = symbol 3 := by
  have row := ContextualClauseSourceState.shared_output_row produce_admitted ⟨0, by decide +kernel⟩ rfl
  change last.rows 0 = _ at row
  rw [row, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
  rfl

theorem the_compiled_row_has_exactly_the_latest_value (fuel : Nat) :
    ∃ result : UniformComputed program fuel, ∀ (Next : Type) (next : Next → MetaArity base)
      (candidate : Assignment result.family next) (pattern : Term (signature base next) [] ()),
      Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate pattern
        (result.compiledRow 0) ↔ pattern = symbol 3 := by
  obtain ⟨result⟩ := compute_uniform program admitted fuel
  refine ⟨result, ?_⟩
  intro Next next candidate pattern
  exact (result.compiled_row_instances 0 next candidate pattern).trans (source_row_instances next _ pattern)

end RecycledTwice

namespace RetainedCapture

open ContextualPrefixPublicationControls (DataOperator base captures none symbol box)
open ContextualRowAssemblyControls.CapturedCondition (declarations row caller
  the_capture_allows_seven the_capture_rejects_an_unrelated_seven)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev initial : ContextualClauseSourceState.World (declarations false) Nat [] () :=
  ⟨Unit, inferInstance, captures, [], {0}, fun _ => row⟩
def body : Schedule base Nat [] () initial initial := .nil initial
theorem admitted : body.Admitted := by
  refine ⟨Unit, captures, generator captures, ?_⟩
  intro equation member
  cases member

local instance : DecidableEq (ContextualAnswerFamilies.Names body.blockVariables) := Schedule.uniformEquality body

def zero : UniformComputed body 0 :=
  ⟨admitted, ContextualFrameWorklist.identity body.uniformProblem, rfl⟩

def uniformCaller (n : Nat) : Assignment body.uniformFamily none
  | ⟨Option.none, ()⟩ => symbol n
  | ⟨some index, _⟩ => Fin.elim0 index

def nativeCaller (n : Nat) : Assignment zero.family none
  | .inl name => uniformCaller n name
  | .inr (.inl name) => uniformCaller n name
  | .inr (.inr impossible) => nomatch impossible

theorem the_original_capture_is_the_returned_capture (n : Nat) :
    Assignment.compose (nativeCaller n) zero.currentEmbedding = caller n := by
  funext name
  cases name
  with_unfolding_all rfl

theorem the_retained_condition_is_not_forgotten :
    Matches (ContextualPublication.privateFamily (declarations false) zero.update.declaration) zero.family
        (nativeCaller 7) (box (symbol 7)) (zero.compiledRow 0) ∧
      ¬ Matches (ContextualPublication.privateFamily (declarations false) zero.update.declaration) zero.family
        (nativeCaller 9) (box (symbol 7)) (zero.compiledRow 0) := by
  have seven := zero.compiled_row_instances 0 none (nativeCaller 7) (box (symbol 7))
  have nine := zero.compiled_row_instances 0 none (nativeCaller 9) (box (symbol 7))
  rw [the_original_capture_is_the_returned_capture] at seven nine
  exact ⟨seven.mpr the_capture_allows_seven,
    fun matched => the_capture_rejects_an_unrelated_seven (nine.mp matched)⟩

end RetainedCapture

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductionControls
