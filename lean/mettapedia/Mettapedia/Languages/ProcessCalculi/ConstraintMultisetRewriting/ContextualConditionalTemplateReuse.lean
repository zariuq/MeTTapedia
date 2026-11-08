import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses

/-!
# Two independent uses of one published conditional template

An actual following clause reads occurrence 10 twice, choosing different
private values while retaining the same captured caller. Both uses and
their conditions have one joint model. Occurrence 11 remains present but
its incompatible condition is not imported by either read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateReuse

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalRealizations ContextualClauseWitnesses
open ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

variable (firing : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before)
    (authored : firing.sourceRule = sourceRule) (selected : firing.selection = chosen)

local instance : DecidableEq firing.update.Variables := firing.update.equality

abbrev privateNames := ContextualPublication.privateFamily bank firing.update.declaration

def code : RuleInstance (Term (signature base
    (ContextualConjunctiveQueries.queryFamily locals firing.target.declarations)) [] ()) :=
  ⟨[], [pattern 0 0 0, pattern 1 1 0], [], [], [literal 99]⟩

def plan : ContextualPublication.Plan (Term (signature base
    (ContextualConjunctiveQueries.queryFamily locals firing.target.declarations)) [] ()) :=
  ⟨code firing, [true], rfl⟩

def selection : Selection Nat := ⟨[], [10, 10], [14]⟩

include authored selected

theorem source_admitted : ContextualConditionalSourceAdmission.Admitted locals (privateNames firing)
    firing.target.declarations selection (code firing) firing.target.rows firing.target.equations firing.target.present := by
  obtain ⟨Next, next, candidate, model⟩ := firing.target_solvable
  let requests : List (Term (signature base next) [] () × Row (privateNames firing) firing.target.declarations [] ()) :=
    [(pattern 0 0 0, firing.target.rows 10), (pattern 1 1 0, firing.target.rows 10)]
  have matched : ∀ request ∈ requests, Matches (privateNames firing) firing.target.declarations
      candidate request.1 request.2 := by
    intro request member
    rcases List.mem_cons.mp member with rfl | member
    · exact good_template_has_independent_private_instances firing authored selected next candidate model 0
    · have same := List.mem_singleton.mp member
      subst request
      exact good_template_has_independent_private_instances firing authored selected next candidate model 1
  obtain ⟨extension, filler, realized⟩ := finite_realizations (privateNames firing)
    firing.target.declarations candidate requests matched
  let capture := Assignment.compose extension.assignment candidate
  let witness : Witness locals (privateNames firing) firing.target.declarations selection (code firing)
      firing.target.rows firing.target.equations rfl rfl extension.declarations := by
    refine ⟨(fun impossible => nomatch impossible), capture, filler,
      ContextualResidual.models_compose model extension.assignment,
      (by intro equation member; cases member), ?_, ?_⟩
    · intro port
      exact Fin.elim0 port
    · intro port
      fin_cases port
      · exact realized (pattern 0 0 0, firing.target.rows 10) List.mem_cons_self
      · exact realized (pattern 1 1 0, firing.target.rows 10) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by simp [selection], ?_, by simp [selection], ?_, ?_, ?_⟩
  · rw [firing.physical_result, selected]
    decide +kernel
  · rw [firing.physical_result, selected]
    decide +kernel
  · obtain ⟨images, modeled, _, _⟩ := witness.gives_model locals (privateNames firing) firing.target.declarations
    exact ⟨extension.Names, extension.declarations, images, modeled⟩
  · intro check member
    cases member

theorem two_reads_compile_at_any_budget (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled locals (privateNames firing)
        (before := firing.target) (plan firing) selection,
      compiled.firing.fuel = fuel ∧ compiled.firing.selection.read = [10, 10] ∧
        compiled.firing.target.present = {10, 11, 12, 13, 14} := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize locals (privateNames firing)
    (plan firing) selection (source_admitted firing authored selected) fuel
  refine ⟨compiled, budget, ?_, ?_⟩
  · rw [compiled.selected]
    rfl
  · rw [compiled.physical_result, firing.physical_result, selected]
    decide +kernel

def incompatibleSelection : Selection Nat := ⟨[], [10, 11], [14]⟩

theorem selecting_the_incompatible_schema_is_refused :
    ¬ ContextualConditionalSourceAdmission.Admitted locals (privateNames firing)
      firing.target.declarations incompatibleSelection (code firing) firing.target.rows
      firing.target.equations firing.target.present := by
  intro admitted
  obtain ⟨Next, next, images, model⟩ := admitted.solvable
  let witness := witness_of_model locals (privateNames firing) firing.target.declarations
    incompatibleSelection (code firing) firing.target.rows firing.target.equations rfl rfl images model
  have realized := witness.read ⟨1, by decide +kernel⟩
  have matched := realized.matches (privateNames firing) firing.target.declarations
  apply bad_template_stays_latent_and_unmatched firing authored selected next witness.capture witness.previous _
  exact matched

theorem no_compiled_firing_selects_the_incompatible_schema (fuel : Nat) :
    ¬ ∃ compiled : ContextualConditionalClauses.Compiled locals (privateNames firing)
        (before := firing.target) (plan firing) incompatibleSelection, compiled.firing.fuel = fuel := by
  rintro ⟨compiled, _budget⟩
  exact selecting_the_incompatible_schema_is_refused firing authored selected compiled.source_admitted

omit authored selected in
theorem two_actual_firings_with_independent_reuse (publicationFuel useFuel : Nat) :
    ∃ first : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
      first.sourceRule = sourceRule ∧ first.selection = chosen ∧ first.publication.firing.outputs = outputs ∧
        first.publication.firing.fuel = publicationFuel ∧
      ∃ second : ContextualConditionalClauses.Compiled locals (privateNames first)
          (before := first.target) (plan first) selection,
        second.firing.fuel = useFuel ∧ second.firing.selection.read = [10, 10] ∧
          second.firing.target.present = {10, 11, 12, 13, 14} ∧
          ¬ ContextualConditionalSourceAdmission.Admitted locals (privateNames first)
            first.target.declarations incompatibleSelection (code first) first.target.rows
            first.target.equations first.target.present := by
  obtain ⟨first, source, picked, values, budget, _present, _solvable⟩ :=
    an_actual_mixed_firing_exists publicationFuel
  obtain ⟨second, secondBudget, reads, present⟩ := two_reads_compile_at_any_budget first source picked useFuel
  exact ⟨first, source, picked, values, budget, second, secondBudget, reads, present,
    selecting_the_incompatible_schema_is_refused first source picked⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateReuse

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateReuse

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalRealizations ContextualClauseWitnesses
open ContextualConditionalTemplateControls ContextualConditionalTemplateControls.PublicationBoundary

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)
local instance (first : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before) :
    DecidableEq first.update.Variables := first.update.equality

/-- The same continuation that runs after the original publication is
refused after swapping only its saved conditions, despite an identical raw
first execution. This is a program observation of the publication boundary. -/
theorem swapped_conditions_refuse_the_same_continuation
    (first : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before)
    (authored : first.sourceRule = sourceRule) (selected : first.selection = chosen) :
    ¬ ContextualConditionalSourceAdmission.Admitted locals (privateNames first)
      first.target.declarations selection (code first) (swapConditions first authored).target.rows
      first.target.equations first.target.present := by
  intro admitted
  obtain ⟨Next, next, images, model⟩ := admitted.solvable
  let witness := witness_of_model locals (privateNames first) first.target.declarations
    selection (code first) (swapConditions first authored).target.rows first.target.equations rfl rfl images model
  have matched := (witness.read ⟨0, by decide +kernel⟩).matches (privateNames first) first.target.declarations
  exact swapped_first_row_has_no_instance first authored selected next witness.capture witness.previous _ matched

theorem actual_reuse_distinguishes_equal_raw_executions (publicationFuel useFuel : Nat) :
    ∃ first : ContextualConditionalTemplateExecution.CompiledTemplate locals inners before,
      ∃ authored : first.sourceRule = sourceRule,
        first.publication.firing.fuel = publicationFuel ∧
        (swapConditions first authored).publication.firing = first.publication.firing ∧
        (∃ second : ContextualConditionalClauses.Compiled locals (privateNames first)
          (before := first.target) (plan first) selection, second.firing.fuel = useFuel) ∧
        ¬ ContextualConditionalSourceAdmission.Admitted locals (privateNames first)
          first.target.declarations selection (code first) (swapConditions first authored).target.rows
          first.target.equations first.target.present := by
  obtain ⟨first, authored, selected, _outputs, budget, _present, _solvable⟩ := an_actual_mixed_firing_exists publicationFuel
  obtain ⟨second, secondBudget, _reads, _present⟩ := two_reads_compile_at_any_budget first authored selected useFuel
  exact ⟨first, authored, budget, rfl, ⟨second, secondBudget⟩,
    swapped_conditions_refuse_the_same_continuation first authored selected⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateReuse
