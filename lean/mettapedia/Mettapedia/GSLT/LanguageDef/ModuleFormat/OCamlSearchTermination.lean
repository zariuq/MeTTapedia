import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowDependencies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeSteps
import Mettapedia.OSLF.MeTTaIL.StructuralDescentNonrecursiveAdmission
import Mettapedia.OSLF.MeTTaIL.Complete.CompletionBound

/-! O0's actual prepared declarations have only nonrecursive provider
queries. Every finite search therefore settles under any positive quantum;
this is derived from the declarations, not a new admission assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.Machines.ResumableSearchRunner

theorem base_nonrecursive : baseLanguage.rewrites.all
    (fun row => row.premises.all (fun premise => (GeneralPremise.stepSources premise).isEmpty)) = true := by rfl

theorem prepared_nonrecursive (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    ∀ row ∈ prepared.compiled.rewrites, ∀ premise ∈ row.premises, GeneralPremise.stepSources premise = [] := by
  intro row member
  rcases prepared_row_origin program prepared row built member with
    kernel | ⟨reference, instruction, _, formed⟩ | ⟨reference, instruction, rows, _, formed, present⟩ |
      ⟨index, parameter, _, present⟩
  · intro premise inside
    exact List.isEmpty_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp base_nonrecursive row kernel) premise inside)
  · intro premise inside
    rw [(instruction_shapes (patterns program) reference instruction row formed).2.2.1] at inside
    cases inside
  · intro premise inside
    rw [(function_row_shapes program (patterns program) reference instruction rows row formed present).2.2] at inside
    cases inside
  · intro premise inside
    rw [(pattern_rule_shapes parameter index row present).2.2] at inside
    cases inside

theorem epoch_search_completion_bound (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (config : Pattern) (built : prepare program = .ok prepared) :
    ∃ cost, ∀ work, cost ≤ work →
      Complete.Classes.complete (epochPlan prepared table)
        (Complete.Classes.runAt (epochPlan prepared table) [] (.base "MlConfig") config work) = true := by
  have empty := epoch_compiled_equations_empty program prepared table built
  have descends : Complete.Classes.Descends (epochPlan prepared table) := ⟨
    StructuralDescent.nonrecursive_admitted (epochSnapshot prepared table) permissions
      (prepared_nonrecursive program prepared built), by simp [empty]⟩
  apply Complete.Classes.completion_bound (epochPlan prepared table) [] (.base "MlConfig") config descends
    (carrier := [config])
  intro other equivalent
  rw [← Complete.Classes.equivalent_eq_of_no_equations (epochPlan prepared table) [] (.base "MlConfig") empty equivalent]
  simp

theorem epoch_runner_stop_or_commit (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (quantum : Nat) (built : prepare program = .ok prepared)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (running : runner.phase = .running) (positive : 0 < quantum) :
    let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
    (∃ ticks, (Machine.advance search ticks quantum runner).phase ≠ .running ∧
      (Machine.advance search ticks quantum runner).state = runner.state) ∨
    ∃ ticks, ∃ receipt : GeneralOccurrenceSemantics.Receipt, search.Valid runner.state receipt ∧
      Machine.advance search ticks quantum runner = ⟨.running, search.target receipt,
        search.run (search.target receipt) 0, search.target receipt :: runner.states, receipt :: runner.receipts⟩ := by
  obtain ⟨cost, settles⟩ := epoch_search_completion_bound program prepared table runner.state built
  apply stop_or_commit (Settles := fun config => config = runner.state) (cost := fun _ => cost) ?_
    (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical) reached rfl running positive
  intro config work same enough
  subst config
  have done := settles work enough
  change Complete.Classes.status (epochPlan prepared table)
    (Complete.Classes.runAt (epochPlan prepared table) [] (.base "MlConfig") runner.state work) ≠ .pending
  simp only [Complete.Classes.status, done, if_true, ne_eq, reduceCtorEq, not_false_eq_true]

#print axioms base_nonrecursive
#print axioms prepared_nonrecursive
#print axioms epoch_search_completion_bound
#print axioms epoch_runner_stop_or_commit

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
