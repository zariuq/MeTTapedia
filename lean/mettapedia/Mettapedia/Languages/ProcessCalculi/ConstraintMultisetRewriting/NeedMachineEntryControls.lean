import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineEntry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineControls
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructionControls

/-!
# Complete source-program observations of ordinary transform paths

The observation below requires an actual generated-catalogue path from
ordinary program entry and its represented terminal stores. Existing
independent source runs supply concrete derivations; uniform adequacy gives
the physical paths and excludes every different complete observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.EntryControls

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice (Program Store Comp Outcome)
open CallTimeChoiceInstructions.Controls

def Observes (program : Program) (code : Comp) (answers : List (Outcome × List Nat)) : Prop :=
  ∃ results after next stores control, Path program (entry Store.empty [] code) after ∧
    Running after next stores control ∧ control.decode stores = CallTimeChoiceInstructions.Control.returned results [] ∧
      results.map (fun result => (result.1,result.2.trace)) = answers

theorem observes_iff_of_executed {program : Program} {code : Comp} {fuel : Nat}
    {expected : List (Outcome × List Nat)} (executed : execute program fuel code = some expected)
    (answers : List (Outcome × List Nat)) : Observes program code answers ↔ answers = expected := by
  obtain ⟨reference,source,observed⟩ := every_executed_observation_has_a_source_derivation program fuel code expected executed
  constructor
  · rintro ⟨results,after,next,stores,control,path,running,returned,readout⟩
    have derived := (source_derivation_iff program Store.empty [] code results).mpr
      ⟨after,next,stores,control,path,running,returned⟩
    have same := derived.deterministic source
    rw [same] at readout
    exact readout.symm.trans observed
  · rintro rfl
    obtain ⟨after,next,stores,control,path,running,returned⟩ :=
      (source_derivation_iff program Store.empty [] code reference).mp source
    exact ⟨reference,after,next,stores,control,path,running,returned,observed⟩

theorem shared_program_exact (answers : List (Outcome × List Nat)) :
    Observes [] shared answers ↔ answers =
      [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] :=
  observes_iff_of_executed shared_choices_stay_correlated answers

theorem independent_program_exact (answers : List (Outcome × List Nat)) :
    Observes [] independent answers ↔ answers =
      [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 1) (.sym 2)),[]),
        (.ok (pair (.sym 2) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] :=
  observes_iff_of_executed independent_choices_stay_independent answers

theorem delayed_program_exact (answers : List (Outcome × List Nat)) :
    Observes [] repeated answers ↔ answers =
      [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 1) (.sym 2)),[]),
        (.ok (pair (.sym 2) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] :=
  observes_iff_of_executed ordinary_delay_repeats_the_choice answers

theorem shared_effect_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.need effectful twice) answers ↔ answers = [(.ok (pair (.sym 1) (.sym 1)),[9])] :=
  observes_iff_of_executed shared_effect_occurs_once answers

theorem repeated_effect_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.delay effectful twice) answers ↔ answers = [(.ok (pair (.sym 1) (.sym 1)),[9,9])] :=
  observes_iff_of_executed repeated_effect_occurs_twice answers

theorem unused_recursion_exact (answers : List (Outcome × List Nat)) :
    Observes loopProgram (.need (.call 7 []) (.ret (.sym 8))) answers ↔ answers = [(.ok (.sym 8),[])] :=
  observes_iff_of_executed unused_recursive_work_is_not_forced answers

theorem duplicate_alternatives_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.choose (.ret (.sym 1)) (.ret (.sym 1))) answers ↔
      answers = [(.ok (.sym 1),[]),(.ok (.sym 1),[])] :=
  observes_iff_of_executed equal_alternatives_keep_two_occurrences answers

theorem definition_occurrences_exact (answers : List (Outcome × List Nat)) :
    Observes [⟨4,0,.emit 1 (.ret (.sym 8))⟩,⟨4,0,.emit 2 (.ret (.sym 8))⟩,⟨4,0,.emit 1 (.ret (.sym 8))⟩]
      (.call 4 []) answers ↔ answers = [(.ok (.sym 8),[1]),(.ok (.sym 8),[2]),(.ok (.sym 8),[1])] :=
  observes_iff_of_executed duplicate_equations_keep_program_order_and_multiplicity answers

theorem inert_quote_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.quote effectful) answers ↔ answers = [(.ok (.code 0),[])] :=
  observes_iff_of_executed quotation_is_inert answers

theorem repeated_activation_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.seq (.quote effectful) (.seq (.run (.var 0)) (.run (.var 1)))) answers ↔
      answers = [(.ok (.sym 1),[9,9])] :=
  observes_iff_of_executed activation_runs_code_afresh_each_time answers

theorem noncode_activation_exact (answers : List (Outcome × List Nat)) :
    Observes [] (.run (.sym 8)) answers ↔
      answers = [(.ok (.app (.sym CallTimeChoice.unquoteHead) (.sym 8)),[])] :=
  observes_iff_of_executed activating_noncode_returns_the_declared_residual answers

theorem shared_program_cannot_resample :
    ¬ Observes [] shared [(.ok (pair (.sym 1) (.sym 1)),[]),(.ok (pair (.sym 1) (.sym 2)),[]),
      (.ok (pair (.sym 2) (.sym 1)),[]),(.ok (pair (.sym 2) (.sym 2)),[])] := by
  intro observed
  have same := (shared_program_exact _).mp observed
  have lengths := congrArg List.length same
  simp at lengths

theorem a_shared_effect_cannot_be_replayed :
    ¬ Observes [] (.need effectful twice) [(.ok (pair (.sym 1) (.sym 1)),[9,9])] := by
  intro observed
  have same := (shared_effect_exact _).mp observed
  simp at same

def missingControl : NeedControl.Control Nat := .task (.forceVal 0 (.need 0)) []

theorem missing_cell_suspends_the_actual_catalogue :
    ¬ ∃ after, Executes [] (initialWorld Store.empty missingControl) after := by
  apply (initial_running Store.empty missingControl (by simp [missingControl,NeedControl.Control.names,NeedControl.Goal.names])).no_execution_of_stuck
  rfl

theorem retained_example_running : Running NeedMachine.Controls.initial 1 (fun _ => NeedMachine.Controls.oldStore)
    NeedMachine.Controls.intent.plan.input := by
  have initialEq : initialWorld NeedMachine.Controls.oldStore NeedMachine.Controls.intent.plan.input =
      NeedMachine.Controls.initial := by
    apply congrArg₂ Configuration.mk rfl
    decide +kernel
  rw [← initialEq]
  apply initial_running
  simp [NeedMachine.Controls.intent,NeedMachine.Controls.saved,NeedControl.Intent.plan,
    NeedControl.Control.names,NeedControl.Goal.names,NeedControl.Frame.names]

theorem actual_copy_decreases_with_a_source_work_continuation :
    ∃ before after : CertifiedState [], before.1 = NeedMachine.Controls.started ∧
      after.1 = NeedMachine.Controls.prepared ∧ CallTimeChoiceInstructions.sourceWork before.decode = true ∧
      AdministrativeRankLT after.rank before.rank := by
  have running := retained_example_running
  have waiting := running.edit NeedMachine.Controls.intent (.memo 0 (.done (.sym 42)))
    NeedMachine.Controls.resume rfl ⟨NeedMachine.Controls.beginSelection,NeedMachine.Controls.begin_valid,rfl⟩
  have copyStep : Step action label NeedMachine.Controls.prepareRule NeedMachine.Controls.started NeedMachine.Controls.prepared :=
    ⟨NeedMachine.Controls.prepareSelection,NeedMachine.Controls.prepare_valid,rfl⟩
  obtain ⟨nextRank,prepared,_⟩ := waiting.copy (.begin 1 [3]) copyStep
  let before : CertifiedState [] := ⟨NeedMachine.Controls.started,
    .waiting 1 (fun _ => NeedMachine.Controls.oldStore) NeedMachine.Controls.intent 0
      (.memo 0 (.done (.sym 42))) NeedMachine.Controls.resume 3 waiting⟩
  let after : CertifiedState [] := ⟨NeedMachine.Controls.prepared,
    .waiting 1 (fun _ => NeedMachine.Controls.oldStore) NeedMachine.Controls.intent 0
      (.memo 0 (.done (.sym 42))) NeedMachine.Controls.resume nextRank prepared⟩
  refine ⟨before,after,rfl,rfl,rfl,?_⟩
  exact administrative_step_decreases before after ⟨_,.copy _ _ _ _ _ _ _,copyStep⟩
    (Or.inl (by change 0 < 4; decide))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine.EntryControls
