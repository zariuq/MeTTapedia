import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineInvariant

/-!
# One source instruction as an actual transform episode

An episode is a direct start or an edit start, a path containing only that
job's copy rules, and its matching commit. It is defined entirely using
ordinary firings, without a source-instruction or decoding premise. The
source comparison is then proved using the global running/waiting invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine

open NeedControl
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice (Program Store)

inductive Episode (program : Program) : World → World → Prop where
  | direct {before after : World} (next : Nat) (intent : Intent program) (output : Control Nat)
      (direct : intent.plan.action = .direct output)
      (start : Step action label (startRule next intent) before after) : Episode program before after
  | edit {before waiting copied after : World} (job : Nat) (intent : Intent program) (source : Nat)
      (operation : NeedStoreOperations.Operation) (resume : Resume) (event : NeedStoreOperations.Event)
      (edit : intent.plan.action = .edit source operation resume)
      (start : Step action label (startRule job intent) before waiting)
      (copies : CopyPath job intent.plan.input intent.plan.reads source operation resume waiting copied)
      (requested : event.operation = operation)
      (commit : Step action label (commitRule job intent.plan.input intent.plan.reads source resume event) copied after) :
      Episode program before after

theorem Episode.ordinary {program : Program} {before after : World} (episode : Episode program before after) :
    Path program before after := by
  cases episode with
  | direct next intent output direct start => exact Relation.ReflTransGen.single ⟨_,.start _ _,start⟩
  | edit job intent source operation resume event edit start copies requested commit =>
      exact (Relation.ReflTransGen.single ⟨_,.start _ _,start⟩).trans
        (copies.ordinary.trans (Relation.ReflTransGen.single ⟨_,.commit _ _ _ _ _ _,commit⟩))

theorem Running.identify_start {program : Program} {before after : World} {next chosen : Nat}
    {stores : Nat → Store} {control : Control Nat} (running : Running before next stores control)
    (intent : Intent program) (step : Step action label (startRule chosen intent) before after) :
    chosen = next ∧ intent.plan.input = control := by
  obtain ⟨picked,valid,_⟩ := step
  have selected := Selected.take_rows valid (.control chosen intent.plan.input)
    (by cases selected : intent.plan.action <;> simp [startRule,selected])
  exact Row.control.inj (controller_unique running.single selected running.active rfl rfl)

/-- Every actual episode recovers exactly one independently specified
instruction, including the store change and saved continuation. -/
theorem Episode.source_instruction {program : Program} {before after : World} {next : Nat}
    {stores : Nat → Store} {control : Control Nat} (episode : Episode program before after)
    (running : Running before next stores control) :
    ∃ next' stores' control', Running after next' stores' control' ∧
      Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Instruction program
        (control.decode stores) (control'.decode stores') := by
  cases episode with
  | direct chosen intent output direct start =>
      obtain ⟨counter,input⟩ := running.identify_start intent start
      subst chosen
      subst control
      have source := start_source_instruction next intent (running.read_models intent) start
      refine ⟨next,stores,output,running.direct intent output direct start,?_⟩
      simpa only [direct,Action.decode] using source
  | edit chosen intent source operation resume event edit start copies requested commit =>
      obtain ⟨counter,input⟩ := running.identify_start intent start
      subst chosen
      subst control
      have sourceStep := start_source_instruction next intent (running.read_models intent) start
      have waiting := running.edit intent operation resume edit start
      obtain ⟨rank,copied⟩ := waiting.copy_path copies
      have published := (copied.commit event requested commit).2
      refine ⟨next+1,Function.update stores next (operation.apply (stores source)),resumeAt next resume,published,?_⟩
      rw [intent.resume_interpretation stores next source operation resume edit running.bounded]
      exact sourceStep

/-- Source completeness constructs the actual start/copy/commit episode;
it does not install a source evaluator as an ordinary rule. -/
theorem Running.realize_episode {program : Program} {before : World} {next : Nat} {stores : Nat → Store}
    {control : Control Nat} (running : Running before next stores control)
    (target : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Control)
    (instruction : Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Instruction program
      (control.decode stores) target) :
    ∃ after, Episode program before after ∧ ∃ next' stores' control',
      Running after next' stores' control' ∧ control'.decode stores' = target := by
  obtain ⟨intent,input,supported,_⟩ := (source_instruction_iff_supported_plan program stores control target).mp instruction
  subst control
  obtain ⟨waiting,start⟩ := running.start_exists intent supported
  have built : ∃ after, Episode program before after := by
    cases selected : intent.plan.action with
    | direct output => exact ⟨waiting,.direct next intent output selected start⟩
    | edit source operation resume =>
        have pending := running.edit intent operation resume selected start
        obtain ⟨copied,copies,ready⟩ := pending.copy_to_completion
        obtain ⟨_,token,completed,_,_,_⟩ := ready.phase.completed_of_reply ready.phase.zero_replied
        have waitingRow : Has copied.present (.waiting next ⟨intent.plan.input,intent.plan.reads,.edit source operation resume⟩) := by
          rw [← plan_eq_edit ready.edit]
          exact ready.waiting
        obtain ⟨event,after,requested,commit⟩ := commit_exists copied next intent.plan.input intent.plan.reads source
          operation resume (stores source) ready.consistent (NeedStoreOperations.editable_of_completed completed) waitingRow
        exact ⟨after,.edit next intent source operation resume event selected start copies requested commit⟩
  obtain ⟨after,episode⟩ := built
  obtain ⟨next',stores',control',ready,derived⟩ := episode.source_instruction running
  have same := Option.some.inj
    ((Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.next_complete derived).symm.trans
      (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.next_complete instruction))
  exact ⟨after,episode,next',stores',control',ready,same⟩

/-- An edit needs its internal work before publication can advance the
running allocation frontier. This separates a raw firing from an episode. -/
theorem Running.no_new_frontier_after_one {program : Program} {before after : World} {next : Nat}
    {stores : Nat → Store} {control : Control Nat} (running : Running before next stores control)
    (execution : Executes program before after) (output : Control Nat) :
    ¬ Has after.present (.control (next+1) output) := by
  intro advanced
  have single := execution.controller_count.trans running.single
  obtain ⟨intent,_,step⟩ := running_step_is_start next control running.single running.active execution
  cases selected : intent.plan.action with
  | direct target =>
      have active := direct_start_outputs next intent target selected step
      have counters := (Row.control.inj (controller_unique single advanced active rfl rfl)).1
      omega
  | edit source operation resume =>
      have waiting : Has after.present (.waiting next intent.plan) := by
        obtain ⟨picked,valid,rfl⟩ := step
        exact Selected.output_rows valid _ (by simp [startRule,selected])
      have impossible := controller_unique single advanced waiting rfl rfl
      cases impossible

theorem step_records_a_take {rule : RuleInstance Row} {before after : World}
    (step : Step action label rule before after) (nonempty : rule.take ≠ []) : after.equations ≠ [] := by
  obtain ⟨picked,valid,rfl⟩ := step
  cases taken : rule.take with
  | nil => exact False.elim (nonempty taken)
  | cons pattern rest =>
      cases selected : picked.taken with
      | nil =>
          have lengths := valid.take_length
          simp [taken,selected] at lengths
      | cons occurrence others =>
          simp [Selection.result,Selection.problem,Selection.equations,taken,selected]

/-- Ordinary episode endpoints retain a nonempty matching-equation
history. This is a physical-state observation, not a source-state field. -/
theorem Episode.records_equations {program : Program} {before after : World}
    (episode : Episode program before after) : after.equations ≠ [] := by
  cases episode with
  | direct next intent output direct start =>
      exact step_records_a_take start (by simp [startRule,direct])
  | edit job intent source operation resume event edit start copies requested commit =>
      exact step_records_a_take commit (by simp [commitRule])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachine
