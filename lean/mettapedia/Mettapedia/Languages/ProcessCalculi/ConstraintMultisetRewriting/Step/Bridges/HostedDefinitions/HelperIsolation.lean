import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PhaseReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowPhases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleInstances

/-!
# Helper isolation inside the actual compiled definition program

The assembled program consists of the fixed main clauses, the substitution
helper and the actual generated native rows. Literal phases separate the first
and third groups from internal helper states. Thus an assembled step at such a
state is an actual helper step, preserving the helper's successful-prefix
evidence until the public resume boundary. No arbitrary-extension assumption
is used to discharge this instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperIsolation

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem phase_palettes_checked : RuntimeSubstitution.helperPhases.all
    (fun phase => decide (phase ∉ RowPhases.mainPhases)) = true := by decide +kernel

theorem phase_palettes_disjoint {phase : String} (inside : phase ∈ RuntimeSubstitution.helperPhases) :
    phase ∉ RowPhases.mainPhases :=
  of_decide_eq_true (List.all_eq_true.mp phase_palettes_checked phase inside)

theorem fixed_refused {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.fixed)
    {call result : MClosed} (internal : RuntimeSubstitution.Internal call) :
    ¬ ProgramBinders.Answers rule call result := by
  obtain ⟨phase, observed, inside⟩ := internal
  obtain ⟨main, mainInside, headed⟩ := RowPhases.fixed_phase member
  intro answered
  have same : phase = main := Option.some.inj (observed.symm.trans (answered_phase headed answered))
  subst main
  exact phase_palettes_disjoint inside mainInside

theorem authored_refused {dev : Definitions.Development} (built : Compiled dev)
    {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ built.authored)
    {call result : MClosed} (internal : RuntimeSubstitution.Internal call) :
    ¬ ProgramBinders.Answers rule call result := by
  obtain ⟨phase, observed, inside⟩ := internal
  intro answered
  have same : phase = "hd-root" :=
    Option.some.inj (observed.symm.trans (answered_phase (RowPhases.authored_phase built member) answered))
  subst phase
  exact phase_palettes_disjoint inside (by decide)

theorem assembled_step_is_helper {dev : Definitions.Development} (built : Compiled dev)
    {before after : MClosed} (internal : RuntimeSubstitution.Internal before)
    (step : ProgramBinders.Rewrites built.rules.get before after) :
    RuntimeSubstitution.Step before after := by
  obtain ⟨index, answered⟩ := step
  have member := List.get_mem built.rules index
  simp only [Compiled.rules, ProgramLayout.rows, List.mem_append] at member
  rcases member with (fixed | helper) | authored
  · exact False.elim (fixed_refused fixed internal answered)
  · exact RuntimeSubstitution.of_answer helper answered
  · exact False.elim (authored_refused built authored internal answered)

theorem helper_step_is_assembled {dev : Definitions.Development} (built : Compiled dev)
    {before after : MClosed} (step : RuntimeSubstitution.Step before after) :
    ProgramBinders.Rewrites built.rules.get before after :=
  RuleInstances.rewrite_mono
    (fun rule member => by simp [Compiled.rules, ProgramLayout.rows, member]) step

theorem internal_step_iff {dev : Definitions.Development} (built : Compiled dev)
    {before after : MClosed} (internal : RuntimeSubstitution.Internal before) :
    ProgramBinders.Rewrites built.rules.get before after ↔ RuntimeSubstitution.Step before after :=
  ⟨assembled_step_is_helper built internal, helper_step_is_assembled built⟩

theorem prefix_advance {dev : Definitions.Development} (built : Compiled dev)
    {entry before after : MClosed} (initial : RuntimeSubstitution.Internal entry)
    (prefixRun : RuntimeSubstitution.Runs entry before) (working : ¬ RuntimeSubstitution.AtResume before)
    (step : ProgramBinders.Rewrites built.rules.get before after) :
    RuntimeSubstitution.Runs entry after ∧
      (RuntimeSubstitution.Internal after ∨ RuntimeSubstitution.AtResume after) := by
  have internal : RuntimeSubstitution.Internal before :=
    (RuntimeSubstitution.prefix_internal_or_resume initial prefixRun).resolve_right working
  have helper := assembled_step_is_helper built internal step
  exact ⟨prefixRun.tail helper, RuntimeSubstitution.step_result_scope helper⟩

/-- The restriction ends at the public port; main clauses may continue there. -/
def InternalStep {dev : Definitions.Development} (built : Compiled dev) (before after : MClosed) : Prop :=
  RuntimeSubstitution.Internal before ∧ ProgramBinders.Rewrites built.rules.get before after

theorem internalStep_subrelation {dev : Definitions.Development} (built : Compiled dev)
    {before after : MClosed} (step : InternalStep built before after) : RuntimeSubstitution.Step before after :=
  assembled_step_is_helper built step.1 step.2

theorem internal_normalization {dev : Definitions.Development} (built : Compiled dev) {entry : MClosed}
    (terminates : Acc (fun after before => RuntimeSubstitution.Step before after) entry) :
    Acc (fun after before => InternalStep built before after) entry := by
  induction terminates with
  | intro current _ ih =>
      refine .intro current ?_
      intro after moved
      exact ih after (internalStep_subrelation built moved)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperIsolation
