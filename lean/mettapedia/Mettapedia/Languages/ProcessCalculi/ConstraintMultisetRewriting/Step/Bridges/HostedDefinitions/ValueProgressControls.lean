import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramProgress

/-! # Termination of an actual episode and a looping foreign extension -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueProgressControls

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleBuilder

def start : MClosed := valueC (csym "outside-value-grammar") finishContinuation
def loopRule := equation (n := 0) (literal start) (literal start)

theorem original_normalizes {dev : Definitions.Development} (built : Compiled dev) :
    Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after) start :=
  ValueWorkerRank.compiled_initialized_normalizes built _

def extended {dev : Definitions.Development} (built : Compiled dev) := built.rules ++ [loopRule]

theorem foreign_self_step {dev : Definitions.Development} (built : Compiled dev) :
    ProgramBinders.Rewrites (extended built).get start start := by
  have member : loopRule ∈ extended built := by simp [extended]
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  refine ⟨index, ?_⟩
  rw [selected]
  simpa only [loopRule, materialize_literal] using
    instantiated_answer (n := 0) (literal start) (literal start) Fin.elim0

theorem foreign_extension_diverges {dev : Definitions.Development} (built : Compiled dev) :
    ∃ sequence : Nat → MClosed, sequence 0 = start ∧
      ∀ index, ProgramBinders.Rewrites (extended built).get (sequence index) (sequence (index + 1)) :=
  ⟨fun _ => start, rfl, fun _ => foreign_self_step built⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueProgressControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueProgressControls.original_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueProgressControls.foreign_extension_diverges
