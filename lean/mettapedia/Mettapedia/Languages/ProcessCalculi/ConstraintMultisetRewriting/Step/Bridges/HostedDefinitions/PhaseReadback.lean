import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionPrefixes

/-! # Literal phase readback for arbitrary source equations -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage.Elaboration
open LiteralPaths

theorem matched_phase {equation : ProgramBinders.Equation MSig [] ()} {call : MClosed}
    {environment : equation.Ground} {phase : String}
    (headed : symbolAt equation.lhs [1, 0] = some phase)
    (matched : ProgramBinders.Matches equation call environment) :
    RuntimeSubstitution.phaseOf call = some phase := by
  have named := symbolAt_instantiate (equation.assign environment (ProgramBinders.ground MSig)) headed
  rw [matched] at named
  exact named

theorem answered_phase {equation : ProgramBinders.Equation MSig [] ()} {call result : MClosed} {phase : String}
    (headed : symbolAt equation.lhs [1, 0] = some phase)
    (answered : ProgramBinders.Answers equation call result) :
    RuntimeSubstitution.phaseOf call = some phase := by
  obtain ⟨_, matched, _⟩ := answered
  exact matched_phase headed matched

theorem distinct_phase_refuses {equation : ProgramBinders.Equation MSig [] ()} {call : MClosed}
    {phase current : String} (headed : symbolAt equation.lhs [1, 0] = some phase)
    (observed : RuntimeSubstitution.phaseOf call = some current) (different : phase ≠ current) (result : MClosed) :
    ¬ ProgramBinders.Answers equation call result := by
  intro answered
  exact different (Option.some.inj ((answered_phase headed answered).symm.trans observed))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
