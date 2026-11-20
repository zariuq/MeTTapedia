import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundCall
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionControls

/-!
# Ground dependencies rule out a genuine unconstrained source answer

The dependency law implies deterministic answers of each selected equation.
It is not imposed on the ambient language: an actual uncovered right-side
hole has two different answers and fails this law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage.Elaboration

theorem grounding_is_deterministic {rule : ProgramBinders.Equation MSig [] ()}
    (grounded : GroundRead.Grounding rule) : LiteralPaths.EquationDeterministic rule := by
  intro call first second one two
  obtain ⟨firstEnvironment, firstMatch, firstOutput⟩ := one
  obtain ⟨secondEnvironment, secondMatch, secondOutput⟩ := two
  have matching := firstMatch.trans secondMatch.symm
  have outputs := grounded (ProgramBinders.ground MSig)
    (rule.assign firstEnvironment (ProgramBinders.ground MSig)) secondEnvironment matching
  exact Rigid.include_injective (ProgramBinders.ground MSig) first second
    (firstOutput.symm.trans (outputs.trans secondOutput))

theorem uncovered_not_grounding : ¬ GroundRead.Grounding RuntimeSubstitution.uncovered := by
  intro grounded
  obtain ⟨first, second, different⟩ := RuntimeSubstitution.uncovered_rule_has_two_answers
  exact different (grounding_is_deterministic grounded _ _ _ first second)

theorem actual_template_has_grounding :
    GroundRead.Grounding (RuleBuilder.equation GroundRead.identityLhs GroundRead.identityRhs) :=
  GroundRead.equation_grounding _ _ GroundRead.identity_checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundControls.uncovered_not_grounding
