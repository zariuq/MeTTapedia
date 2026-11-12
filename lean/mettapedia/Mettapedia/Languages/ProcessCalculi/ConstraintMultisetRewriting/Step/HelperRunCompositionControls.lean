import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementBlocks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunRebaseControls

/-! # The native helper consumer of sequential contextual interpretation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.RunCompositionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Helpers.Consumer (tiny start first)
open ContextResultControls (placed)

abbrev firstAllowed := ResidualRunExchangeControls.first_admitted
abbrev next := ResidualRunExchangeControls.T.residual first firstAllowed Helpers.Consumer.second
abbrev nextAllowed := ResidualRunExchangeControls.second_after_first

def initial : helperStep.Run start := .cons first firstAllowed (.nil _)
def later : helperStep.Run initial.last := .cons next nextAllowed (.nil _)

def prefixPlan : RebasePlan tiny Nat placed initial :=
  .cons (by simp [Firing.selection]) ContextResultControls.native_admitted (.nil _)

def suffixPlan : RebasePlan tiny Nat (RebasePlan.realize placed initial prefixPlan).target later :=
  .cons (by simp [Firing.selection]) RunRebaseControls.second_native_admitted (.nil _)

def combined := prefixPlan.append contextualRunInterpretation placed initial later suffixPlan

def sequential := prefixPlan.sequentialExecution contextualRunInterpretation placed initial later suffixPlan

theorem source_word_unchanged : initial.append later = RunRebaseControls.localRun := rfl

theorem existing_native_run_is_sequential : helperTransport.TraceEquiv placed.state
    RunRebaseControls.realization.execution sequential := by
  have related := ContextualRunInterpretation.Plan.append_trace contextualRunInterpretation placed initial prefixPlan later suffixPlan
  have same := ContextualRunInterpretation.Plan.unique contextualRunInterpretation combined RunRebaseControls.plan
  have sameExecution := congrArg (fun plan : RebasePlan tiny Nat placed RunRebaseControls.localRun =>
    (RebasePlan.realize placed RunRebaseControls.localRun plan).execution) same
  exact Eq.mp (congrArg (fun run => helperTransport.TraceEquiv placed.state run sequential) sameExecution) related

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.RunCompositionControls
