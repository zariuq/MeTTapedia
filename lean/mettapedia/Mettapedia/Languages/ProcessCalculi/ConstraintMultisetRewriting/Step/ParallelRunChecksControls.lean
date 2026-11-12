import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ParallelRunChecks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchangeControls

/-!
# Source-level complete-run checks in growing contextual frames

The helper consumer supplies actual complete runs and local closing witnesses.
An inconsistent-state control retains the empty interchange, as the raw run
category requires, without introducing a global consistency requirement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ParallelRunChecksControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers
open Helpers.Consumer (tiny start empty constant)

abbrev P := ResidualRunExchangeControls.P
abbrev T := ResidualRunExchangeControls.T

def right : P.Run start :=
  .cons ResidualRunExchangeControls.third ResidualRunExchangeControls.third_admitted (.nil _)

def localClosings := ResidualRunExchangeControls.crossing.closingsFromGlobal ResidualRunExchangeControls.closing
def head := ResidualRunExchangeControls.crossing.exchangeWith localClosings

noncomputable def connection : T.Iso head.residualRun.last
    (P.result head.residualFiring head.residualAdmitted) := Classical.choice head.same_endpoint

def plan : T.RunInterchangePlan ResidualRunExchangeControls.twoStepRun right :=
  ⟨ResidualRunExchangeControls.crossing, localClosings, connection, PUnit.unit⟩

theorem source_checks_hold : Transport.InterchangeChecks Helpers.helperCoherent
    ResidualRunExchangeControls.twoStepRun right :=
  (Transport.interchange_plan_iff_checks Helpers.helperCoherent _ _).mp ⟨plan⟩

theorem actual_three_event_exchange :
    (ResidualRunExchangeControls.twoStepRun.append plan.exchange.afterLeft).word.length = 3 :=
  plan.exchange.total_length

theorem contextual_block_interchange : T.TraceEquiv start
    (right.append plan.exchange.afterRight)
    (ResidualRunExchangeControls.twoStepRun.append plan.exchange.afterLeft) := plan.exchange.interchange

def impossibleEquation : Equation (Observation tiny empty.arity) :=
  (observe (constant (Γ := []) 7), observe (constant (Γ := []) 8))

def inconsistent : Helpers.State tiny Nat := ⟨empty, [impossibleEquation], ∅⟩

theorem inconsistent_knowledge : ¬(Frames.contextual tiny).Solvable inconsistent.knowledge := by
  rintro ⟨target, mapping, solved⟩
  have impossible := solved impossibleEquation (List.mem_singleton_self _)
  change observe (constant (declaration := target.arity) (Γ := []) 7) =
    observe (constant (Γ := []) 8) at impossible
  cases observe_injective impossible

def idle : P.Run inconsistent := .nil inconsistent

theorem empty_plan_without_consistency :
    Nonempty (T.RunInterchangePlan idle idle) ∧ ¬(Frames.contextual tiny).Solvable inconsistent.knowledge :=
  ⟨⟨PUnit.unit⟩, inconsistent_knowledge⟩

theorem empty_source_checks_without_consistency :
    Transport.InterchangeChecks Helpers.helperCoherent idle idle ∧
      ¬(Frames.contextual tiny).Solvable inconsistent.knowledge := by
  exact ⟨(Transport.interchange_plan_iff_checks Helpers.helperCoherent idle idle).mp
    empty_plan_without_consistency.1, inconsistent_knowledge⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ParallelRunChecksControls
