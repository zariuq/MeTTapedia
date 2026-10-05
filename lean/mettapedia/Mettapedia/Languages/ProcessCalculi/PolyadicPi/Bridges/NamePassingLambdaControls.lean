import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

/-!
# Controls for the name-passing lambda communication blocks

Distinct argument and return names expose the binary binder order. The
guarding and definition examples distinguish the supported head interpretation
from strong reduction and from the omitted source environment dynamics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

abbrev Ambient : Ctx sig := [Srt.nm, Srt.nm]
def argument : Var Ambient .nm := .zero
def result : Var Ambient .nm := .succ .zero
def identityBody : Expr (.nm :: Ambient) := .var .zero
def identityCall : Expr Ambient := .app (.lam identityBody) argument

/-- The actual firing source after exchanging the two parallel components. -/
def selectedCall : Proc Ambient := nu (par
  (out2 (.var .zero) (.var (.succ argument)) (.var (.succ result)))
  (inp2 (.var .zero) (compile identityBody (callEnv (push (fun _ x => x)))
    (.succ .zero))))

theorem identity_call_source :
    NamePassing.HeadStep identityCall (.var argument) :=
  .root (.beta identityBody argument)

theorem identity_call_target :
    Step selectedCall (nu (weaken (out1 (.var argument) (.var result)))) :=
  (beta_firing_iff identityBody argument (fun _ x => x) result _).mpr rfl

/-- This selected communication is an event of the declared target rule. -/
theorem identity_call_authored :
    AuthoredStep selectedCall (nu (weaken (out1 (.var argument) (.var result)))) :=
  (authoredStep_iff _ _).mpr identity_call_target

/-- Swapping the reference and return channels is rejected at the actual
supplied endpoint, even though both names have the same sort. -/
theorem swapped_argument_return_rejected :
    ¬ Step selectedCall (nu (weaken (out1 (.var result) (.var argument)))) := by
  intro step
  have equal := (beta_firing_iff identityBody argument (fun _ x => x) result
    (out1 (.var result) (.var argument))).mp step
  change out1 (.var result) (.var argument) = out1 (.var argument) (.var result) at equal
  cases equal

/-- The source contextual comparison also handles a call beneath a carrier. -/
theorem call_beneath_carrier :
    StepModulo
      (translate (.carrier result (.var result) identityCall) result)
      (translate (.carrier result (.var result) (.var argument)) result) :=
  headStep_preserved (.carrier result (.var result) identity_call_source)
    (fun _ x => x) result

def guardedBody : Expr (.nm :: Ambient) :=
  .app (.lam (.var .zero)) .zero

theorem guarded_body_has_beta :
    NamePassing.RootStep guardedBody (.var .zero) := .beta (.var .zero) .zero

/-- Head evaluation cannot silently turn into strong reduction under lambda. -/
theorem lambda_body_not_exposed {endpoint : Expr Ambient} :
    ¬ NamePassing.HeadStep (.lam guardedBody) endpoint :=
  NamePassing.lambda_no_head_step guardedBody

/-- The translated body is input-guarded: it has no bare operational firing
until a caller supplies its reference and return channels. -/
theorem lambda_target_input_guarded {endpoint : Proc Ambient} :
    ¬ Step (translate (.lam guardedBody) result) endpoint := by
  intro step
  cases step

theorem unary_fetch_positive :
    Step (translate (.carrier argument (.var result) (.var argument)) result)
      (out1 (.var result) (.var result)) :=
  fetch_preserved argument (.var result) (fun _ x => x) result

theorem carrier_distinct_name_rejected {endpoint : Expr Ambient} :
    ¬ NamePassing.RootStep (.carrier argument (.var result) (.var result)) endpoint := by
  apply NamePassing.distinct_name_no_fetch
  intro equal
  cases equal

/-- The abridged source rules have no definition activation. -/
theorem definition_source_inert {endpoint : Expr Ambient} :
    ¬ NamePassing.HeadStep (.defn (.var argument) (.var .zero)) endpoint :=
  NamePassing.defn_variable_no_head_step (.var argument) .zero

/-- The target server does answer that reference. Thus the displayed source
roots alone cannot support reflection of all target computations. -/
theorem definition_target_fires :
    ∃ endpoint, StepModulo
      (translate (.defn (.var argument) (.var .zero)) result) endpoint :=
  ⟨_, definition_fetch (.var argument) (fun _ x => x) result⟩

/-- Replication does not erase the arity distinction between fetch and call. -/
theorem fetch_is_not_binary_call {endpoint : Proc Ambient} :
    ¬ Step (par (out1 (.var argument) (.var result))
      (inp2 (.var argument) nil)) endpoint :=
  mismatched_arity_no_step _ _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaControls
