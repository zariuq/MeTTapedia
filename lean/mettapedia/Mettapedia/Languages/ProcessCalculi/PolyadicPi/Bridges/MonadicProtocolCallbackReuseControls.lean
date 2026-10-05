import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCallbackReuse
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

/-!
# Bound-callback reuse controls

A callback in an older occurrence can take the genuinely fresh receiver
name while another occurrence's session is retained. If the reserved
callback is used, contraction can instead identify a reference subject
with its call-valued payload. The two resulting closed processes are
separated by the existing structural-invariant channel-role judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackReuse.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities RuntimeState NamePassingChannelRoles

abbrev context : Ctx sig := []
abbrev chosen : Fin 2 := ⟨1, by decide⟩
abbrev other : Fin 2 := ⟨0, by decide⟩
def oldCallback : Var (World 2 context) .nm := key 2 chosen .callback
def otherSession : Var (World 2 context) .nm := key 2 other .session

def freshBody : Proc (.nm :: World 2 context) :=
  out1 (.var .zero) (.var (.succ otherSession))

theorem reserved_callback_unused : countVar (Var.succ oldCallback) freshBody = 0 := rfl

theorem exact_supplied_endpoint :
    inst freshBody (.var oldCallback) = out1 (.var oldCallback) (.var otherSession) := rfl

/-- The selected callback is behind a complete newer occurrence pair. -/
theorem older_occurrence_callback_reused :
    StructuralEq ((privateScope 2).close (nu freshBody))
      ((privateScope 2).close (out1 (.var oldCallback) (.var otherSession))) := by
  have result := private_callback 2 chosen freshBody reserved_callback_unused
  change StructuralEq ((privateScope 2).close (nu freshBody))
    ((privateScope 2).close (inst freshBody (.var oldCallback))) at result
  rw [exact_supplied_endpoint] at result
  exact result

theorem other_session_retained :
    countVar otherSession (inst freshBody (.var oldCallback)) = 1 := rfl

theorem distinct_old_owner_ports : oldCallback ≠ otherSession := by
  intro same
  have ports := (key_injective 2 chosen other .callback .session same).2
  cases ports

def noRoles : Roles context := fun name => nomatch name

def usedBody : Proc (.nm :: World 1 context) :=
  out1 (.var (.succ (key 1 ⟨0, by decide⟩ .callback))) (.var .zero)

def beforeUsed : Proc context := (privateScope 1).close (nu usedBody)
def afterUsed : Proc context :=
  (privateScope 1).close (inst usedBody (.var (key 1 ⟨0, by decide⟩ .callback)))

theorem old_callback_is_used :
    countVar (Var.succ (key 1 ⟨0, by decide⟩ .callback)) usedBody = 1 := rfl

theorem separate_bound_names_have_roles : Typed noRoles beforeUsed :=
  .nu .call (.nu .reference (.nu .call (.out1 _ _ rfl rfl)))

theorem used_callback_contraction_has_no_roles : ¬ Typed noRoles afterUsed := by
  intro typed
  change Typed noRoles (nu (nu (out1 (.var .zero) (.var .zero)))) at typed
  cases typed with
  | nu outerRole inside => cases inside with
    | nu innerRole output =>
        obtain ⟨reference, call⟩ := unary_output_roles _ .zero .zero output
        rw [reference] at call
        cases call

/-- The absence hypothesis is necessary even for the actual static
equations: these supplied closed endpoints are not equivalent. -/
theorem used_callback_cannot_be_reused : ¬ StructuralEq beforeUsed afterUsed := by
  intro equal
  exact used_callback_contraction_has_no_roles
    ((Typed.structural_iff noRoles equal).mp separate_bound_names_have_roles)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.CallbackReuse.Controls
