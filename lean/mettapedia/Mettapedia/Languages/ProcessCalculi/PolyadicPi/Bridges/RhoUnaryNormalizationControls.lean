import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryObservationControls

/-!
# Terminating initialization and an actual nonterminating source server

The scoped output performs four real initialization communications and has
no source successor. A retained echo server, in contrast, has a genuine
source self-loop modulo the authored structural equations. Thus the source
accessibility hypothesis discriminates actual admitted programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryReadback RhoUnaryCompiler

/-- The concrete four-step allocator client is accessible under every
actual target schedule, despite having unfinished administrative work. -/
theorem scoped_output_normalizes :
    Acc (fun next state => Target.Step state next)
      (runtimeProcess RhoUnaryObservationControls.code 2) := by
  have sourceAcc : Acc
      (fun after before => (NativeTypes.operationalTheory RhoUnaryObservationControls.context).Step before after)
      RhoUnaryObservationControls.scopedOutput :=
    .intro _ (fun after step => False.elim (RhoUnaryObservationControls.source_terminal after step))
  obtain ⟨witness, _⟩ := initial_witness (.nu RhoUnaryObservationControls.publicBody_guarded)
    RhoUnaryObservationControls.world RhoUnaryObservationControls.code
    RhoUnaryObservationControls.supplied_compilation
  exact RhoUnaryNormalization.strongly_normalizing sourceAcc witness

abbrev context : Ctx sig := [Srt.nm, Srt.nm]
abbrev channel : Var context .nm := .zero
abbrev datum : Var context .nm := .succ .zero

def echoBody : Proc (.nm :: context) := out1 (.var (.succ channel)) (.var .zero)
def echoInput : Proc context := inp1 (.var channel) echoBody
def echoServer : Proc context := rep echoInput
def echo : Proc context := par (out1 (.var channel) (.var datum)) echoServer

theorem echo_guarded : GuardedUnary echo :=
  .par (.out1 _ _) (.server _ (.out1 _ _))

/-- Unfolding the retained server provides one receiver while leaving the
same server in the actual communication's frame. -/
theorem echo_step : (NativeTypes.operationalTheory context).Step echo echo := by
  change StepModulo echo echo
  have opened : inst echoBody (.var datum) = out1 (.var channel) (.var datum) := rfl
  refine ⟨par (par (out1 (.var channel) (.var datum)) echoInput) echoServer,
    par (inst echoBody (.var datum)) echoServer, ?_, ?_, ?_⟩
  · exact .trans (.par (.refl _) (.repUnfold echoInput)) (.symm (.parAssoc _ _ _))
  · exact .parL echoServer (.comm1 (.var channel) (.var datum) echoBody)
  · rw [opened]
    exact .refl _

theorem echo_not_normalizing :
    ¬ Acc (fun after before => (NativeTypes.operationalTheory context).Step before after) echo :=
  not_acc_iff_exists_descending_chain.mpr ⟨fun _ => echo, rfl, fun _ => echo_step⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationControls
