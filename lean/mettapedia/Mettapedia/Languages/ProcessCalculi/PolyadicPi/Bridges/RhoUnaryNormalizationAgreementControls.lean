import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreement
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationControls

/-!
# A terminating allocator client and an infinite persistent echo service

The allocator client has no source communication but does have four actual
implementation communications. The echo service has a real source self-loop:
it receives a payload, sends the same payload again and retains its original
server. Its successful core-rho compilation therefore admits an infinite
authored execution, including its real finite installation phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreementControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryCode RhoUnaryWorld RhoUnaryActive RhoUnaryReadback
open RhoUnaryNormalizationAgreement

/-- A source that has no communication still has a nonempty terminating
initialization in the actual target theory. -/
theorem allocator_client_accessible :
    Acc (fun next state => Target.Step state next)
      (runtimeProcess RhoUnaryObservationControls.code 2) := by
  have sourceAcc : Acc
      (fun after state => (NativeTypes.operationalTheory RhoUnaryObservationControls.context).Step state after)
      RhoUnaryObservationControls.scopedOutput :=
    .intro _ (fun after firing => False.elim (RhoUnaryObservationControls.source_terminal after firing))
  exact (compiled_accessibility_iff (.nu RhoUnaryObservationControls.publicBody_guarded)
    RhoUnaryObservationControls.world RhoUnaryObservationControls.code
    RhoUnaryObservationControls.supplied_compilation).mp sourceAcc

def echoWorld : SeedWorld RhoUnaryNormalizationControls.context :=
  RhoUnaryWorld.initial RhoUnaryNormalizationControls.context

noncomputable def echoCode : Code 0 :=
  compiled RhoUnaryNormalizationControls.echo_guarded echoWorld.world

theorem echo_compilation :
    compile echoWorld.world RhoUnaryNormalizationControls.echo = some echoCode :=
  compiled_spec RhoUnaryNormalizationControls.echo_guarded echoWorld.world

/-- This target execution is derived from a genuine nonterminating source
server. It is not an assumed execution or an administrative self-loop. -/
theorem echo_runtime_has_infinite_execution :
    ∃ runtime : Nat → TargetProcess,
      runtime 0 = runtimeProcess echoCode echoWorld.available ∧
      ∀ index, Target.Step (runtime index) (runtime (index + 1)) :=
  (compiled_infinite_execution_iff RhoUnaryNormalizationControls.echo_guarded
    echoWorld echoCode echo_compilation).mp
      ⟨fun _ => RhoUnaryNormalizationControls.echo, rfl,
        fun _ => RhoUnaryNormalizationControls.echo_step⟩

/-- Accessibility of this actual compiled echo runtime would contradict
the source's real self-loop, even though each public request has finite
implementation and rearming overhead. -/
theorem echo_runtime_not_accessible :
    ¬ Acc (fun next state => Target.Step state next)
      (runtimeProcess echoCode echoWorld.available) := by
  intro targetAcc
  exact RhoUnaryNormalizationControls.echo_not_normalizing
    ((compiled_accessibility_iff RhoUnaryNormalizationControls.echo_guarded
      echoWorld echoCode echo_compilation).mpr targetAcc)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreementControls
