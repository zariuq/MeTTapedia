import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SameHost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementFreshTarget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RecordedChoice

/-!
# The feature table, with the carrier of each cell

`InterfaceTable` states each feature at the first-order, contextual and dependent full steps. A cell
proved on one step does not show that it composes with a cell proved on another. This companion
records, for answer coverage, preparation and disequations, the **carrier** of each cell: the
category of frames its step is an instance over. Cells on the same carrier are stated together
(`contextual_carrier`, `contextual_disequation_carrier`), and the one step that has every feature at
once is `SameHost.hostWith` (`same_host_acceptance`). Every step here is sound
(`SettlementCoverage.sound`); answer coverage is the property of the exhaustive ones, and the
committing controls are sound without it.

| cell | first-order | contextual helper | contextual native | same host | dependent full |
|---|---|---|---|---|---|
| carrier | `Frames.ofSubstitution A` | `Frames.contextual S` | `Frames.contextual S` | `Frames.contextual S` | `ContextualDependentEta.frames levels` |
| answer coverage | `firstOrder_covers` (strong) | `helper_covers` (strong) | `native_coversAnswers` (fresh target) | `host_coversAnswers` | `dependent_covers` (strong) |
| prepared result | `ofPrestep` | `ofPrestep` | `nativePrepared`, agreeing with `native` (`nativePrepared_result`) | `settledBy` | `ofPrestep` |
| carrier with disequations | `frames (Frames.ofSubstitution A)` | `frames (Frames.contextual S)` | `frames (Frames.contextual S)` | `frames (Frames.contextual S)` | `frames (ContextualDependentEta.frames levels)` |
| guarded disequations (`Interface.Step.withDisequations`, guards kept) | `firstOrderWith` | `Contextual.withDisequations` | `nativeGuarded` (firings without guards: `nativeGuarded_admits_iff_of_no_guards`) | `hostWith` | `Dependent.withDisequations` |
| coverage with disequations | `firstOrderWith_covers` | `helperWith_covers` | `nativeGuarded_coversAnswers` | `hostWith_coversAnswers` | `dependentWith_covers` |
| preparation control | | | | `preparation_control`, `guard_not_everywhere` | |
| committing settlement | | | | `closing_control`, `closing_sound_not_covering` | |

Other carriers: the rational step is the first-order step over `Frames.ofSubstitution (rationalAction σ)`
(`rational_covers`); located occurrences over `Frames.ofSubstitution (LocatedSubstitution.action A)`
(`located_covers`); permitted steps are restrictions over their step's carrier
(`permitted_coversAnswers`). The two-bit world frame carries the controls of `SettlementCoverage`
(the committing step `committing_sound_not_covering`), `PreparedStep` and `RecordedChoice`; the
two-sorted declaration frames carry `SettlementCoverage.FreshTarget` (`strong_form_strictly_stronger`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InterfaceTableHosts

open Interface (Frames)
open SettlementCoverage (CoversSettlement CoversAnswers)

section Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable (S : Signature) (O : Type) [DecidableEq O] (Γ : Ctx S) (sort : S.Srt)
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **One carrier, declaration frames**: the helper step, the native step, the prepared native step
and the host, all instances over `Frames.contextual S`, cover their answers. -/
theorem contextual_carrier :
    CoversSettlement (Interface.Helpers.helperStep (S := S) (O := O)).toStep ∧
      CoversAnswers (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep ∧
      CoversAnswers (PreparedStep.nativePrepared S O Γ sort).step.toStep ∧
      CoversAnswers (SameHost.host S O).step.toStep :=
  ⟨SettlementCoverage.helper_covers, SettlementCoverage.native_coversAnswers,
    PreparedStep.nativePrepared_coversAnswers, SameHost.host_coversAnswers⟩

/-- **One carrier, disequation frames over declaration frames**: the helper step, guarded native
firings and the host, all with disequations, cover their answers. -/
theorem contextual_disequation_carrier :
    CoversSettlement (DisequalityFrames.Contextual.withDisequations S O) ∧
      CoversAnswers (PreparedStep.nativeGuarded S O Γ sort) ∧
      CoversAnswers (SameHost.hostWith S O) :=
  ⟨SettlementCoverage.helperWith_covers S O, PreparedStep.nativeGuarded_coversAnswers,
    SameHost.hostWith_coversAnswers⟩

end Contextual

/-- **The same-host acceptance test**: on the host over declaration frames with natural-number
constants, the guarded firing with a fresh helper is refused without its disequation and admitted
with it, the host with disequations covers its answers, and a committing settlement closing old
names admits the firing without guards and does not cover. -/
theorem same_host_acceptance :
    (¬ (SameHost.host Interface.Helpers.Consumer.tiny Nat).step.Admits SameHost.Controls.guarded ∧
      (SameHost.hostWith Interface.Helpers.Consumer.tiny Nat).Admits SameHost.Controls.apart) ∧
    CoversAnswers (SameHost.hostWith Interface.Helpers.Consumer.tiny Nat) ∧
    ((SameHost.Controls.closing).step.Admits SameHost.Controls.quiet ∧
      ¬ CoversAnswers (SameHost.Controls.closing).step.toStep) :=
  ⟨SameHost.Controls.preparation_control, SameHost.hostWith_coversAnswers,
    SameHost.Controls.quiet_admitted, SameHost.Controls.closing_not_coversAnswers⟩

#print axioms contextual_carrier
#print axioms contextual_disequation_carrier
#print axioms same_host_acceptance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InterfaceTableHosts
