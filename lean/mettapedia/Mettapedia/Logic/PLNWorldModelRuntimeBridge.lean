import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Languages.MeTTa.RuntimeSpec

/-!
# RuntimeSpec -> WM Obligation Bridge Surface

This module defines the first runtime-facing `C*` target for the MeTTa family.
It does not define new runtime semantics. Instead, it packages the minimal
obligation surface needed to land a runtime step relation on the same WM
strength-consequence boundary already used by other bridges.

Design constraints:

- keep PureKernel `A/B/C1` untouched
- keep `RuntimeSpec` audit-oriented and minimal
- let concrete runtime relations (`HE`, `PeTTa`, later MM2-near layers) prove
  their soundness against this surface

At this level, MM2 priority and sink/update details are treated as execution
metadata rather than semantic necessities. They matter for scheduling and native
execution planning, but not yet for the logical statement that an accepted
runtime step transports to a WM strength inequality.
-/

namespace Mettapedia.Logic.PLNWorldModelRuntimeBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Languages.MeTTa.RuntimeSpec

/-- Local WM strength obligation for a fixed state/query pair. -/
abbrev WMStrengthObligation
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (q₁ q₂ : Query) : Prop :=
  BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂

/-- First runtime-facing `C*` interface target.

`Cfg` is the runtime configuration carrier for the dialect-specific step
relation. `step` is intentionally external to `RuntimeSpec`: the runtime spec
records the visible semantic shape of a dialect, while this interface records
how a concrete runtime relation lands on WM obligations.
-/
structure RuntimeJudgmentWMInterface
    (State Query Cfg : Type*)
    [EvidenceType State] [BinaryWorldModel State Query]
    (step : Cfg → Cfg → Prop) where
  spec : MeTTaRuntimeSpec
  encode : Cfg → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {c₁ c₂ : Cfg},
      side W →
      step c₁ c₂ →
      WMStrengthObligation State Query W (encode c₁) (encode c₂)

namespace RuntimeJudgmentWMInterface

variable {State Query Cfg : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]
variable {step : Cfg → Cfg → Prop}

/-- Star closure of runtime steps transports to WM inequalities by transitivity. -/
theorem stepStar_sound
    (I : RuntimeJudgmentWMInterface State Query Cfg step)
    {W : State} {c₁ c₂ : Cfg}
    (hW : I.side W)
    (hstar : Relation.ReflTransGen step c₁ c₂) :
    WMStrengthObligation State Query W (I.encode c₁) (I.encode c₂) := by
  induction hstar with
  | refl =>
      exact le_rfl
  | tail hxy hyz ih =>
      exact le_trans ih (I.step_sound hW hyz)

/-- Package one concrete runtime step as a WM state-indexed consequence rule. -/
def wmConsequenceRuleOn_of_step
    (I : RuntimeJudgmentWMInterface State Query Cfg step)
    {c₁ c₂ : Cfg}
    (hstep : step c₁ c₂) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode c₁
  conclusion := I.encode c₂
  sound := by
    intro W hW
    exact I.step_sound hW hstep

/-- Package runtime star closure as a WM state-indexed consequence rule. -/
def wmConsequenceRuleOn_of_stepStar
    (I : RuntimeJudgmentWMInterface State Query Cfg step)
    {c₁ c₂ : Cfg}
    (hstar : Relation.ReflTransGen step c₁ c₂) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode c₁
  conclusion := I.encode c₂
  sound := by
    intro W hW
    exact I.stepStar_sound hW hstar

end RuntimeJudgmentWMInterface

end Mettapedia.Logic.PLNWorldModelRuntimeBridge
