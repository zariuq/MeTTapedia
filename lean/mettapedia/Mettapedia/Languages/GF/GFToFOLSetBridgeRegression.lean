import Mettapedia.Languages.GF.GFToFOLSetBridge

/-!
# GF → FOL(Set) Typed Fragment Bridge Regression

Concrete fixture consuming the SUMO-style typed GF→FOL(Set) fragment translator
through the Set↔WM bridge.
-/

namespace Mettapedia.Languages.GF.GFToFOLSetBridgeRegression

open LO
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Languages.GF.GFToFOLSetBridge

/-- End-to-end fixture:
SUMO-style GF node translation -> ZF provable implication -> WM state-indexed
consequence rule, consumed on singleton set-theory states. -/
theorem canary_sumoStub_rule_singleton
    (S : SetPointed) (hS : S ⊧* 𝗭𝗙) :
    let rule := zfWmRuleOfSumoStubTranslation
    WorldModel.queryStrength (State := SetState) (Query := SetQuery)
      ({S} : SetState) rule.premise ≤
    WorldModel.queryStrength (State := SetState) (Query := SetQuery)
      ({S} : SetState) rule.conclusion := by
  intro rule
  have hW : rule.side ({S} : SetState) := by
    intro S' hmem
    have hEq : S' = S := by
      simpa using (Multiset.mem_singleton.mp hmem)
    cases hEq
    simpa using hS
  exact rule.sound hW

end Mettapedia.Languages.GF.GFToFOLSetBridgeRegression
