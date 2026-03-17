import Mettapedia.Logic.PLNWorldModelRuntimeBridge
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# PeTTa Minimal-Instruction -> WM Obligation Bridge

This module specializes the generic runtime-facing WM bridge to the concrete
PeTTa minimal-instruction step relation:

- configurations are `Pattern`
- one-step runtime dynamics are `MeTTaStep s`
- the runtime spec is fixed to `pettaRuntimeSpec`

The goal is modest and explicit: land concrete PeTTa runtime steps on the same
WM strength/consequence surface already used by other bridges, without touching
PureKernel `A/B/C1` and without smuggling MM2 execution metadata into the
logical statement.
-/

namespace Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- PeTTa-specialized runtime judgment interface.

This is the first concrete `R_spec -> C*` specialization:
- the runtime configuration carrier is `Pattern`
- the runtime relation is `MeTTaStep s`
- the runtime profile/spec is fixed to `pettaRuntimeSpec`
-/
structure PeTTaJudgmentWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (s : PeTTaSpace) where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      MeTTaStep s p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace PeTTaJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]
variable {s : PeTTaSpace}

/-- Forget the PeTTa-specific wrapper back to the generic runtime WM interface. -/
def toRuntimeJudgmentWMInterface
    (I : PeTTaJudgmentWMInterface State Query s) :
    RuntimeJudgmentWMInterface State Query Pattern (MeTTaStep s) where
  spec := pettaRuntimeSpec
  encode := I.encode
  side := I.side
  step_sound := I.step_sound

@[simp] theorem toRuntimeJudgmentWMInterface_spec
    (I : PeTTaJudgmentWMInterface State Query s) :
    I.toRuntimeJudgmentWMInterface.spec = pettaRuntimeSpec := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_encode
    (I : PeTTaJudgmentWMInterface State Query s) :
    I.toRuntimeJudgmentWMInterface.encode = I.encode := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_side
    (I : PeTTaJudgmentWMInterface State Query s) :
    I.toRuntimeJudgmentWMInterface.side = I.side := rfl

/-- Any concrete PeTTa minimal step transports to a WM strength obligation. -/
theorem mettaStep_to_wmStrengthObligation
    (I : PeTTaJudgmentWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstep : MeTTaStep s p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  I.step_sound hW hstep

/-- PeTTa star closure transports to WM inequalities by transitivity. -/
theorem mettaStepStar_to_wmStrengthObligation
    (I : PeTTaJudgmentWMInterface State Query s)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : Relation.ReflTransGen (MeTTaStep s) p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  RuntimeJudgmentWMInterface.stepStar_sound I.toRuntimeJudgmentWMInterface hW hstar

/-- Package one concrete PeTTa minimal step as a WM consequence rule. -/
def wmConsequenceRuleOn_of_mettaStep
    (I : PeTTaJudgmentWMInterface State Query s)
    {p q : Pattern}
    (hstep : MeTTaStep s p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step
    I.toRuntimeJudgmentWMInterface hstep

/-- Package PeTTa star closure as a WM consequence rule. -/
def wmConsequenceRuleOn_of_mettaStepStar
    (I : PeTTaJudgmentWMInterface State Query s)
    {p q : Pattern}
    (hstar : Relation.ReflTransGen (MeTTaStep s) p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_stepStar
    I.toRuntimeJudgmentWMInterface hstar

/-- The `eval` constructor already yields a WM consequence rule once a PeTTa
runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_evalStep
    (I : PeTTaJudgmentWMInterface State Query s)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p)
    (hq : applyBindings bs r.right = q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.evalStep r bs p q hr hprem hm hq)

/-- The `chain` constructor already yields a WM consequence rule once a PeTTa
runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_chainStep
    (I : PeTTaJudgmentWMInterface State Query s)
    (p tmpl q result : Pattern) (var : String)
    (hstep : MeTTaStep s p q)
    (hresult : result = applyBindings [(var, q)] tmpl) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.chainStep p tmpl q result var hstep hresult)

/-- The successful `unify` constructor already yields a WM consequence rule
once a PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_unifySuccess
    (I : PeTTaJudgmentWMInterface State Query s)
    (a pat thenB elseB merged : Pattern)
    (bs : Bindings)
    (hm : bs ∈ matchPattern pat a)
    (hresult : merged = applyBindings bs thenB) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.unifySuccess a pat thenB elseB merged bs hm hresult)

/-- The failing `unify` constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_unifyFailure
    (I : PeTTaJudgmentWMInterface State Query s)
    (a pat thenB elseB : Pattern)
    (hno : matchPattern pat a = []) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.unifyFailure a pat thenB elseB hno)

/-- The `decons-atom` constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_deconsStep
    (I : PeTTaJudgmentWMInterface State Query s)
    (c : String) (hd : Pattern) (args : List Pattern)
    (hne : args ≠ []) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.deconsStep c hd args hne)

/-- The `cons-atom` constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_consStep
    (I : PeTTaJudgmentWMInterface State Query s)
    (h : Pattern) (tl : List Pattern) (ct : CollType) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.consStep h tl ct)

/-- The lambda-abstraction constructor already yields a WM consequence rule
once a PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_lambdaAbstract
    (I : PeTTaJudgmentWMInterface State Query s)
    (var : String) (body : Pattern) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.lambdaAbstract var body)

/-- The beta-reduction constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_betaReduce
    (I : PeTTaJudgmentWMInterface State Query s)
    (lcBody arg result : Pattern)
    (hresult : result = openBVar 0 arg lcBody) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.betaReduce lcBody arg result hresult)

/-- The function-return constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_functionReturn
    (I : PeTTaJudgmentWMInterface State Query s)
    (val : Pattern) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.functionReturn val)

/-- The empty-step constructor already yields a WM consequence rule once a
PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_emptyStep
    (I : PeTTaJudgmentWMInterface State Query s) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    MeTTaStep.emptyStep

/-- The contextual `evalc` constructor already yields a WM consequence rule
once a PeTTa runtime interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_evalcStep
    (I : PeTTaJudgmentWMInterface State Query s)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p)
    (hq : applyBindings bs r.right = q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_mettaStep
    (MeTTaStep.evalcStep r bs p q hr hprem hm hq)

end PeTTaJudgmentWMInterface

end Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge
