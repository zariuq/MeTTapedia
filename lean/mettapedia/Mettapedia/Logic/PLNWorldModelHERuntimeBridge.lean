import Mettapedia.Logic.PLNWorldModelRuntimeBridge
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# HE LanguageDef Runtime -> WM Obligation Bridge

This module specializes the generic runtime-facing WM bridge to the concrete HE
state-machine relation already exported by `HELanguageDef`:

- configurations are `Pattern`
- one-step runtime dynamics are `DeclReducesRel mettaHE`
- the runtime spec is fixed to `heRuntimeSpec`

This is intentionally the **derived LanguageDef** surface rather than a
handwritten interpreter-step judgment: the current HE formalization exposes the
runtime state machine through `HELanguageDef`, and that is the honest concrete
runtime-facing relation available for the first bridge.
-/

namespace Mettapedia.Logic.PLNWorldModelHERuntimeBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelRuntimeBridge
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- HE-specialized runtime judgment interface using the interpreter-derived
`LanguageDef` relation `DeclReducesRel mettaHE`. -/
structure HEJudgmentWMInterface
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      DeclReducesRel mettaHE p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace HEJudgmentWMInterface

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Forget the HE-specific wrapper back to the generic runtime WM interface. -/
def toRuntimeJudgmentWMInterface
    (I : HEJudgmentWMInterface State Query) :
    RuntimeJudgmentWMInterface State Query Pattern (DeclReducesRel mettaHE) where
  spec := heRuntimeSpec
  encode := I.encode
  side := I.side
  step_sound := I.step_sound

@[simp] theorem toRuntimeJudgmentWMInterface_spec
    (I : HEJudgmentWMInterface State Query) :
    I.toRuntimeJudgmentWMInterface.spec = heRuntimeSpec := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_encode
    (I : HEJudgmentWMInterface State Query) :
    I.toRuntimeJudgmentWMInterface.encode = I.encode := rfl

@[simp] theorem toRuntimeJudgmentWMInterface_side
    (I : HEJudgmentWMInterface State Query) :
    I.toRuntimeJudgmentWMInterface.side = I.side := rfl

/-- Any concrete HE state-machine step transports to a WM strength obligation. -/
theorem declReducesRel_to_wmStrengthObligation
    (I : HEJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstep : DeclReducesRel mettaHE p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  I.step_sound hW hstep

/-- HE star closure transports to WM inequalities by transitivity. -/
theorem declReducesRelStar_to_wmStrengthObligation
    (I : HEJudgmentWMInterface State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : Relation.ReflTransGen (DeclReducesRel mettaHE) p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) :=
  RuntimeJudgmentWMInterface.stepStar_sound I.toRuntimeJudgmentWMInterface hW hstar

/-- Package one concrete HE derived state-machine step as a WM consequence rule. -/
def wmConsequenceRuleOn_of_declReducesRel
    (I : HEJudgmentWMInterface State Query)
    {p q : Pattern}
    (hstep : DeclReducesRel mettaHE p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_step
    I.toRuntimeJudgmentWMInterface hstep

/-- Package HE star closure as a WM consequence rule. -/
def wmConsequenceRuleOn_of_declReducesRelStar
    (I : HEJudgmentWMInterface State Query)
    {p q : Pattern}
    (hstar : Relation.ReflTransGen (DeclReducesRel mettaHE) p q) :
    WMConsequenceRuleOn State Query :=
  RuntimeJudgmentWMInterface.wmConsequenceRuleOn_of_stepStar
    I.toRuntimeJudgmentWMInterface hstar

/-- A top-rule HE state-machine step already yields a WM consequence rule once
an HE interpretation interface is fixed. -/
def wmConsequenceRuleOn_of_topRule
    (I : HEJudgmentWMInterface State Query)
    (r : RewriteRule) {p q : Pattern}
    (hr : r ∈ mettaHE.rewrites)
    (hprem : r.premises = [])
    (bs : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (hmatch : MatchRel r.left p bs)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q) :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_declReducesRel
    (DeclReducesRel.topRule r hr hprem bs hmatch hq)

/-- A congruence HE state-machine step already yields a WM consequence rule
once an HE interpretation interface is fixed. -/
  def wmConsequenceRuleOn_of_congElem
    (I : HEJudgmentWMInterface State Query)
    {elems : List Pattern} {ct : CollType} {rest : Option String}
    (hct : LanguageDef.allowsCongruenceIn mettaHE ct)
    (i : Nat) (hi : i < elems.length)
    (r : RewriteRule)
    (hr : r ∈ mettaHE.rewrites)
    (hprem : r.premises = [])
    (bs : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (hmatch : MatchRel r.left elems[i] bs)
    {q' : Pattern}
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q') :
    WMConsequenceRuleOn State Query :=
  I.wmConsequenceRuleOn_of_declReducesRel
    (p := .collection ct elems rest)
    (q := .collection ct (elems.set i q') rest)
    (DeclReducesRel.congElem
      (rest := rest) hct i hi r hr hprem bs hmatch hq)

end HEJudgmentWMInterface

end Mettapedia.Logic.PLNWorldModelHERuntimeBridge
