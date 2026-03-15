import Mettapedia.Languages.GF.GFWMObligationAdapter

/-!
# GF → WM Obligation Adapter Regression

Concrete fixtures that consume the pure-interface-aligned GF adapter surface.
-/

namespace Mettapedia.Languages.GF.GFWMObligationAdapterRegression

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.GFWMConnections
open Mettapedia.Languages.GF.GFWMObligationAdapter
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelPureKernelBridge
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped ENNReal

abbrev TestState := Evidence

instance : WorldModel TestState Pattern where
  evidence := fun W _ => W
  evidence_add := by
    intro W₁ W₂ _
    simp
  evidence_zero _ := rfl

def t₁ : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "house" "N")
def t₂ : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "house" "N")

def A : GFSyntaxObj := ⟨t₁⟩
def B : GFSyntaxObj := ⟨t₂⟩

def hAB : A ⟶ B := PLift.up rfl

/-- Identity-pattern interface, used only as an adapter fixture. -/
def testPureInterface : PureJudgmentWMInterface TestState Pattern where
  encode := fun p => p
  side := fun _ => True
  profileStep_sound := by
    intro W p q _ _
    have hEv :
        WorldModel.evidence (State := TestState) (Query := Pattern) W p =
          WorldModel.evidence (State := TestState) (Query := Pattern) W q := by
      rfl
    exact le_of_eq (congrArg Evidence.toStrength hEv)

/-- Direct GF syntactic transport consumed as a pure-style WM obligation. -/
theorem canary_gfSyntaxHom_to_pureStyleObligation (W : TestState) :
    WMStrengthObligation TestState Pattern W
      ((testPureInterface.encode) (syntaxQuery A))
      ((testPureInterface.encode) (syntaxQuery B)) := by
  have hW : testPureInterface.side W := by
    simp [testPureInterface]
  exact gfSyntaxHom_to_wmStrengthObligation
    (I := testPureInterface) (f := hAB) (W := W) hW

/-- End-to-end fixture:
GF syntactic transport -> WM consequence rule -> pure-style obligation witness. -/
theorem canary_endToEnd_gfRule_to_pureStyleObligation (W : TestState) :
    let rule :=
      wmConsequenceRuleOn_of_gfSyntaxHom_viaPureInterface
        (I := testPureInterface) (A := A) (B := B) hAB
    WMStrengthObligation TestState Pattern W rule.premise rule.conclusion := by
  have hW : testPureInterface.side W := by
    simp [testPureInterface]
  simp [wmConsequenceRuleOn_of_gfSyntaxHom_viaPureInterface]
  exact gfSyntaxHom_to_wmStrengthObligation
    (I := testPureInterface) (f := hAB) (W := W) hW

/-- Frege-strong wrapper endpoint is consumable on the pure-style WM obligation
surface. -/
theorem canary_fregeStrong_to_pureStyleObligation (W : TestState) :
    let rule :=
      wmConsequenceRuleOn_of_fregeStrong_viaPureInterface
        (I := testPureInterface)
        FunctionSig.UseN [mkLeaf "house" "N"] [mkLeaf "house" "N"] rfl
    WMStrengthObligation TestState Pattern W rule.premise rule.conclusion := by
  simp [wmConsequenceRuleOn_of_fregeStrong_viaPureInterface,
    wmConsequenceRuleOn_of_gfTreePatternEq_viaPureInterface,
    wmConsequenceRuleOn_of_gfSyntaxHom_viaPureInterface, testPureInterface]

/-- Negative expressivity fixture:
under constant evidence semantics and distinct syntax queries, the GF->WM
functor is not full. -/
theorem canary_notFull_constantEvidence :
    ¬ CategoryTheory.Functor.Full (syntaxToWMFunctor (State := TestState)) := by
  have hconst :
      ∀ W : TestState, ∀ p q : Pattern,
        WorldModel.evidence (State := TestState) (Query := Pattern) W p =
        WorldModel.evidence (State := TestState) (Query := Pattern) W q := by
    intro W p q
    rfl
  let A0 : GFSyntaxObj := ⟨mkLeaf "house" "N"⟩
  let B0 : GFSyntaxObj := ⟨mkLeaf "dog" "N"⟩
  have hneq : syntaxQuery A0 ≠ syntaxQuery B0 := by
    intro h
    simp [A0, B0, syntaxQuery, mkLeaf] at h
  exact syntaxToWMFunctor_not_full_of_constant_evidence
    (State := TestState) hconst
    (A := A0) (B := B0) hneq

end Mettapedia.Languages.GF.GFWMObligationAdapterRegression
