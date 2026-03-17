import Mettapedia.Languages.GF.GFWMConnections

/-!
# GF ↔ WM Connections Regression

Small theorem-level fixtures that consume the `GFWMConnections` endpoints.
-/

namespace Mettapedia.Languages.GF.GFWMConnectionsRegression

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.OSLFToNTT
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.GFWMConnections
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.CategoryTheory.NativeTypeTheory
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open scoped ENNReal

abbrev TestState := BinaryEvidence

instance : BinaryWorldModel TestState Pattern where
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

/-- Categorical map from GF syntax to WM semantics gives concrete strength equality. -/
theorem canary_syntaxToWM_strength (W : TestState) :
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W
      (wmQuery (State := TestState) (syntaxToWMFunctor.obj A)) =
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W
      (wmQuery (State := TestState) (syntaxToWMFunctor.obj B)) := by
  simpa [A, B, hAB] using
    (syntaxToWMFunctor_map_strengthEq (State := TestState) (A := A) (B := B) hAB W)

/-- The WM consequence-rule wrapper built from a GF syntactic transport is consumable. -/
theorem canary_syntaxHom_rule_apply (W : TestState) :
    let rule := wmConsequenceRuleOn_of_syntaxHom (State := TestState) (A := A) (B := B) hAB
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.premise ≤
      BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.conclusion := by
  intro rule
  exact rule.sound (W := W) trivial

/-- Direct WM-strength endpoint from a syntactic hom is consumable. -/
theorem canary_syntaxHom_strengthLE (W : TestState) :
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W (syntaxQuery A) ≤
      BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W (syntaxQuery B) := by
  exact wmStrengthLE_of_syntaxHom (State := TestState) (A := A) (B := B) hAB W

/-- Tree-pattern equality wrapper endpoint is consumable as a WM rule. -/
theorem canary_treePatternEq_rule_apply (W : TestState) :
    let rule := wmConsequenceRuleOn_of_treePatternEq (State := TestState) (t₁ := t₁) (t₂ := t₂) rfl
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.premise ≤
      BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.conclusion := by
  intro rule
  exact rule.sound (W := W) trivial

/-- Generic NTT bridge endpoint is consumable as a hom witness. -/
theorem canary_scopeOrderingNTBridge_nonempty
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {x y : String} (hne : x ≠ y)
    (φ : QFormula2) (p : Pattern) (X : PLNObj) :
    Nonempty (Hom (formulaToNT R I Dom env (.qexists y (.qforall x φ)) p X)
      (formulaToNT R I Dom env (.qforall x (.qexists y φ)) p X)) := by
  exact ⟨scopeOrderingNTBridge R I Dom env hne φ p X⟩

/-- Positive canary for Frege-strong compositional transport. -/
theorem canary_fregeStrong_strength_fixture (W : TestState) :
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W
      (gfAbstractToPattern (.apply FunctionSig.UseN [mkLeaf "house" "N"])) =
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W
      (gfAbstractToPattern (.apply FunctionSig.UseN [mkLeaf "house" "N"])) := by
  exact
    (Mettapedia.Languages.GF.GFWMConnections.canary_fregeStrong_strength (State := TestState)
      FunctionSig.UseN [mkLeaf "house" "N"] [mkLeaf "house" "N"] rfl W)

/-- Frege-strong wrapper endpoint is consumable as a WM rule. -/
theorem canary_fregeStrong_rule_fixture (W : TestState) :
    let rule := wmConsequenceRuleOn_of_fregeStrong (State := TestState)
      FunctionSig.UseN [mkLeaf "house" "N"] [mkLeaf "house" "N"] rfl
    BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.premise ≤
      BinaryWorldModel.queryStrength (State := TestState) (Query := Pattern) W rule.conclusion := by
  intro rule
  exact rule.sound (W := W) trivial

/-- Negative canary endpoint remains available in the regression surface. -/
theorem canary_gardenPath_not_collapsed :
    ∃ p q : Pattern, p ≠ q :=
  canary_gardenPath_patterns_distinct

end Mettapedia.Languages.GF.GFWMConnectionsRegression
