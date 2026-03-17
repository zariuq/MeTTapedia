import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.Languages.GF.OSLFToNTT
import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# GF ↔ WM Connections

This module makes the GF-to-WM connection explicit at three levels:

1. **Direct semantic transport** (`gfAbstractToPattern` equality gives WM query
   equality, strength equality, and consequence inequality),
2. **Categorical transport** (a thin syntactic category of GF trees mapping
   functorially into a thin WM-query-equivalence category),
3. **Operational wrappers** (syntax transport packaged as WM consequence rules).

It also includes both positive and negative canaries to keep the endpoint
claims honest.
-/

namespace Mettapedia.Languages.GF.GFWMConnections

open CategoryTheory
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.Languages.GF.OSLFToNTT
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.CategoryTheory.NativeTypeTheory
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open scoped ENNReal

universe u

section GenericWM

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- GF-tree evidence as a direct WM query projection through `gfAbstractToPattern`. -/
noncomputable def gfNodeEvidence (W : State) (t : AbstractNode) : BinaryEvidence :=
  BinaryWorldModel.evidence W (gfAbstractToPattern t)

/-- Revising WM states commutes with GF-tree evidence extraction. -/
theorem gfNodeEvidence_add (W₁ W₂ : State) (t : AbstractNode) :
    gfNodeEvidence (W₁ + W₂) t = gfNodeEvidence W₁ t + gfNodeEvidence W₂ t := by
  simpa [gfNodeEvidence] using
    (BinaryWorldModel.evidence_add (State := State) (Query := Pattern) W₁ W₂ (gfAbstractToPattern t))

/-- Lift a base `Pattern`-query WM into a GF-`AbstractNode`-query WM. -/
noncomputable def gfNodeWorldModel : BinaryWorldModel State AbstractNode where
  evidence := gfNodeEvidence
  evidence_add := gfNodeEvidence_add
  evidence_zero t := by
    simp [gfNodeEvidence, BinaryWorldModel.evidence_zero]

/-- Pattern equality implies WM query equality at the pattern-query layer. -/
theorem queryEq_of_patternEq {p q : Pattern} (h : p = q) :
    WMQueryEq (State := State) (Query := Pattern) p q := by
  intro W
  simp [h]

/-- If two GF trees map to the same pattern, they are WM-query-equivalent. -/
theorem queryEq_of_treePatternEq {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    WMQueryEq (State := State) (Query := Pattern)
      (gfAbstractToPattern t₁) (gfAbstractToPattern t₂) :=
  queryEq_of_patternEq (State := State) hPat

/-- Pattern equality transport to WM strength equality for all states. -/
theorem strengthEq_of_patternEq {p q : Pattern} (h : p = q) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W p =
        BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W q :=
  WMQueryEq.to_queryStrength (State := State) (Query := Pattern)
    (queryEq_of_patternEq (State := State) h)

/-- Tree-pattern equality transport to WM strength equality for all states. -/
theorem strengthEq_of_treePatternEq {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₁) =
        BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₂) :=
  strengthEq_of_patternEq (State := State) hPat

/-- Frege-strong syntactic compositionality transports directly to WM query equality. -/
theorem fregeStrong_to_queryEq (f : FunctionSig)
    (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map gfAbstractToPattern = args₂.map gfAbstractToPattern) :
    WMQueryEq (State := State) (Query := Pattern)
      (gfAbstractToPattern (.apply f args₁))
      (gfAbstractToPattern (.apply f args₂)) :=
  queryEq_of_patternEq (State := State) (frege_strong f args₁ args₂ hargs)

/-- Frege-strong syntactic compositionality transports directly to WM strength equality. -/
theorem fregeStrong_to_strengthEq (f : FunctionSig)
    (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map gfAbstractToPattern = args₂.map gfAbstractToPattern) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (gfAbstractToPattern (.apply f args₁)) =
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (gfAbstractToPattern (.apply f args₂)) :=
  strengthEq_of_patternEq (State := State) (frege_strong f args₁ args₂ hargs)

/-- Translation invariance endpoint in WM-strength form. -/
theorem translation_preserves_strength_allW
    {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₁) =
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₂) :=
  strengthEq_of_treePatternEq (State := State) hPat

end GenericWM

section Categorical

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Object layer for the thin GF syntactic category. -/
structure GFSyntaxObj where
  tree : AbstractNode

/-- Pattern query extracted from a GF syntactic object. -/
abbrev syntaxQuery (A : GFSyntaxObj) : Pattern := gfAbstractToPattern A.tree

/-- Thin syntactic hom: equality of extracted GF query patterns. -/
abbrev GFSyntaxHom (A B : GFSyntaxObj) : Type := PLift (syntaxQuery A = syntaxQuery B)

instance gfSyntaxHomSubsingleton (A B : GFSyntaxObj) : Subsingleton (GFSyntaxHom A B) := by
  refine ⟨?_⟩
  intro f g
  cases f
  cases g
  rfl

instance gfSyntaxCategory : CategoryTheory.Category GFSyntaxObj where
  Hom A B := GFSyntaxHom A B
  id A := PLift.up rfl
  comp f g := PLift.up (f.down.trans g.down)
  id_comp := by intro A B f; exact Subsingleton.elim _ _
  comp_id := by intro A B f; exact Subsingleton.elim _ _
  assoc := by intro A B C D f g h; exact Subsingleton.elim _ _

/-- Object layer for the thin WM semantic category on GF queries. -/
structure GFWMObj (State : Type u) where
  tree : AbstractNode

/-- Pattern query extracted from a GF semantic object. -/
abbrev wmQuery (A : GFWMObj State) : Pattern := gfAbstractToPattern A.tree

/-- Thin semantic hom: WM-query-equivalence between extracted GF queries. -/
abbrev GFWMHom (A B : GFWMObj State) : Type :=
  PLift (WMQueryEq (State := State) (Query := Pattern) (wmQuery A) (wmQuery B))

instance gfWMHomSubsingleton (A B : GFWMObj State) :
    Subsingleton (GFWMHom (State := State) A B) := by
  refine ⟨?_⟩
  intro f g
  cases f
  cases g
  rfl

instance gfWMCategory : CategoryTheory.Category (GFWMObj State) where
  Hom A B := GFWMHom (State := State) A B
  id A := PLift.up (WMQueryEq.refl (State := State) (Query := Pattern) (wmQuery A))
  comp f g := PLift.up (WMQueryEq.trans (State := State) (Query := Pattern) f.down g.down)
  id_comp := by intro A B f; exact Subsingleton.elim _ _
  comp_id := by intro A B f; exact Subsingleton.elim _ _
  assoc := by intro A B C D f g h; exact Subsingleton.elim _ _

/-- Functor from thin GF syntax equalities to thin WM query equivalences. -/
def syntaxToWMFunctor : CategoryTheory.Functor GFSyntaxObj (GFWMObj State) where
  obj A := ⟨A.tree⟩
  map := by
    intro A B f
    refine PLift.up ?_
    intro W
    simpa [wmQuery, syntaxQuery] using
      congrArg (BinaryWorldModel.evidence (State := State) (Query := Pattern) W) f.down
  map_id := by
    intro A
    rfl
  map_comp := by
    intro A B C f g
    cases f
    cases g
    rfl

/-- Functorial map soundness at the WM-query-equivalence layer. -/
theorem syntaxToWMFunctor_map_queryEq {A B : GFSyntaxObj} (f : A ⟶ B) :
    WMQueryEq (State := State) (Query := Pattern)
      (wmQuery (State := State) (syntaxToWMFunctor.obj A))
      (wmQuery (State := State) (syntaxToWMFunctor.obj B)) :=
  (syntaxToWMFunctor.map f).down

/-- Functorial map soundness at the WM-strength layer. -/
theorem syntaxToWMFunctor_map_strengthEq {A B : GFSyntaxObj} (f : A ⟶ B) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (wmQuery (State := State) (syntaxToWMFunctor.obj A)) =
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (wmQuery (State := State) (syntaxToWMFunctor.obj B)) :=
  WMQueryEq.to_queryStrength (State := State) (Query := Pattern)
    (syntaxToWMFunctor_map_queryEq (State := State) f)

/-- Any syntactic hom induces a concrete WM strength inequality endpoint. -/
theorem wmStrengthLE_of_syntaxHom {A B : GFSyntaxObj} (f : A ⟶ B) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (syntaxQuery A) ≤
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (syntaxQuery B) :=
  WMQueryEq.to_strengthLE (State := State) (Query := Pattern)
    (syntaxToWMFunctor_map_queryEq (State := State) f)

/-- Build a syntactic hom directly from tree-pattern equality. -/
def syntaxHom_of_treePatternEq {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    (⟨t₁⟩ : GFSyntaxObj) ⟶ (⟨t₂⟩ : GFSyntaxObj) :=
  PLift.up hPat

/-- Tree-pattern equality induces a concrete WM strength inequality endpoint. -/
theorem wmStrengthLE_of_treePatternEq {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₁) ≤
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W (gfAbstractToPattern t₂) :=
  wmStrengthLE_of_syntaxHom (State := State)
    (syntaxHom_of_treePatternEq (hPat := hPat))

/-- Package a syntactic transport proof as a global WM consequence rule. -/
def wmConsequenceRule_of_syntaxHom
    {A B : GFSyntaxObj} (f : A ⟶ B) :
    WMConsequenceRule State Pattern where
  side := True
  premise := syntaxQuery A
  conclusion := syntaxQuery B
  sound := by
    intro _
    exact WMQueryEq.to_strengthLE (State := State) (Query := Pattern)
      (syntaxToWMFunctor.map f).down

/-- Package a syntactic transport proof as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_syntaxHom
    {A B : GFSyntaxObj} (f : A ⟶ B) :
    WMConsequenceRuleOn State Pattern where
  side := fun _ => True
  premise := syntaxQuery A
  conclusion := syntaxQuery B
  sound := by
    intro W _
    exact
      (WMQueryEq.to_strengthLE (State := State) (Query := Pattern)
        (syntaxToWMFunctor.map f).down) W

/-- Package tree-pattern equality as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_treePatternEq {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    WMConsequenceRuleOn State Pattern :=
  wmConsequenceRuleOn_of_syntaxHom (State := State)
    (syntaxHom_of_treePatternEq (hPat := hPat))

/-- Package Frege-strong compositional transport as a state-indexed WM
consequence rule endpoint. -/
def wmConsequenceRuleOn_of_fregeStrong
    (f : FunctionSig) (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map gfAbstractToPattern = args₂.map gfAbstractToPattern) :
    WMConsequenceRuleOn State Pattern :=
  wmConsequenceRuleOn_of_treePatternEq (State := State)
    (hPat := frege_strong f args₁ args₂ hargs)

end Categorical

section VisibleAndNTT

/-- Scope-ordering bridge, restated as the GF→NT endpoint. -/
noncomputable def scopeOrderingNTBridge
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {x y : String} (hne : x ≠ y)
    (φ : QFormula2) (p : Pattern) (X : PLNObj) :
    Hom (formulaToNT R I Dom env (.qexists y (.qforall x φ)) p X)
        (formulaToNT R I Dom env (.qforall x (.qexists y φ)) p X) :=
  scope_ordering_NT R I Dom env hne φ p X

/-- Positive canary: closed quantified formulas are env-invariant in the NT view. -/
theorem closedFormula_envInvariant_NT
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    (env₁ env₂ : VarEnv2) (φ : QFormula2) (hcl : closedQF2 φ) (p : Pattern)
    (X : PLNObj) :
    formulaToNT R I Dom env₁ φ p X = formulaToNT R I Dom env₂ φ p X :=
  formulaToNT_closed_env_irrel R I Dom env₁ env₂ φ hcl p X

end VisibleAndNTT

section Canaries

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Positive canary: compositional argument-pattern equality preserves WM strength. -/
theorem canary_fregeStrong_strength
    (f : FunctionSig) (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map gfAbstractToPattern = args₂.map gfAbstractToPattern) :
    ∀ W : State,
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (gfAbstractToPattern (.apply f args₁)) =
      BinaryWorldModel.queryStrength (State := State) (Query := Pattern) W
        (gfAbstractToPattern (.apply f args₂)) :=
  fregeStrong_to_strengthEq (State := State) f args₁ args₂ hargs

/-- Negative canary: garden-path parses are not syntactically collapsed. -/
theorem canary_gardenPath_patterns_distinct :
    ∃ p q : Pattern, p ≠ q :=
  ⟨_, _, garden_path_queries_differ⟩

/-- Negative canary: lexical monotonicity is not derivable from WM axioms alone. -/
theorem canary_lexicalMonotone_not_trivial
    (W : State) (p q : Pattern)
    (hlex : ∀ name, Mettapedia.Languages.GF.LinguisticInvariance.containsLexical name p = true →
      Mettapedia.Languages.GF.LinguisticInvariance.containsLexical name q = true)
    (hlt : BinaryWorldModel.evidence (State := State) (Query := Pattern) W q <
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W p) :
    ¬ LexicalEvidenceMonotone (State := State) W :=
  lexicalMono_not_trivial (State := State) W p q hlex hlt

end Canaries

end Mettapedia.Languages.GF.GFWMConnections
