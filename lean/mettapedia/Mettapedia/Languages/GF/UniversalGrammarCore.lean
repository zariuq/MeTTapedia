import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# Universal Grammar as a Shared Semantic Core

This file formalizes the strongest UG-style claim that the current GF stack
supports with clean theorem-level backing:

1. concrete language/interface observations live above a shared abstract core;
2. semantic views that depend only on `gfAbstractToPattern` factor through that
   core;
3. equality at the semantic core forces agreement on selected invariant
   judgments (pattern predicates, WM query equivalence, evidence, strength);
4. cross-linguistic surface variation can coexist with shared core semantics.

This is a **weak, formal UG** result: it is about shared abstract/semantic
structure inside the current GF architecture, not a biological or empirical
theory of all human languages.
-/

namespace Mettapedia.Languages.GF.UniversalGrammarCore

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.LinguisticInvariance
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

universe u

/-! ## Generic interface machinery -/

/-- A grammar interface is just an observation map on shared GF abstract trees. -/
structure GrammarInterface (Obs : Type*) where
  observe : AbstractNode → Obs

/-- Observation-induced equivalence. -/
def ObsEq {α β : Type*} (obs : α → β) : α → α → Prop :=
  fun x y => obs x = obs y

/-- Quotient relation induced by an observation map. -/
def obsSetoid {α β : Type*} (obs : α → β) : Setoid α where
  r := ObsEq obs
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/-- `obs` factors through `core` iff it can be written as `view ∘ core`. -/
def FactorsThrough {α β γ : Type*} (core : α → β) (obs : α → γ) : Prop :=
  ∃ view : β → γ, ∀ x, obs x = view (core x)

/-- Core equality forces equality for every observation that factors through it. -/
theorem coreEq_implies_obsEq_of_factorsThrough
    {α β γ : Type*}
    {core : α → β} {obs : α → γ}
    (hFactor : FactorsThrough core obs)
    {x y : α} :
    ObsEq core x y → ObsEq obs x y := by
  rcases hFactor with ⟨view, hview⟩
  intro hxy
  unfold ObsEq at hxy ⊢
  rw [hview x, hview y, hxy]

/-- Canonical quotient map induced by factorization through a core observation. -/
def quotientMap_of_factor
    {α β γ : Type*}
    (core : α → β) (obs : α → γ)
    (hFactor : FactorsThrough core obs) :
    Quotient (obsSetoid core) → Quotient (obsSetoid obs) :=
  Quotient.lift
    (fun x => Quotient.mk (obsSetoid obs) x)
    (by
      intro x y hxy
      exact Quotient.sound (coreEq_implies_obsEq_of_factorsThrough hFactor hxy))

/-- The quotient map induced by factorization is surjective. -/
theorem quotientMap_of_factor_surjective
    {α β γ : Type*}
    (core : α → β) (obs : α → γ)
    (hFactor : FactorsThrough core obs) :
    Function.Surjective (quotientMap_of_factor core obs hFactor) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk (obsSetoid core) x, rfl⟩

/-! ## Shared cores and concrete interfaces -/

/-- Shared abstract-tree core: the common GF abstract syntax object. -/
def abstractTreeCore : GrammarInterface AbstractNode where
  observe := id

/-- Shared semantic core: the abstract tree compiled into the GF/OSLF pattern. -/
def semanticCore : GrammarInterface Pattern where
  observe := gfAbstractToPattern

/-- The semantic core trivially factors through the abstract-tree core. -/
theorem semanticCore_factorsThrough_abstractTree :
    FactorsThrough abstractTreeCore.observe semanticCore.observe := by
  refine ⟨gfAbstractToPattern, ?_⟩
  intro t
  rfl

/-- A semantics-preserving interface is any observation on abstract trees that
factors through the shared semantic core. -/
structure SemanticsPreservingInterface (Obs : Type*) where
  observe : AbstractNode → Obs
  factorsThroughSemanticCore : FactorsThrough semanticCore.observe observe

/-- Trees equal at the semantic core are observationally indistinguishable for
every semantics-preserving interface. -/
theorem SemanticsPreservingInterface.coreEq_implies_agreement
    {Obs : Type*} (I : SemanticsPreservingInterface Obs)
    {t₁ t₂ : AbstractNode} :
    semanticCore.observe t₁ = semanticCore.observe t₂ →
      I.observe t₁ = I.observe t₂ :=
  coreEq_implies_obsEq_of_factorsThrough I.factorsThroughSemanticCore

/-- Every semantics-preserving interface receives a canonical surjective
quotient map from the semantic-core quotient. -/
def SemanticsPreservingInterface.quotientMap
    {Obs : Type*} (I : SemanticsPreservingInterface Obs) :
    Quotient (obsSetoid semanticCore.observe) → Quotient (obsSetoid I.observe) :=
  quotientMap_of_factor semanticCore.observe I.observe I.factorsThroughSemanticCore

/-- The canonical quotient map for a semantics-preserving interface is
surjective. -/
theorem SemanticsPreservingInterface.quotientMap_surjective
    {Obs : Type*} (I : SemanticsPreservingInterface Obs) :
    Function.Surjective I.quotientMap :=
  quotientMap_of_factor_surjective _ _ _

/-! ## Semantic views that factor through the GF semantic core -/

section SemanticViews

variable (φ : Pattern → Prop)

/-- Any predicate on compiled GF patterns is a semantic-core view. -/
def predicateView : GrammarInterface Prop where
  observe := fun t => φ (semanticCore.observe t)

theorem predicateView_factorsThrough_semanticCore :
    FactorsThrough semanticCore.observe (predicateView φ).observe := by
  refine ⟨φ, ?_⟩
  intro t
  rfl

/-- Any predicate on compiled GF patterns yields a semantics-preserving
interface. -/
def predicateInterface : SemanticsPreservingInterface Prop where
  observe := (predicateView φ).observe
  factorsThroughSemanticCore := predicateView_factorsThrough_semanticCore φ

end SemanticViews

section GenericWM

variable {State : Type u} [EvidenceType State] [WorldModel State Pattern]

/-- World-model evidence as a semantic-core view. -/
noncomputable def evidenceView (W : State) : GrammarInterface Mettapedia.Logic.EvidenceQuantale.Evidence where
  observe := fun t => gfEvidenceDenote W t

theorem evidenceView_factorsThrough_semanticCore (W : State) :
    FactorsThrough semanticCore.observe (evidenceView W).observe := by
  refine ⟨fun p => WorldModel.evidence W p, ?_⟩
  intro t
  rfl

/-- Evidence extraction at a fixed state is a semantics-preserving interface. -/
noncomputable def evidenceInterface (W : State) :
    SemanticsPreservingInterface Mettapedia.Logic.EvidenceQuantale.Evidence where
  observe := (evidenceView W).observe
  factorsThroughSemanticCore := evidenceView_factorsThrough_semanticCore W

/-- World-model strength as a semantic-core view. -/
noncomputable def strengthView (W : State) : GrammarInterface ℝ≥0∞ where
  observe := fun t => WorldModel.queryStrength W (gfAbstractToPattern t)

theorem strengthView_factorsThrough_semanticCore (W : State) :
    FactorsThrough semanticCore.observe (strengthView W).observe := by
  refine ⟨fun p => WorldModel.queryStrength W p, ?_⟩
  intro t
  rfl

/-- Strength extraction at a fixed state is a semantics-preserving interface. -/
noncomputable def strengthInterface (W : State) :
    SemanticsPreservingInterface ℝ≥0∞ where
  observe := (strengthView W).observe
  factorsThroughSemanticCore := strengthView_factorsThrough_semanticCore W

/-- Core equality preserves every predicate on compiled GF patterns. -/
theorem semanticCoreEq_implies_predicateAgreement
    {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂)
    (φ : Pattern → Prop) :
    φ (semanticCore.observe t₁) ↔ φ (semanticCore.observe t₂) := by
  have hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂ := by
    simpa [semanticCore] using hCore
  simp [semanticCore, hPat]

/-- Core equality gives WM query equivalence. -/
theorem semanticCoreEq_implies_queryEq
    {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    WMQueryEq (State := State) (Query := Pattern)
      (semanticCore.observe t₁) (semanticCore.observe t₂) := by
  have hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂ := by
    simpa [semanticCore] using hCore
  intro W
  simpa [semanticCore] using congrArg (WorldModel.evidence W) hPat

/-- Core equality preserves evidence in every world-model state. -/
theorem semanticCoreEq_implies_evidenceAgreement
    {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    ∀ W : State, gfEvidenceDenote W t₁ = gfEvidenceDenote W t₂ := by
  have hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂ := by
    simpa [semanticCore] using hCore
  exact translation_preserves_evidence_allW (State := State) hPat

/-- Core equality preserves strength in every world-model state. -/
theorem semanticCoreEq_implies_strengthAgreement
    {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    ∀ W : State,
      WorldModel.queryStrength W (semanticCore.observe t₁) =
        WorldModel.queryStrength W (semanticCore.observe t₂) := by
  have hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂ := by
    simpa [semanticCore] using hCore
  intro W
  simpa [semanticCore] using congrArg (WorldModel.queryStrength W) hPat

end GenericWM

/-! ## Cross-linguistic witness theorems -/

/-- English and Czech agree on OSLF semantics over the shared semantic core. -/
theorem english_czech_share_core_semantics
    (I : String → Pattern → Prop) (φ : OSLFFormula) (tree : AbstractNode) :
    sem (langReduces englishGFLanguageDef) I φ (semanticCore.observe tree) ↔
    sem (langReduces czechGFLanguageDef) I φ (semanticCore.observe tree) := by
  simpa [semanticCore] using english_czech_tree_sem_iff I φ tree

/-- Witness: the same abstract tree can have different cross-linguistic
surface forms while retaining identical OSLF semantics at the shared core. -/
theorem theBigHouse_surface_variation_with_shared_core_semantics
    (I : String → Pattern → Prop) (φ : OSLFFormula) :
    theBigHouse_pair.englishSurface ≠ theBigHouse_pair.czechSurface ∧
      (sem (langReduces englishGFLanguageDef) I φ
          (semanticCore.observe theBigHouse_pair.tree) ↔
        sem (langReduces czechGFLanguageDef) I φ
          (semanticCore.observe theBigHouse_pair.tree)) := by
  refine ⟨cross_ling_surfaces_differ.2, ?_⟩
  simpa [semanticCore] using english_czech_tree_sem_iff I φ theBigHouse_pair.tree

/-- The selected shared semantic core is nontrivial. -/
theorem semanticCore_nontrivial :
    ∃ t₁ t₂ : AbstractNode, semanticCore.observe t₁ ≠ semanticCore.observe t₂ := by
  refine ⟨theCat_pair.tree, theBigHouse_pair.tree, ?_⟩
  intro h
  simp [semanticCore,
    theCat_pair, theBigHouse_pair,
    Typing.mkApp2, Typing.mkApp1, Typing.mkLeaf] at h

/-- The quotient of trees by semantic-core equality canonically surjects onto
any observation that factors through the semantic core. -/
theorem semanticCore_quotient_surjects_onto_predicateView
    (φ : Pattern → Prop) :
    Function.Surjective
      (quotientMap_of_factor semanticCore.observe (predicateView φ).observe
        (predicateView_factorsThrough_semanticCore φ)) :=
  quotientMap_of_factor_surjective _ _ _

end Mettapedia.Languages.GF.UniversalGrammarCore
