import Mettapedia.Languages.GF.UniversalGrammarCore
import Mettapedia.Languages.GF.OSLFToNTT

/-!
# Selected Weakest UG Core

This file turns the shared-core story into an intrinsic weakest-core theorem.

The key move is to define a **selected invariant signature** directly, then
quotient abstract trees by agreement on all selected observations. Any
interface from which those observations can be recovered is necessarily finer,
so it factors through the selected core quotient.

This avoids the vacuity of defining “semantics-preserving” by already assuming
factorization through `semanticCore`.
-/

namespace Mettapedia.Languages.GF.UGCoreSelected

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.UniversalGrammarCore
open Mettapedia.Languages.GF.OSLFToNTT
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.CategoryTheory.NativeTypeTheory
open scoped ENNReal

universe u

/-- A selected invariant signature: labels with label-indexed observation types. -/
structure UGSignature where
  Label : Type
  Obs : Label → Type
  observe : (ℓ : Label) → AbstractNode → Obs ℓ

/-- Two trees are equal at a selected UG core iff every selected observation
agrees on them. -/
def UGCoreEq (sig : UGSignature) (t₁ t₂ : AbstractNode) : Prop :=
  ∀ ℓ, sig.observe ℓ t₁ = sig.observe ℓ t₂

theorem UGCoreEq.refl (sig : UGSignature) (t : AbstractNode) :
    UGCoreEq sig t t := by
  intro ℓ
  rfl

theorem UGCoreEq.symm (sig : UGSignature) {t₁ t₂ : AbstractNode} :
    UGCoreEq sig t₁ t₂ → UGCoreEq sig t₂ t₁ := by
  intro h ℓ
  exact (h ℓ).symm

theorem UGCoreEq.trans (sig : UGSignature) {t₁ t₂ t₃ : AbstractNode} :
    UGCoreEq sig t₁ t₂ → UGCoreEq sig t₂ t₃ → UGCoreEq sig t₁ t₃ := by
  intro h12 h23 ℓ
  exact (h12 ℓ).trans (h23 ℓ)

/-- Setoid induced by a selected invariant signature. -/
def ugCoreSetoid (sig : UGSignature) : Setoid AbstractNode where
  r := UGCoreEq sig
  iseqv := by
    constructor
    · exact UGCoreEq.refl sig
    · exact UGCoreEq.symm sig
    · exact UGCoreEq.trans sig

/-- Every selected observation descends to the selected-core quotient. -/
def UGSignature.observeOnCore (sig : UGSignature) (ℓ : sig.Label) :
    Quotient (ugCoreSetoid sig) → sig.Obs ℓ :=
  Quotient.lift (sig.observe ℓ) (by
    intro x y hxy
    exact hxy ℓ)

theorem UGSignature.observeOnCore_mk (sig : UGSignature) (ℓ : sig.Label) (t : AbstractNode) :
    sig.observeOnCore ℓ (Quotient.mk (ugCoreSetoid sig) t) = sig.observe ℓ t := rfl

/-- An interface preserves a selected signature if each selected observation can
be recovered from the interface observation. -/
structure SignaturePreservingInterface (sig : UGSignature) (Obs : Type*) where
  observe : AbstractNode → Obs
  recover : ∀ ℓ, ∃ decode : Obs → sig.Obs ℓ, ∀ t, sig.observe ℓ t = decode (observe t)

/-- Equality under any signature-preserving interface forces selected-core
equality. -/
theorem SignaturePreservingInterface.obsEq_implies_coreEq
    {sig : UGSignature} {Obs : Type*}
    (I : SignaturePreservingInterface sig Obs)
    {t₁ t₂ : AbstractNode} :
    I.observe t₁ = I.observe t₂ → UGCoreEq sig t₁ t₂ := by
  intro hObs ℓ
  rcases I.recover ℓ with ⟨decode, hdecode⟩
  rw [hdecode t₁, hdecode t₂, hObs]

/-- Every selected-signature-preserving interface quotient surjects onto the
selected-core quotient. -/
def SignaturePreservingInterface.quotientMap
    {sig : UGSignature} {Obs : Type*}
    (I : SignaturePreservingInterface sig Obs) :
    Quotient (obsSetoid I.observe) → Quotient (ugCoreSetoid sig) :=
  Quotient.lift
    (fun t => Quotient.mk (ugCoreSetoid sig) t)
    (by
      intro t₁ t₂ hObs
      exact Quotient.sound (I.obsEq_implies_coreEq hObs))

theorem SignaturePreservingInterface.quotientMap_surjective
    {sig : UGSignature} {Obs : Type*}
    (I : SignaturePreservingInterface sig Obs) :
    Function.Surjective I.quotientMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  exact ⟨Quotient.mk (obsSetoid I.observe) t, rfl⟩

/-- Weakest-core theorem for a selected invariant signature. -/
theorem UGCoreEq_selected_is_weakest
    (sig : UGSignature) {Obs : Type*}
    (I : SignaturePreservingInterface sig Obs) :
    ∃ π : Quotient (obsSetoid I.observe) → Quotient (ugCoreSetoid sig),
      Function.Surjective π := by
  exact ⟨I.quotientMap, I.quotientMap_surjective⟩

/-! ## English/Czech selected signature -/

section EnglishCzech

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Finite selected invariant family for the current English/Czech UG-core
instance. -/
inductive EnglishCzechSelectedLabel where
  | englishSem
  | czechSem
  | evidence
  | strength
  | scopeNT
  | closedNT₁
  | closedNT₂
  deriving DecidableEq

/-- Selected signature using:
1. English OSLF semantics,
2. Czech OSLF semantics,
3. WM evidence,
4. WM strength,
5. scope-ordering NTT morphism bundle,
6. closed-formula NTT object at env₁,
7. closed-formula NTT object at env₂. -/
noncomputable def englishCzechSelectedSignature
    (W : State)
    (Isem : String → Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Pattern → Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (_hcl : closedQF2 φclosed) :
    UGSignature where
  Label := EnglishCzechSelectedLabel
  Obs
    | .englishSem => Prop
    | .czechSem => Prop
    | .evidence => BinaryEvidence
    | .strength => ℝ≥0∞
    | .scopeNT => Sigma fun A : NativeTypeBundle => Sigma fun B : NativeTypeBundle => Hom A B
    | .closedNT₁ => NativeTypeBundle
    | .closedNT₂ => NativeTypeBundle
  observe
    | .englishSem => fun t =>
        sem (langReduces englishGFLanguageDef) Isem φsem (gfAbstractToPattern t)
    | .czechSem => fun t =>
        sem (langReduces czechGFLanguageDef) Isem φsem (gfAbstractToPattern t)
    | .evidence => fun t =>
        gfEvidenceDenote W t
    | .strength => fun t =>
        BinaryWorldModel.queryStrength W (gfAbstractToPattern t)
    | .scopeNT => fun t =>
        let p := gfAbstractToPattern t
        ⟨ formulaToNT Rnt Int Dom envScope (.qexists y (.qforall x φscope)) p X
        , ⟨ formulaToNT Rnt Int Dom envScope (.qforall x (.qexists y φscope)) p X
          , scope_ordering_NT Rnt Int Dom envScope hne φscope p X
          ⟩
        ⟩
    | .closedNT₁ => fun t =>
        formulaToNT Rnt Int Dom env₁ φclosed (gfAbstractToPattern t) X
    | .closedNT₂ => fun t =>
        formulaToNT Rnt Int Dom env₂ φclosed (gfAbstractToPattern t) X

/-- The selected English/Czech signature factors through the shared semantic
core. -/
noncomputable def semanticCore_preserves_englishCzechSelected
    (W : State)
    (Isem : String → Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Pattern → Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    SignaturePreservingInterface
      (englishCzechSelectedSignature W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl)
      Pattern where
  observe := semanticCore.observe
  recover
    | .englishSem =>
        ⟨fun p => sem (langReduces englishGFLanguageDef) Isem φsem p, by
          intro t
          rfl⟩
    | .czechSem =>
        ⟨fun p => sem (langReduces czechGFLanguageDef) Isem φsem p, by
          intro t
          rfl⟩
    | .evidence =>
        ⟨fun p => BinaryWorldModel.evidence W p, by
          intro t
          rfl⟩
    | .strength =>
        ⟨fun p => BinaryWorldModel.queryStrength W p, by
          intro t
          rfl⟩
    | .scopeNT =>
        ⟨fun p =>
          ⟨ formulaToNT Rnt Int Dom envScope (.qexists y (.qforall x φscope)) p X
          , ⟨ formulaToNT Rnt Int Dom envScope (.qforall x (.qexists y φscope)) p X
            , scope_ordering_NT Rnt Int Dom envScope hne φscope p X
            ⟩
          ⟩, by
            intro t
            rfl⟩
    | .closedNT₁ =>
        ⟨fun p => formulaToNT Rnt Int Dom env₁ φclosed p X, by
          intro t
          rfl⟩
    | .closedNT₂ =>
        ⟨fun p => formulaToNT Rnt Int Dom env₂ φclosed p X, by
          intro t
          rfl⟩

/-- Semantic-core equality implies equality at the selected English/Czech UG
core. -/
theorem semanticCoreEq_implies_englishCzechSelectedCoreEq
    (W : State)
    (Isem : String → Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Pattern → Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed)
    {t₁ t₂ : AbstractNode}
    (hCore : semanticCore.observe t₁ = semanticCore.observe t₂) :
    UGCoreEq
      (englishCzechSelectedSignature W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl)
      t₁ t₂ :=
  (semanticCore_preserves_englishCzechSelected
      W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ).obsEq_implies_coreEq hCore

/-- English and Czech selected observations both descend to the same selected
UG-core quotient. -/
theorem EnglishCzech_factor_through_UGCore_selected
    (W : State)
    (Isem : String → Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Pattern → Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let sig :=
      englishCzechSelectedSignature W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ∃ engLift : Quotient (ugCoreSetoid sig) → Prop,
      ∃ czeLift : Quotient (ugCoreSetoid sig) → Prop,
        ∃ evLift : Quotient (ugCoreSetoid sig) → BinaryEvidence,
          ∃ strLift : Quotient (ugCoreSetoid sig) → ℝ≥0∞,
            (∀ t, engLift (Quotient.mk (ugCoreSetoid sig) t) =
              sem (langReduces englishGFLanguageDef) Isem φsem (gfAbstractToPattern t)) ∧
            (∀ t, czeLift (Quotient.mk (ugCoreSetoid sig) t) =
              sem (langReduces czechGFLanguageDef) Isem φsem (gfAbstractToPattern t)) ∧
            (∀ t, evLift (Quotient.mk (ugCoreSetoid sig) t) = gfEvidenceDenote W t) ∧
            (∀ t, strLift (Quotient.mk (ugCoreSetoid sig) t) =
              BinaryWorldModel.queryStrength W (gfAbstractToPattern t)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (englishCzechSelectedSignature
      W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ).observeOnCore .englishSem
  · exact (englishCzechSelectedSignature
      W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ).observeOnCore .czechSem
  · exact (englishCzechSelectedSignature
      W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ).observeOnCore .evidence
  · exact (englishCzechSelectedSignature
      W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ).observeOnCore .strength
  · intro t
    rfl
  · intro t
    rfl
  · intro t
    rfl
  · intro t
    rfl

/-- The two closed-formula NTT selected views coincide pointwise, so adding both
does not artificially strengthen the English/Czech selected core. -/
theorem closedNT_selected_views_agree
    (W : State)
    (Isem : String → Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Pattern → Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed)
    (t : AbstractNode) :
    let sig :=
      englishCzechSelectedSignature W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    sig.observe .closedNT₁ t = sig.observe .closedNT₂ t := by
  dsimp [englishCzechSelectedSignature]
  simpa using formulaToNT_closed_env_irrel
    Rnt Int Dom env₁ env₂ φclosed hcl (gfAbstractToPattern t) X

end EnglishCzech

end Mettapedia.Languages.GF.UGCoreSelected
