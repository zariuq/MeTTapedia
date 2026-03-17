import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Logic.IdentityEvidence

/-!
# GF Identity BinaryEvidence Semantics

Identity-aware extension of the GF → OSLF → WM pipeline.

The extension is conservative by design:
- when `enabled = false`, atom/formula semantics coincide with the existing
  `WorldModelSemantics` definitions.
-/

namespace Mettapedia.Languages.GF.IdentityEvidenceSemantics

open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.IdentityEvidence
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

open scoped ENNReal

section IdentityLayer

variable {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
variable {Entity : Type*}

/-- Configuration for identity-aware semantic transport. -/
structure IdentityLayerConfig (Entity : Type*) where
  entityOf : Pattern → Entity
  idEvidence : IdEvidence Entity
  thresholds : TransportThresholds
  enabled : Bool

/-- Transfer atom evidence from `src` to `dst` using guarded identity transport. -/
noncomputable def transferAtomEvidence
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (a : String)
    (src dst : Pattern) : BinaryEvidence :=
  transportAcrossIdentityIf cfg.enabled cfg.idEvidence cfg.thresholds
    (cfg.entityOf src) (cfg.entityOf dst)
    (BinaryWorldModel.evidence W (queryOfAtom a src))

/-- Identity-aware evidence atom semantics (self-transport at each queried pattern). -/
noncomputable def gfEvidenceAtomSemFromWM_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State) : EvidenceAtomSem :=
  fun a p => transferAtomEvidence cfg W a p p

/-- Identity-aware Prop atom semantics via thresholding. -/
noncomputable def gfAtomSemFromWM_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (threshold : ℝ≥0∞) : AtomSem :=
  fun a p =>
    threshold ≤ BinaryEvidence.toStrength (gfEvidenceAtomSemFromWM_withIdentity cfg W a p)

/-- Identity-aware evidence-valued formula semantics. -/
noncomputable def gfWMFormulaSemE_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (φ : OSLFFormula)
    (p : Pattern) : BinaryEvidence :=
  semE (langReduces gfRGLLanguageDef) (gfEvidenceAtomSemFromWM_withIdentity cfg W) φ p

/-- Identity-aware Prop-valued formula semantics. -/
noncomputable def gfWMFormulaSem_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (threshold : ℝ≥0∞)
    (φ : OSLFFormula)
    (p : Pattern) : Prop :=
  sem (langReduces gfRGLLanguageDef) (gfAtomSemFromWM_withIdentity cfg W threshold) φ p

/-- Pointwise-equivalent atom interpretations induce equivalent formula semantics. -/
theorem sem_iff_of_atomSem_pointwise
    {R : Pattern → Pattern → Prop}
    {I J : AtomSem}
    (hIJ : ∀ a p, I a p ↔ J a p)
    (φ : OSLFFormula)
    (p : Pattern) :
    sem R I φ p ↔ sem R J φ p := by
  induction φ generalizing p with
  | top =>
      simp [sem]
  | bot =>
      simp [sem]
  | atom a =>
      simpa [sem] using hIJ a p
  | and φ ψ ihφ ihψ =>
      simp [sem, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [sem, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [sem, ihφ, ihψ]
  | dia φ ih =>
      constructor
      · intro h
        rcases h with ⟨q, hstep, hq⟩
        exact ⟨q, hstep, (ih q).1 hq⟩
      · intro h
        rcases h with ⟨q, hstep, hq⟩
        exact ⟨q, hstep, (ih q).2 hq⟩
  | box φ ih =>
      constructor
      · intro h q hstep
        exact (ih q).1 (h q hstep)
      · intro h q hstep
        exact (ih q).2 (h q hstep)

theorem transferAtomEvidence_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (a : String)
    (src dst : Pattern) :
    transferAtomEvidence cfg W a src dst =
      BinaryWorldModel.evidence W (queryOfAtom a src) := by
  simp [transferAtomEvidence, hdis, transportAcrossIdentityIf]

theorem gfEvidenceAtomSemFromWM_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State) :
    gfEvidenceAtomSemFromWM_withIdentity cfg W = gfEvidenceAtomSemFromWM W := by
  funext a p
  simp [gfEvidenceAtomSemFromWM_withIdentity, gfEvidenceAtomSemFromWM, wmEvidenceAtomSem,
    transferAtomEvidence_disabled, hdis]

theorem gfAtomSemFromWM_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    (a : String)
    (p : Pattern) :
    gfAtomSemFromWM_withIdentity cfg W threshold a p =
      gfAtomSemFromWM W threshold a p := by
  simp [gfAtomSemFromWM_withIdentity, gfAtomSemFromWM,
    gfEvidenceAtomSemFromWM_withIdentity, transferAtomEvidence_disabled, hdis]

/-- Conservative extension theorem (BinaryEvidence layer):
identity disabled implies no change to existing evidence semantics. -/
theorem gfWMFormulaSemE_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (φ : OSLFFormula)
    (p : Pattern) :
    gfWMFormulaSemE_withIdentity cfg W φ p = gfWMFormulaSemE W φ p := by
  simp [gfWMFormulaSemE_withIdentity, gfWMFormulaSemE,
    gfEvidenceAtomSemFromWM_withIdentity_disabled, hdis]

/-- Conservative extension theorem (Prop layer):
identity disabled implies no change to existing threshold semantics. -/
theorem gfWMFormulaSem_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    (φ : OSLFFormula)
    (p : Pattern) :
    gfWMFormulaSem_withIdentity cfg W threshold φ p ↔
      gfWMFormulaSem W threshold φ p := by
  refine sem_iff_of_atomSem_pointwise
    (R := langReduces gfRGLLanguageDef)
    (I := gfAtomSemFromWM_withIdentity cfg W threshold)
    (J := gfAtomSemFromWM W threshold)
    (hIJ := ?_) φ p
  intro a' p'
  exact Iff.intro
    (fun h =>
      by
        simpa [gfAtomSemFromWM_withIdentity_disabled (cfg := cfg) hdis (W := W)
          (threshold := threshold) (a := a') (p := p')] using h)
    (fun h =>
      by
        simpa [gfAtomSemFromWM_withIdentity_disabled (cfg := cfg) hdis (W := W)
          (threshold := threshold) (a := a') (p := p')] using h)

/-- Existing checker soundness result remains valid when identity layer is unused. -/
theorem oslf_sat_implies_wm_semantics_withIdentity_unused
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms :
      ∀ a p, I_check a p = true →
        gfAtomSemFromWM_withIdentity cfg W threshold a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing .empty gfRGLLanguageDef I_check fuel p φ = .sat) :
    gfWMFormulaSem_withIdentity cfg W threshold φ p := by
  have h_atoms_base :
      ∀ a p, I_check a p = true →
        gfAtomSemFromWM W threshold a p := by
    intro a p hc
    simpa [gfAtomSemFromWM_withIdentity_disabled, hdis] using h_atoms a p hc
  have hbase :
      gfWMFormulaSem W threshold φ p :=
    oslf_sat_implies_wm_semantics (W := W) (threshold := threshold) h_atoms_base hSat
  exact (gfWMFormulaSem_withIdentity_disabled
    (cfg := cfg) hdis (W := W) (threshold := threshold) (φ := φ) (p := p)).2 hbase

end IdentityLayer

end Mettapedia.Languages.GF.IdentityEvidenceSemantics
