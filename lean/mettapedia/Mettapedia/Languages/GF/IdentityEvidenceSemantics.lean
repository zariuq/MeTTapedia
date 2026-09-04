import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.PLN.Evidence.IdentityEvidence

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
open Mettapedia.Languages.GF.EquationCanonicalSection
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.IdentityEvidence
open Mettapedia.OSLF.Framework.EvidenceSemantics
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

/-- Identity-aware evidence atom semantics.  The identity transport is queried
at the computable representative of the GF equation class, so this is a
semantic observation rather than a predicate on a chosen presentation. -/
noncomputable def gfEvidenceAtomSemFromWM_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State) : EquationEvidenceAtomSem gfLegacySemanticLanguageDef :=
  canonicalEvidenceAtomSem gfLegacySemanticLanguageDef gfEquationSection
    (fun atom term => transferAtomEvidence cfg W atom term term)

/-- Identity-aware Prop atom semantics via thresholding. -/
noncomputable def gfAtomSemFromWM_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (threshold : ℝ≥0∞) : EquationAtomSem gfLegacySemanticLanguageDef :=
  fun atom =>
    ⟨fun term => threshold ≤ BinaryEvidence.toStrength
        ((gfEvidenceAtomSemFromWM_withIdentity cfg W atom).1 term), by
      intro left right equivalent
      change (threshold ≤ BinaryEvidence.toStrength
          ((gfEvidenceAtomSemFromWM_withIdentity cfg W atom).1 left)) ↔
        threshold ≤ BinaryEvidence.toStrength
          ((gfEvidenceAtomSemFromWM_withIdentity cfg W atom).1 right)
      rw [(gfEvidenceAtomSemFromWM_withIdentity cfg W atom).2 equivalent]⟩

/-- Identity-aware evidence-valued formula semantics. -/
noncomputable def gfWMFormulaSemE_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (φ : OSLFFormula)
    (p : Pattern) : BinaryEvidence :=
  langSemE gfLegacySemanticLanguageDef
    (gfEvidenceAtomSemFromWM_withIdentity cfg W) φ p

/-- Identity-aware Prop-valued formula semantics. -/
noncomputable def gfWMFormulaSem_withIdentity
    (cfg : IdentityLayerConfig Entity)
    (W : State)
    (threshold : ℝ≥0∞)
    (φ : OSLFFormula)
    (p : Pattern) : Prop :=
  langFormulaSem gfLegacySemanticLanguageDef
    (gfAtomSemFromWM_withIdentity cfg W threshold) φ p

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
  funext atom
  apply Subtype.ext
  funext term
  simp [gfEvidenceAtomSemFromWM_withIdentity, gfEvidenceAtomSemFromWM,
    canonicalEvidenceAtomSem, canonicalEvidenceAtomSemUsing, wmEvidenceAtomSem,
    transferAtomEvidence_disabled, hdis]

theorem gfAtomSemFromWM_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞) :
    gfAtomSemFromWM_withIdentity cfg W threshold =
      gfEquationAtomSemFromWM W threshold := by
  funext atom
  apply Subtype.ext
  funext term
  change (threshold ≤ BinaryEvidence.toStrength
      ((gfEvidenceAtomSemFromWM_withIdentity cfg W atom).1 term)) =
    (threshold ≤ BinaryEvidence.toStrength
      ((gfEvidenceAtomSemFromWM W atom).1 term))
  rw [gfEvidenceAtomSemFromWM_withIdentity_disabled cfg hdis W]

/-- Conservative extension theorem (BinaryEvidence layer):
identity disabled implies no change to existing evidence semantics. -/
theorem gfWMFormulaSemE_withIdentity_disabled
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (φ : OSLFFormula)
    (p : Pattern) :
    gfWMFormulaSemE_withIdentity cfg W φ p = gfWMFormulaSemE W φ p := by
  rw [gfWMFormulaSemE_withIdentity, gfWMFormulaSemE,
    gfEvidenceAtomSemFromWM_withIdentity_disabled cfg hdis W]

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
  rw [gfWMFormulaSem_withIdentity, gfWMFormulaSem,
    gfAtomSemFromWM_withIdentity_disabled cfg hdis W threshold]

/-- Existing checker soundness result remains valid when identity layer is unused. -/
theorem oslf_sat_implies_wm_semantics_withIdentity_unused
    (cfg : IdentityLayerConfig Entity)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms :
      ∀ a p, I_check a p = true →
        (gfAtomSemFromWM_withIdentity cfg W threshold a).1 p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing .empty gfLegacySemanticLanguageDef I_check fuel p φ = .sat) :
    gfWMFormulaSem_withIdentity cfg W threshold φ p := by
  have h_atoms_base :
      ∀ a p, I_check a p = true →
        gfAtomSemFromWM W threshold a p := by
    intro a p hc
    have atomSemEqual := congrFun
      (gfAtomSemFromWM_withIdentity_disabled cfg hdis W threshold) a
    have holds := h_atoms a p hc
    rw [atomSemEqual] at holds
    simpa [gfEquationAtomSemFromWM] using holds
  have hbase :
      gfWMFormulaSem W threshold φ p :=
    oslf_sat_implies_wm_semantics (W := W) (threshold := threshold) h_atoms_base hSat
  exact (gfWMFormulaSem_withIdentity_disabled
    (cfg := cfg) hdis (W := W) (threshold := threshold) (φ := φ) (p := p)).2 hbase

end IdentityLayer

end Mettapedia.Languages.GF.IdentityEvidenceSemantics
