import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.IdentityEvidence

/-!
# Identity BinaryEvidence Transfer (Framework-Level)

Generic OSLF semantic transfer wrapper for guarded identity-evidence layers.

This module is intentionally independent of GF/Pi/Rho internals. It provides:
- an identity-aware atom semantics constructor over any `BinaryWorldModel`,
- conservative disabled-mode equivalence (`enabled = false`),
- checker-soundness reuse through the disabled-mode bridge.
-/

namespace Mettapedia.OSLF.Framework.IdentityEvidenceTransfer

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.IdentityEvidence
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

open scoped ENNReal

section Generic

variable {State : Type*} [EvidenceType State]
variable {Query Entity : Type*} [BinaryWorldModel State Query]

/-- Generic identity layer config for atom/query transport. -/
structure IdentityAtomLayerConfig (Entity Query : Type*) where
  entityOf : Pattern → Entity
  queryOfAtom : String → Pattern → Query
  idEvidence : IdEvidence Entity
  thresholds : TransportThresholds
  enabled : Bool

/-- Generic guarded identity transport for atom evidence. -/
noncomputable def transferAtomEvidence
    (cfg : IdentityAtomLayerConfig Entity Query)
    (W : State)
    (a : String)
    (src dst : Pattern) : BinaryEvidence :=
  transportAcrossIdentityIf cfg.enabled cfg.idEvidence cfg.thresholds
    (cfg.entityOf src) (cfg.entityOf dst)
    (BinaryWorldModel.evidence W (cfg.queryOfAtom a src))

/-- Base (non-identity) threshold atom semantics. -/
noncomputable def atomSemBase
    (cfg : IdentityAtomLayerConfig Entity Query)
    (W : State)
    (threshold : ℝ≥0∞) : AtomSem :=
  fun a p => threshold ≤ BinaryEvidence.toStrength (BinaryWorldModel.evidence W (cfg.queryOfAtom a p))

/-- Identity-aware threshold atom semantics. -/
noncomputable def atomSemWithIdentity
    (cfg : IdentityAtomLayerConfig Entity Query)
    (W : State)
    (threshold : ℝ≥0∞) : AtomSem :=
  fun a p => threshold ≤ BinaryEvidence.toStrength (transferAtomEvidence cfg W a p p)

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
    (cfg : IdentityAtomLayerConfig Entity Query)
    (hdis : cfg.enabled = false)
    (W : State)
    (a : String)
    (src dst : Pattern) :
    transferAtomEvidence cfg W a src dst =
      BinaryWorldModel.evidence W (cfg.queryOfAtom a src) := by
  simp [transferAtomEvidence, hdis, transportAcrossIdentityIf]

theorem atomSemWithIdentity_disabled
    (cfg : IdentityAtomLayerConfig Entity Query)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    (a : String)
    (p : Pattern) :
    atomSemWithIdentity cfg W threshold a p =
      atomSemBase cfg W threshold a p := by
  simp [atomSemWithIdentity, atomSemBase, transferAtomEvidence_disabled, hdis]

/-- Generic conservative extension theorem:
`enabled = false` recovers base OSLF semantics for all formulas. -/
theorem sem_withIdentity_disabled_iff
    (cfg : IdentityAtomLayerConfig Entity Query)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula)
    (p : Pattern) :
    sem R (atomSemWithIdentity cfg W threshold) φ p ↔
      sem R (atomSemBase cfg W threshold) φ p := by
  refine sem_iff_of_atomSem_pointwise
    (R := R)
    (I := atomSemWithIdentity cfg W threshold)
    (J := atomSemBase cfg W threshold)
    (hIJ := ?_) φ p
  intro a p'
  exact Iff.intro
    (fun h =>
      by
        simpa [atomSemWithIdentity_disabled (cfg := cfg) hdis (W := W)
          (threshold := threshold) (a := a) (p := p')] using h)
    (fun h =>
      by
        simpa [atomSemWithIdentity_disabled (cfg := cfg) hdis (W := W)
          (threshold := threshold) (a := a) (p := p')] using h)

/-- Framework-level checker bridge:
reuse `checkLangUsing_sat_sound` with identity disabled. -/
theorem checkLangUsing_sat_sound_withIdentity_unused
    {relEnv : RelationEnv}
    (cfg : IdentityAtomLayerConfig Entity Query)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    {lang : LanguageDef}
    {I_check : AtomCheck}
    (h_atoms :
      ∀ a p, I_check a p = true →
        atomSemWithIdentity cfg W threshold a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing relEnv lang I_check fuel p φ = .sat) :
    sem (langReducesUsing relEnv lang) (atomSemWithIdentity cfg W threshold) φ p := by
  have h_atoms_base :
      ∀ a p, I_check a p = true →
        atomSemBase cfg W threshold a p := by
    intro a p hc
    simpa [atomSemWithIdentity_disabled, hdis] using h_atoms a p hc
  have hbase :
      sem (langReducesUsing relEnv lang) (atomSemBase cfg W threshold) φ p :=
    checkLangUsing_sat_sound (relEnv := relEnv) (lang := lang)
      (I_check := I_check) (I_sem := atomSemBase cfg W threshold) h_atoms_base hSat
  exact (sem_withIdentity_disabled_iff
    (cfg := cfg) hdis (W := W) (threshold := threshold)
    (R := langReducesUsing relEnv lang) (φ := φ) (p := p)).2 hbase

/-- Canonical framework endpoint packaging disabled-mode semantic transfer. -/
theorem identity_semantic_transfer_endpoint
    (cfg : IdentityAtomLayerConfig Entity Query)
    (hdis : cfg.enabled = false)
    (W : State)
    (threshold : ℝ≥0∞)
    (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula)
    (p : Pattern) :
    (sem R (atomSemWithIdentity cfg W threshold) φ p ↔
      sem R (atomSemBase cfg W threshold) φ p) := by
  exact sem_withIdentity_disabled_iff
    (cfg := cfg) hdis (W := W) (threshold := threshold) (R := R) (φ := φ) (p := p)

end Generic

end Mettapedia.OSLF.Framework.IdentityEvidenceTransfer
