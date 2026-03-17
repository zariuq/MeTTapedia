import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# PLN ↔ WM ↔ OSLF Bridge

Links the WM query-rewrite calculus (`WMRewriteRule`, `WMStrengthRule`) to
OSLF evidence semantics (`semE`, `sem`) via a generic `Query`-type bridge.

This file is a bridge layer. Canonical evidence semantics remains in
`Mettapedia.Logic.EvidenceQuantale`; `OSLFEvidenceSemantics` provides the
OSLF adapter over that carrier.

## Core Bridge (§1)

- `wmEvidenceAtomSemQ` — generic WM atom semantics (arbitrary Query type)
- `thresholdAtomSemOfWMQ` — strength-level threshold for WM queries
- Rewrite/strength rules lift to OSLF atom evidence and threshold Prop
- Revision commutation generalizes `semE_wm_atom_revision`

## ξPLN Layer (§2)

- `XiPLN` packages Σ-guarded rules + atom→query encoder
- Derivation judgments (`XiDerivesAtomEvidence`, `XiDerivesAtomStrength`)
- Soundness: derivations are OSLF-semantically sound

All theorems are fully proved (0 sorry).
-/

namespace Mettapedia.Logic.PLNWMOSLFBridge

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## §1 Core Bridge -/

section CoreBridge

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Generic atom-evidence semantics from WM queries.

Unlike `wmEvidenceAtomSem` (which hardcodes `Query = Pattern`), this works
with arbitrary `Query` types (e.g. `AtomQuery Atom`). -/
noncomputable def wmEvidenceAtomSemQ
    (W : State) (queryOfAtom : String → Pattern → Query) : EvidenceAtomSem :=
  fun a p => BinaryWorldModel.evidence W (queryOfAtom a p)

/-- Strength-level threshold atom semantics from WM queries.

An atom holds when the posterior-mean strength of the corresponding WM query
exceeds threshold `tau`. This connects to `WMStrengthRule.derive` (which
returns `ℝ≥0∞`), unlike the evidence-level `threshAtomSem` (which uses
`τ : BinaryEvidence`). -/
noncomputable def thresholdAtomSemOfWMQ
    (W : State) (tau : ℝ≥0∞) (queryOfAtom : String → Pattern → Query) : AtomSem :=
  fun a p => tau ≤ BinaryEvidence.toStrength (BinaryWorldModel.evidence W (queryOfAtom a p))

/-- Atom unfolding: `semE` of an atom under `wmEvidenceAtomSemQ` is the WM evidence
for the encoded query. -/
@[simp] theorem semE_atom_wmEvidenceAtomSemQ
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQ W queryOfAtom) (.atom a) p =
      BinaryWorldModel.evidence W (queryOfAtom a p) := rfl

/-- `WMQueryJudgment` gives the exact OSLF atom evidence when encoded via
`queryOfAtom`. -/
theorem wmQueryJudgment_semE_atom
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern) (e : BinaryEvidence)
    (hQ : WMQueryJudgment W (queryOfAtom a p) e) :
    semE R (wmEvidenceAtomSemQ W queryOfAtom) (.atom a) p = e := by
  simp [wmEvidenceAtomSemQ, hQ.2]

/-- Direct specialization of `WMRewriteRule.apply` — unchanged, but exposed
for the bridge API. -/
theorem wmRewriteRule_apply_queryJudgment
    {r : WMRewriteRule State Query} {W : State}
    (hSide : r.side) (hW : WMJudgment W) :
    WMQueryJudgment W r.conclusion (r.derive W) :=
  WMRewriteRule.apply hSide hW

/-- WM rewrite soundness transferred to OSLF atom evidence: if the atom's
query matches the rule's conclusion, the atom's evidence equals the rule's
derived value. -/
theorem wmRewriteRule_semE_atom_eq_derive
    (R : Pattern → Pattern → Prop)
    (r : WMRewriteRule State Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    semE R (wmEvidenceAtomSemQ W queryOfAtom) (.atom a) p = r.derive W := by
  simp [wmEvidenceAtomSemQ, hEnc, (r.sound hSide W).symm]

/-- Threshold consequence for an atom from a WM rewrite rule: if the derived
evidence has strength ≥ `tau`, the atom holds under strength-threshold semantics. -/
theorem wmRewriteRule_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WMRewriteRule State Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ BinaryEvidence.toStrength (r.derive W)) :
    sem R (thresholdAtomSemOfWMQ W tau queryOfAtom) (.atom a) p := by
  show tau ≤ BinaryEvidence.toStrength (BinaryWorldModel.evidence W (queryOfAtom a p))
  rw [hEnc, (r.sound hSide W).symm]
  exact hTau

/-- Strength-rule version: if the derived strength ≥ `tau`, the atom holds
under strength-threshold semantics. -/
theorem wmStrengthRule_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WMStrengthRule State Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ r.derive W) :
    sem R (thresholdAtomSemOfWMQ W tau queryOfAtom) (.atom a) p := by
  show tau ≤ BinaryEvidence.toStrength (BinaryWorldModel.evidence W (queryOfAtom a p))
  rw [hEnc, ← BinaryWorldModel.queryStrength, ← r.sound hSide W]
  exact hTau

/-- Revision commutation at atom level for the generic query encoder:
extracting atom evidence from a revised state = summing atom evidence
from each component. -/
theorem semE_wm_atom_revision_q
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State) (queryOfAtom : String → Pattern → Query)
    (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQ (W₁ + W₂) queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSemQ W₁ queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSemQ W₂ queryOfAtom) (.atom a) p := by
  simp [wmEvidenceAtomSemQ, BinaryWorldModel.evidence_add]

/-! ### Compatibility with existing Pattern-specialized bridge -/

/-- The generic bridge specializes to the existing `wmEvidenceAtomSem` when
`Query = Pattern`. -/
theorem wmEvidenceAtomSemQ_pattern_eq
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W : State) (queryOfAtom : String → Pattern → Pattern) :
    wmEvidenceAtomSemQ W queryOfAtom = wmEvidenceAtomSem W queryOfAtom := rfl

/-- The generic revision theorem specializes to `semE_wm_atom_revision` when
`Query = Pattern`. -/
theorem semE_wm_atom_revision_q_pattern_eq
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W₁ W₂ : State) (queryOfAtom : String → Pattern → Pattern)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    semE_wm_atom_revision_q R W₁ W₂ queryOfAtom a p =
      semE_wm_atom_revision W₁ W₂ queryOfAtom R a p := rfl

end CoreBridge

/-! ## §2 ξPLN Layer -/

section XiPLN

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- ξPLN packages a PLN configuration: Σ-guarded WM rules + an OSLF atom→query encoder.

This is the semantic bridge between PLN inference (operating on queries in the
WM calculus) and OSLF formula evaluation (operating on atom names + patterns). -/
structure XiPLN where
  /-- Maps OSLF atom names + patterns to WM queries. -/
  queryOfAtom : String → Pattern → Query
  /-- BinaryEvidence-level rewrite rules available in this PLN configuration. -/
  rulesE : Set (WMRewriteRule State Query)
  /-- Strength-level rules available. -/
  rulesS : Set (WMStrengthRule State Query)

/-- BinaryEvidence-level ξPLN atom derivation judgment: some rewrite rule in `Ξ`
derives evidence `e` for atom `a` at pattern `p`. -/
def XiDerivesAtomEvidence
    (Ξ : XiPLN (State := State) (Query := Query))
    (W : State) (a : String) (p : Pattern) (e : BinaryEvidence) : Prop :=
  ∃ r, r ∈ Ξ.rulesE ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    e = r.derive W

/-- Strength-level ξPLN atom derivation judgment: some strength rule in `Ξ`
derives strength `s` for atom `a` at pattern `p`. -/
def XiDerivesAtomStrength
    (Ξ : XiPLN (State := State) (Query := Query))
    (W : State) (a : String) (p : Pattern) (s : ℝ≥0∞) : Prop :=
  ∃ r, r ∈ Ξ.rulesS ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    s = r.derive W

/-- ξPLN evidence derivations are OSLF-semantically sound: if ξPLN derives
evidence `e` for atom `a`, then `semE` of that atom = `e`. -/
theorem xiDerivesAtomEvidence_sound
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidence Ξ W a p e) :
    semE R (wmEvidenceAtomSemQ W Ξ.queryOfAtom) (.atom a) p = e := by
  obtain ⟨r, _, hside, henc, rfl⟩ := hDer
  exact wmRewriteRule_semE_atom_eq_derive R r hside W Ξ.queryOfAtom a p henc

/-- ξPLN strength derivations yield threshold-Prop atom truth: if ξPLN derives
strength `s` and `tau ≤ s`, the atom holds under strength-threshold semantics. -/
theorem xiDerivesAtomStrength_threshold_sound
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {s tau : ℝ≥0∞}
    (hDer : XiDerivesAtomStrength Ξ W a p s)
    (hTau : tau ≤ s) :
    sem R (thresholdAtomSemOfWMQ W tau Ξ.queryOfAtom) (.atom a) p := by
  obtain ⟨r, _, hside, henc, rfl⟩ := hDer
  exact wmStrengthRule_threshold_atom R r hside W tau Ξ.queryOfAtom a p henc hTau

/-- ξPLN is revision-compatible at atom evidence level: extracting from a
revised state = summing from each component. -/
theorem xi_atom_revision
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State) (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQ (W₁ + W₂) Ξ.queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSemQ W₁ Ξ.queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSemQ W₂ Ξ.queryOfAtom) (.atom a) p :=
  semE_wm_atom_revision_q R W₁ W₂ Ξ.queryOfAtom a p

/-- ξPLN evidence derivations lift to `WMQueryJudgment` when the WM state is
derivable. This is the key "PLN ↔ WM" statement: a ξPLN derivation witnesses
both OSLF atom equality AND a WM query judgment. -/
theorem xiDerivesAtomEvidence_to_wmQueryJudgment
    (Ξ : XiPLN (State := State) (Query := Query))
    {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidence Ξ W a p e)
    (hW : WMJudgment W) :
    WMQueryJudgment W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hside, henc, rfl⟩ := hDer
  exact ⟨hW, by rw [henc]; exact r.sound hside W⟩

end XiPLN

/-! ## §2b ξPLN Context-Aware Layer

Lifts ξPLN derivation judgments to context-indexed WM judgments (`WMJudgmentCtx`,
`WMQueryJudgmentCtx`). This tracks which evidence sources contributed to a derivation
while preserving all OSLF soundness properties. -/

section XiPLNCtx

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- ξPLN evidence derivations lift to `WMQueryJudgmentCtx` when the WM state is
derivable from context Γ. Preserves provenance: the conclusion is only as
trustworthy as the sources in Γ. -/
theorem xiDerivesAtomEvidence_to_wmQueryJudgmentCtx
    (Ξ : XiPLN (State := State) (Query := Query))
    {Γ : Set State} {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidence Ξ W a p e)
    (hW : WMJudgmentCtx Γ W) :
    WMQueryJudgmentCtx Γ W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hside, henc, rfl⟩ := hDer
  exact ⟨hW, by rw [henc]; exact r.sound hside W⟩

/-- ξPLN evidence derivations are OSLF-semantically sound under context-indexing.
Soundness is purely about the WM semantics (not about contexts), so this follows
directly from the context-free version. -/
theorem xiDerivesAtomEvidence_sound_ctx
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {Γ : Set State} {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidence Ξ W a p e)
    (_hW : WMJudgmentCtx Γ W) :
    semE R (wmEvidenceAtomSemQ W Ξ.queryOfAtom) (.atom a) p = e :=
  xiDerivesAtomEvidence_sound Ξ R hDer

/-- ξPLN strength derivations yield threshold truth under context-indexing. -/
theorem xiDerivesAtomStrength_threshold_sound_ctx
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {Γ : Set State} {W : State} {a : String} {p : Pattern} {s tau : ℝ≥0∞}
    (hDer : XiDerivesAtomStrength Ξ W a p s)
    (hTau : tau ≤ s)
    (_hW : WMJudgmentCtx Γ W) :
    sem R (thresholdAtomSemOfWMQ W tau Ξ.queryOfAtom) (.atom a) p :=
  xiDerivesAtomStrength_threshold_sound Ξ R hDer hTau

/-- ξPLN revision under context: combining two context-derivable states yields
a state derivable from the union of contexts, with evidence additivity. -/
theorem xi_atom_revision_ctx
    (Ξ : XiPLN (State := State) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {Γ₁ Γ₂ : Set State} {W₁ W₂ : State}
    (_hW₁ : WMJudgmentCtx Γ₁ W₁) (_hW₂ : WMJudgmentCtx Γ₂ W₂)
    (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQ (W₁ + W₂) Ξ.queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSemQ W₁ Ξ.queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSemQ W₂ Ξ.queryOfAtom) (.atom a) p :=
  xi_atom_revision Ξ R W₁ W₂ a p

end XiPLNCtx

/-! ## §3 Concrete Example: d-separation rewrite through ξPLN

Instantiates ξPLN with a single `dsep_rewrite` rule and proves the full chain:
WM rewrite → atom evidence → `semE` consequence. -/

section ConcreteExample

variable {Atom State : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

/-- Example ξPLN with a single d-separation rewrite rule. -/
noncomputable def xiDsepExample
    (q₁ q₂ : AtomQuery Atom) (Sigma : Prop)
    (h : Sigma → WMQueryEq (State := State) (Query := AtomQuery Atom) q₁ q₂)
    (enc : String → Pattern → AtomQuery Atom) :
    XiPLN (State := State) (Query := AtomQuery Atom) :=
  { queryOfAtom := enc
    rulesE := {dsep_rewrite (State := State) q₁ q₂ Sigma h}
    rulesS := ∅ }

/-- End-to-end: if the atom encodes `q₂` and Σ holds, the atom evidence
equals the evidence for `q₁` (the rewritten query). -/
theorem xiDsepExample_atom_eq
    (q₁ q₂ : AtomQuery Atom) (Sigma : Prop)
    (h : Sigma → WMQueryEq (State := State) (Query := AtomQuery Atom) q₁ q₂)
    (enc : String → Pattern → AtomQuery Atom)
    (R : Pattern → Pattern → Prop)
    (a : String) (p : Pattern)
    (hEnc : enc a p = q₂) (hSigma : Sigma) (W : State) :
    semE R (wmEvidenceAtomSemQ W enc) (.atom a) p =
      BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W q₁ := by
  simp [wmEvidenceAtomSemQ, hEnc]
  exact (h hSigma W).symm

end ConcreteExample

end Mettapedia.Logic.PLNWMOSLFBridge

/-! # PLN ↔ WMΣ ↔ OSLF Bridge (Typed Queries)

Typed variant where WM queries are sort-indexed:
`Query : Srt → Type`.

Atoms are encoded into typed WM queries via:
`queryOfAtom : String → Pattern → Sigma Query`.
-/

namespace Mettapedia.Logic.PLNWMOSLFBridgeTyped

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## Core Bridge -/

section CoreBridge

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Atom-evidence semantics from typed WM queries. -/
noncomputable def wmEvidenceAtomSemQSigma
    (W : State) (queryOfAtom : String → Pattern → Sigma Query) : EvidenceAtomSem :=
  fun a p => WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p)

/-- Strength-threshold atom semantics from typed WM queries. -/
noncomputable def thresholdAtomSemOfWMQSigma
    (W : State) (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  fun a p =>
    tau ≤ BinaryEvidence.toStrength
      (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))

@[simp] theorem semE_atom_wmEvidenceAtomSemQSigma
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p =
      WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p) := rfl

/-- Typed query judgment gives exact OSLF atom evidence under the encoder. -/
theorem wmQueryJudgmentSigma_semE_atom
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) (e : BinaryEvidence)
    (hQ : WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      W (queryOfAtom a p) e) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p = e := by
  simp [wmEvidenceAtomSemQSigma, hQ.2]

/-- Typed WM rewrite soundness transferred to OSLF atom evidence. -/
theorem wmRewriteRuleSigma_semE_atom_eq_derive
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p = r.derive W := by
  simp [wmEvidenceAtomSemQSigma, hEnc, (r.sound hSide W).symm]

/-- Typed threshold consequence from an evidence-level rewrite rule. -/
theorem wmRewriteRuleSigma_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ BinaryEvidence.toStrength (r.derive W)) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau queryOfAtom)
      (.atom a) p := by
  show tau ≤ BinaryEvidence.toStrength
    (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))
  rw [hEnc, (r.sound hSide W).symm]
  exact hTau

/-- Typed threshold consequence from a strength-level rewrite rule. -/
theorem wmStrengthRuleSigma_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMStrengthRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ r.derive W) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau queryOfAtom)
      (.atom a) p := by
  show tau ≤ BinaryEvidence.toStrength
    (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))
  rw [hEnc]
  have hs :
      r.derive W =
        BinaryEvidence.toStrength
          (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W r.conclusion) := by
    simpa [WorldModelSigma.queryStrength] using (r.sound hSide W)
  rw [← hs]
  exact hTau

/-- Revision commutation at atom level for typed query encoders. -/
theorem semE_wm_atom_revision_qsigma
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) (W₁ + W₂) queryOfAtom)
      (.atom a) p =
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom)
        (.atom a) p +
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom)
        (.atom a) p := by
  simp [wmEvidenceAtomSemQSigma, WorldModelSigma.evidence_add]

end CoreBridge

/-! ## ξPLNΣ Layer -/

section XiPLNSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Typed ξPLN package: OSLF atom encoder into typed WM queries plus rule sets. -/
structure XiPLNSigma where
  queryOfAtom : String → Pattern → Sigma Query
  rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State Srt Query)
  rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State Srt Query)

/-- Typed evidence-level ξ-derivation judgment. -/
def XiDerivesAtomEvidenceSigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (W : State) (a : String) (p : Pattern) (e : BinaryEvidence) : Prop :=
  ∃ r, r ∈ Ξ.rulesE ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    e = r.derive W

/-- Typed strength-level ξ-derivation judgment. -/
def XiDerivesAtomStrengthSigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (W : State) (a : String) (p : Pattern) (s : ℝ≥0∞) : Prop :=
  ∃ r, r ∈ Ξ.rulesS ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    s = r.derive W

/-- Typed ξ evidence derivations are OSLF-semantically sound. -/
theorem xiDerivesAtomEvidenceSigma_sound
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W Ξ.queryOfAtom)
      (.atom a) p = e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact wmRewriteRuleSigma_semE_atom_eq_derive
    (State := State) (Srt := Srt) (Query := Query) R r hSide W Ξ.queryOfAtom a p hEnc

/-- Typed ξ strength derivations imply threshold truth under OSLF semantics. -/
theorem xiDerivesAtomStrengthSigma_threshold_sound
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {s tau : ℝ≥0∞}
    (hDer : XiDerivesAtomStrengthSigma Ξ W a p s)
    (hTau : tau ≤ s) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau Ξ.queryOfAtom)
      (.atom a) p := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact wmStrengthRuleSigma_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) R r hSide W tau Ξ.queryOfAtom a p hEnc hTau

/-- Typed ξ derivations lift to typed WM query judgments. -/
theorem xiDerivesAtomEvidenceSigma_to_wmQueryJudgment
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e)
    (hW : WMJudgment W) :
    WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact ⟨hW, by rw [hEnc]; exact r.sound hSide W⟩

/-- Typed ξ derivations lift to typed context-indexed WM query judgments. -/
theorem xiDerivesAtomEvidenceSigma_to_wmQueryJudgmentCtx
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    {Γ : Set State} {W : State} {a : String} {p : Pattern} {e : BinaryEvidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e)
    (hW : WMJudgmentCtx Γ W) :
    WorldModelSigma.WMQueryJudgmentCtxSigma (State := State) (Srt := Srt) (Query := Query)
      Γ W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact ⟨hW, by rw [hEnc]; exact r.sound hSide W⟩

/-- Typed ξ revision at atom-evidence level commutes with WM revision. -/
theorem xi_atom_revision_sigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State) (a : String) (p : Pattern) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) (W₁ + W₂) Ξ.queryOfAtom)
      (.atom a) p =
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₁ Ξ.queryOfAtom)
        (.atom a) p +
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₂ Ξ.queryOfAtom)
        (.atom a) p :=
  semE_wm_atom_revision_qsigma
    (State := State) (Srt := Srt) (Query := Query) R W₁ W₂ Ξ.queryOfAtom a p

end XiPLNSigma

/-! ## Concrete Sort-Judgment-Derived Encoders -/

namespace MeTTaTypeOf

/-- Sort tags derived from MeTTa `typeOf(space, atom, ty)` judgments. -/
inductive SortTag where
  | state
  | instr
  | atom
  | space
  deriving DecidableEq, Repr

/-- Type markers used by `typeOf` lookups for each sort. -/
structure SortTypeMarkers where
  stateTy : Pattern
  instrTy : Pattern
  atomTy  : Pattern
  spaceTy : Pattern

/-- Default markers aligned with `MeTTaCore.FullLanguageDef` type names. -/
def defaultMarkers : SortTypeMarkers where
  stateTy := .apply "State" []
  instrTy := .apply "Instr" []
  atomTy := .apply "Atom" []
  spaceTy := .apply "Space" []

/-- Sort/type judgment oracle (`typeOf(space, atom, ty)` semantics). -/
abbrev TypeOfJudgment := Pattern → Pattern → Pattern → Bool

/-- Concrete MeTTa-flavored syntactic judgment used as a default oracle. -/
def syntacticTypeOfJudgment : TypeOfJudgment := fun _space atom ty =>
  match ty with
  | .apply "State" [] =>
      match atom with
      | .apply "State" _ => true
      | _ => false
  | .apply "Instr" [] =>
      match atom with
      | .apply "Eval" _ => true
      | .apply "Unify" _ => true
      | .apply "Chain" _ => true
      | .apply "TypeCheck" _ => true
      | .apply "Cast" _ => true
      | .apply "Grounded1" _ => true
      | .apply "Grounded2" _ => true
      | .apply "If" _ => true
      | .apply "Return" _ => true
      | .apply "Done" _ => true
      | _ => false
  | .apply "Space" [] =>
      match atom with
      | .apply "Space" _ => true
      | _ => false
  | .apply "Atom" [] => true
  | _ => false

/-- Sort judgment induced by `typeOf` and a marker table. -/
def hasSort (judge : TypeOfJudgment) (markers : SortTypeMarkers)
    (space atom : Pattern) (s : SortTag) : Bool :=
  match s with
  | .state => judge space atom markers.stateTy
  | .instr => judge space atom markers.instrTy
  | .atom => judge space atom markers.atomTy
  | .space => judge space atom markers.spaceTy

/-- Deterministic sort inference from `typeOf` judgments. -/
def inferSort (judge : TypeOfJudgment) (markers : SortTypeMarkers)
    (space atom : Pattern) : SortTag :=
  if hasSort judge markers space atom .state then .state
  else if hasSort judge markers space atom .instr then .instr
  else if hasSort judge markers space atom .atom then .atom
  else if hasSort judge markers space atom .space then .space
  else .atom

/-- A typed query constructor per inferred sort. -/
structure QueryBuilder (Query : SortTag → Type*) where
  mkState : String → Pattern → Query .state
  mkInstr : String → Pattern → Query .instr
  mkAtom : String → Pattern → Query .atom
  mkSpace : String → Pattern → Query .space

/-- Sort-derived atom encoder from concrete `typeOf` judgments. -/
def queryOfAtomFromTypeOfWith
    {Query : SortTag → Type*}
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query := fun a p =>
  match inferSort judge markers space (subjectOf a p) with
  | .state => ⟨.state, builder.mkState a p⟩
  | .instr => ⟨.instr, builder.mkInstr a p⟩
  | .atom => ⟨.atom, builder.mkAtom a p⟩
  | .space => ⟨.space, builder.mkSpace a p⟩

/-- Common case: infer sort from the pattern argument itself. -/
def queryOfAtomFromTypeOf
    {Query : SortTag → Type*}
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query :=
  queryOfAtomFromTypeOfWith judge markers space (fun _ p => p) builder

/-- Convenience encoder using the default concrete MeTTa syntactic judgment. -/
def queryOfAtomFromSyntacticTypeOf
    {Query : SortTag → Type*}
    (markers : SortTypeMarkers := defaultMarkers)
    (space : Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query :=
  queryOfAtomFromTypeOf syntacticTypeOfJudgment markers space builder

theorem inferSort_eq_state
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = true) :
    inferSort judge markers space atom = .state := by
  simp [inferSort, hState]

theorem inferSort_eq_instr
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = true) :
    inferSort judge markers space atom = .instr := by
  simp [inferSort, hState, hInstr]

theorem inferSort_eq_atom
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = false)
    (hAtom : hasSort judge markers space atom .atom = true) :
    inferSort judge markers space atom = .atom := by
  simp [inferSort, hState, hInstr, hAtom]

theorem inferSort_eq_space
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = false)
    (hAtom : hasSort judge markers space atom .atom = false)
    (hSpace : hasSort judge markers space atom .space = true) :
    inferSort judge markers space atom = .space := by
  simp [inferSort, hState, hInstr, hAtom, hSpace]

/-- Build a typed ξPLN package whose encoder is derived from concrete
MeTTa `typeOf` judgments. -/
def xiPLNSigmaOfTypeOf
    {State : Type*} [EvidenceType State]
    {Query : SortTag → Type*}
    [WorldModelSigma State SortTag Query]
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query)
    (rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State SortTag Query))
    (rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State SortTag Query)) :
    XiPLNSigma (State := State) (Srt := SortTag) (Query := Query) where
  queryOfAtom := queryOfAtomFromTypeOfWith judge markers space subjectOf builder
  rulesE := rulesE
  rulesS := rulesS

/-- Convenience ξ-constructor using the concrete MeTTa syntactic judgment. -/
def xiPLNSigmaOfSyntacticTypeOf
    {State : Type*} [EvidenceType State]
    {Query : SortTag → Type*}
    [WorldModelSigma State SortTag Query]
    (markers : SortTypeMarkers := defaultMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query)
    (rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State SortTag Query))
    (rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State SortTag Query)) :
    XiPLNSigma (State := State) (Srt := SortTag) (Query := Query) :=
  xiPLNSigmaOfTypeOf syntacticTypeOfJudgment markers space subjectOf builder rulesE rulesS

end MeTTaTypeOf

end Mettapedia.Logic.PLNWMOSLFBridgeTyped
