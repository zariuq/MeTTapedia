import Mettapedia.Logic.PLNWorldModel

/-!
# PLN World Models (Sort-Indexed / Typed Query Layer)

This module adds a sort-indexed WM interface aligned with the OSLF/NTT style:
queries are typed by a sort index `Srt` via a family `Query : Srt → Type`.

The evidence carrier and revision algebra are unchanged (`EvidenceType State`).
Only the query layer is typed.
-/

namespace Mettapedia.Logic.PLNWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## Typed Interface -/

/-- Sort-indexed WM interface.

`Query` is a dependent family over sorts. For interoperability with untyped APIs,
queries are packaged as `Sigma Query`.
-/
class WorldModelSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] where
  /-- Extract binary evidence for a typed query. -/
  evidence : State → Sigma Query → Evidence
  /-- Extraction commutes with WM revision (`+`). -/
  evidence_add : ∀ W₁ W₂ q, evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q

namespace WorldModelSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Extract evidence using an explicit sort index. -/
def evidenceAt (W : State) {s : Srt} (q : Query s) : Evidence :=
  WorldModelSigma.evidence W ⟨s, q⟩

/-! ## Generic views -/

/-- Posterior-mean strength view for a typed query. -/
noncomputable def queryStrength (W : State) (q : Sigma Query) : ℝ≥0∞ :=
  Evidence.toStrength (WorldModelSigma.evidence W q)

/-- Posterior-mean strength view with explicit sort index. -/
noncomputable def queryStrengthAt (W : State) {s : Srt} (q : Query s) : ℝ≥0∞ :=
  queryStrength W ⟨s, q⟩

/-- WTV view for a typed query. -/
noncomputable def queryWTV (κ : ℝ≥0∞) (W : State) (q : Sigma Query) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (WorldModelSigma.evidence W q)

/-- WTV view with explicit sort index. -/
noncomputable def queryWTVAt (κ : ℝ≥0∞) (W : State) {s : Srt} (q : Query s) :
    PLNWeightTV.WTV :=
  queryWTV κ W ⟨s, q⟩

theorem evidence_add' (W₁ W₂ : State) (q : Sigma Query) :
    WorldModelSigma.evidence (W₁ + W₂) q =
      WorldModelSigma.evidence W₁ q + WorldModelSigma.evidence W₂ q :=
  WorldModelSigma.evidence_add W₁ W₂ q

theorem evidenceAt_add (W₁ W₂ : State) {s : Srt} (q : Query s) :
    evidenceAt (W₁ + W₂) q = evidenceAt W₁ q + evidenceAt W₂ q := by
  simpa [evidenceAt] using (evidence_add' W₁ W₂ ⟨s, q⟩)

/-! ## Typed judgments -/

/-- Typed query judgment from a derivable WM state. -/
def WMQueryJudgmentSigma
    (W : State) (q : Sigma Query) (e : Evidence) : Prop :=
  WMJudgment W ∧ e = WorldModelSigma.evidence W q

notation:50 "⊢qΣ " W " ⇓ " q " ↦ " e => WMQueryJudgmentSigma W q e

/-- Typed query judgment under a context-indexed WM derivation. -/
def WMQueryJudgmentCtxSigma
    (Γ : Set State) (W : State) (q : Sigma Query) (e : Evidence) : Prop :=
  WMJudgmentCtx Γ W ∧ e = WorldModelSigma.evidence W q

notation:50 "⊢qΣ[" Γ "] " W " ⇓ " q " ↦ " e => WMQueryJudgmentCtxSigma Γ W q e

/-- Typed strength judgment from a derivable WM state. -/
def WMStrengthJudgmentSigma
    (W : State) (q : Sigma Query) (s : ℝ≥0∞) : Prop :=
  WMJudgment W ∧ s = queryStrength W q

notation:50 "⊢sΣ " W " ⇓ " q " ↦ " s => WMStrengthJudgmentSigma W q s

/-- Typed strength judgment under a context-indexed WM derivation. -/
def WMStrengthJudgmentCtxSigma
    (Γ : Set State) (W : State) (q : Sigma Query) (s : ℝ≥0∞) : Prop :=
  WMJudgmentCtx Γ W ∧ s = queryStrength W q

notation:50 "⊢sΣ[" Γ "] " W " ⇓ " q " ↦ " s => WMStrengthJudgmentCtxSigma Γ W q s

/-! ## Typed Rewrite Rules -/

/-- Typed evidence-level rewrite rule over sort-indexed queries. -/
structure WMRewriteRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] where
  /-- Side conditions (Σ). -/
  side : Prop
  /-- The conclusion query. -/
  conclusion : Sigma Query
  /-- Derived evidence term from the WM state. -/
  derive : State → Evidence
  /-- Soundness under side conditions. -/
  sound : side → ∀ W : State, derive W = WorldModelSigma.evidence W conclusion

/-- Typed strength-level rewrite rule over sort-indexed queries. -/
structure WMStrengthRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] where
  side : Prop
  conclusion : Sigma Query
  derive : State → ℝ≥0∞
  sound : side → ∀ W : State, derive W = queryStrength W conclusion

namespace WMRewriteRuleSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

theorem apply {r : WMRewriteRuleSigma State Srt Query} {W : State} :
    r.side → (⊢wm W) → (⊢qΣ W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

theorem applyCtx {r : WMRewriteRuleSigma State Srt Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢qΣ[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

end WMRewriteRuleSigma

namespace WMStrengthRuleSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

theorem apply {r : WMStrengthRuleSigma State Srt Query} {W : State} :
    r.side → (⊢wm W) → (⊢sΣ W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

theorem applyCtx {r : WMStrengthRuleSigma State Srt Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢sΣ[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

end WMStrengthRuleSigma

/-! ## Interop Adapters -/

/-- Every typed WM induces an untyped WM over `Sigma Query`. -/
def toWorldModelSigma
    (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] :
    WorldModel State (Sigma Query) where
  evidence := WorldModelSigma.evidence
  evidence_add := WorldModelSigma.evidence_add

/-- Any untyped WM over `Sigma Query` can be viewed as a typed WM. -/
def ofWorldModelSigma
    (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModel State (Sigma Query)] :
    WorldModelSigma State Srt Query where
  evidence := WorldModel.evidence
  evidence_add := WorldModel.evidence_add

/-- Any untyped WM can be trivially typed with one sort (`PUnit`). -/
def ofWorldModelUnit
    (State : Type*) (Query : Type*)
    [EvidenceType State] [WorldModel State Query] :
    WorldModelSigma State PUnit (fun _ => Query) where
  evidence W q := WorldModel.evidence W q.2
  evidence_add W₁ W₂ q := WorldModel.evidence_add W₁ W₂ q.2

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
