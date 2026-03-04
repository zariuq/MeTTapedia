import Mettapedia.Logic.PLNWorldModel

/-!
# PLN World-Model Calculus (Query Rewrite Layer)

This module adds the **query-rewrite** layer on top of the WM calculus:

* `WMJudgment` builds/revises posterior states (`⊢wm`).
* `WMQueryJudgment` extracts evidence from derivable states (`⊢q ... ⇓ ... ↦ ...`).
* A **rewrite rule** is a *sound* derivation procedure for a query, guarded by
  explicit side conditions `Σ` (e.g., d-separation / screening-off).

This is the core template for “PLN rule = query rewrite under Σ”.
-/

namespace Mettapedia.Logic.PLNWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## Query equivalence (evidence-level) -/

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-- Two queries are equivalent if they extract identical evidence from every WM state. -/
def WMQueryEq (q₁ q₂ : Query) : Prop :=
  ∀ W : State, WorldModel.evidence (State := State) (Query := Query) W q₁ =
    WorldModel.evidence (State := State) (Query := Query) W q₂

theorem WMQueryEq.refl (q : Query) : WMQueryEq (State := State) (Query := Query) q q := by
  intro W
  rfl

theorem WMQueryEq.symm {q₁ q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
      WMQueryEq (State := State) (Query := Query) q₂ q₁ := by
  intro h W
  simpa using (h W).symm

theorem WMQueryEq.trans {q₁ q₂ q₃ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
    WMQueryEq (State := State) (Query := Query) q₂ q₃ →
      WMQueryEq (State := State) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

/-! ## Weaker bridge notions -/

/-- Evidence-preorder bridge: `q₁` is pointwise no stronger than `q₂` in extracted evidence. -/
def WMEvidenceLE (q₁ q₂ : Query) : Prop :=
  ∀ W : State,
    WorldModel.evidence (State := State) (Query := Query) W q₁ ≤
      WorldModel.evidence (State := State) (Query := Query) W q₂

theorem WMEvidenceLE.refl (q : Query) :
    WMEvidenceLE (State := State) (Query := Query) q q := by
  intro W
  exact le_rfl

theorem WMEvidenceLE.trans {q₁ q₂ q₃ : Query} :
    WMEvidenceLE (State := State) (Query := Query) q₁ q₂ →
    WMEvidenceLE (State := State) (Query := Query) q₂ q₃ →
    WMEvidenceLE (State := State) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  exact le_trans (h12 W) (h23 W)

theorem WMQueryEq.to_evidenceLE {q₁ q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
    WMEvidenceLE (State := State) (Query := Query) q₁ q₂ := by
  intro h W
  simp [h W]

theorem WMEvidenceLE.antisymm_to_WMQueryEq {q₁ q₂ : Query} :
    WMEvidenceLE (State := State) (Query := Query) q₁ q₂ →
    WMEvidenceLE (State := State) (Query := Query) q₂ q₁ →
    WMQueryEq (State := State) (Query := Query) q₁ q₂ := by
  intro h12 h21 W
  exact le_antisymm (h12 W) (h21 W)

/-- View-level equivalence: two queries agree after applying a view to extracted evidence. -/
def WMViewEq {α : Type*} (view : Evidence → α) (q₁ q₂ : Query) : Prop :=
  ∀ W : State,
    view (WorldModel.evidence (State := State) (Query := Query) W q₁) =
      view (WorldModel.evidence (State := State) (Query := Query) W q₂)

theorem WMViewEq.refl {α : Type*} (view : Evidence → α) (q : Query) :
    WMViewEq (State := State) (Query := Query) view q q := by
  intro W
  rfl

theorem WMViewEq.trans {α : Type*} (view : Evidence → α) {q₁ q₂ q₃ : Query} :
    WMViewEq (State := State) (Query := Query) view q₁ q₂ →
    WMViewEq (State := State) (Query := Query) view q₂ q₃ →
    WMViewEq (State := State) (Query := Query) view q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

theorem WMQueryEq.to_viewEq {α : Type*} (view : Evidence → α) {q₁ q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
    WMViewEq (State := State) (Query := Query) view q₁ q₂ := by
  intro h W
  simp [h W]

/-! ## Transport lemmas for standard views

These are the canonical WM transport families used by downstream APIs:

* equality transport: `to_queryStrengthWith`, `to_queryConfidence`, `to_queryInterpret`
* threshold transport: `to_queryStrengthWith_threshold`, `to_queryConfidence_threshold`

Typed `...Sigma` analogues appear in the typed section below.
-/

theorem WMQueryEq.to_queryStrength {q₁ q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
    ∀ W : State,
      WorldModel.queryStrength (State := State) (Query := Query) W q₁ =
        WorldModel.queryStrength (State := State) (Query := Query) W q₂ := by
  intro h W
  simpa [WorldModel.queryStrength] using congrArg Evidence.toStrength (h W)

theorem WMQueryEq.to_queryStrength_threshold {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q₁) :
    τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q₂ := by
  simpa [WMQueryEq.to_queryStrength (State := State) (Query := Query) h W] using hτ

theorem WMQueryEq.to_queryStrengthWith {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (ctx : BinaryContext) (W : State) :
    WorldModel.queryStrengthWith (State := State) (Query := Query) ctx W q₁ =
      WorldModel.queryStrengthWith (State := State) (Query := Query) ctx W q₂ := by
  simpa [WorldModel.queryStrengthWith] using congrArg (Evidence.strengthWith ctx) (h W)

theorem WMQueryEq.to_queryStrengthWith_threshold {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (ctx : BinaryContext) (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ WorldModel.queryStrengthWith (State := State) (Query := Query) ctx W q₁) :
    τ ≤ WorldModel.queryStrengthWith (State := State) (Query := Query) ctx W q₂ := by
  simpa [WMQueryEq.to_queryStrengthWith (State := State) (Query := Query) h ctx W] using hτ

theorem WMQueryEq.to_queryConfidence {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) :
    WorldModel.queryConfidence (State := State) (Query := Query) κ W q₁ =
      WorldModel.queryConfidence (State := State) (Query := Query) κ W q₂ := by
  simpa [WorldModel.queryConfidence] using congrArg (Evidence.toConfidence κ) (h W)

theorem WMQueryEq.to_queryConfidence_threshold {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ WorldModel.queryConfidence (State := State) (Query := Query) κ W q₁) :
    τ ≤ WorldModel.queryConfidence (State := State) (Query := Query) κ W q₂ := by
  simpa [WMQueryEq.to_queryConfidence (State := State) (Query := Query) h κ W] using hτ

theorem WMQueryEq.to_queryInterpret
    {Ctx Val : Type*}
    [InterpretableEvidence Ctx Evidence Val]
    {q₁ q₂ : Query}
    (h : WMQueryEq (State := State) (Query := Query) q₁ q₂)
    (ctx : Ctx) (W : State) :
    WorldModel.queryInterpret (State := State) (Query := Query) (Ctx := Ctx) (Val := Val) ctx W q₁ =
      WorldModel.queryInterpret (State := State) (Query := Query) (Ctx := Ctx) (Val := Val) ctx W q₂ := by
  simpa [WorldModel.queryInterpret] using
    congrArg (InterpretableEvidence.interpret ctx) (h W)

/-! ## Strength judgments (VE-facing view) -/

/-- Strength judgment: a scalar view of a query derived from a WM state. -/
def WMStrengthJudgment {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (W : State) (q : Query) (s : ℝ≥0∞) : Prop :=
  WMJudgment W ∧
    s = WorldModel.queryStrength (State := State) (Query := Query) W q

notation:50 "⊢s " W " ⇓ " q " ↦ " s => WMStrengthJudgment W q s

/-- Strength judgments are deterministic for fixed state/query. -/
theorem WMStrengthJudgment.deterministic {W : State} {q : Query} {s₁ s₂ : ℝ≥0∞}
    (h₁ : ⊢s W ⇓ q ↦ s₁) (h₂ : ⊢s W ⇓ q ↦ s₂) :
    s₁ = s₂ := by
  rcases h₁ with ⟨_, hs₁⟩
  rcases h₂ with ⟨_, hs₂⟩
  calc
    s₁ = WorldModel.queryStrength (State := State) (Query := Query) W q := hs₁
    _ = s₂ := hs₂.symm

/-! ## Strength consequence layer (inequality rules) -/

/-- Pointwise strength consequence relation between two queries. -/
def WMStrengthLE (q₁ q₂ : Query) : Prop :=
  ∀ W : State,
    WorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
      WorldModel.queryStrength (State := State) (Query := Query) W q₂

theorem WMStrengthLE.refl (q : Query) :
    WMStrengthLE (State := State) (Query := Query) q q := by
  intro W
  exact le_rfl

theorem WMStrengthLE.trans {q₁ q₂ q₃ : Query} :
    WMStrengthLE (State := State) (Query := Query) q₁ q₂ →
    WMStrengthLE (State := State) (Query := Query) q₂ q₃ →
    WMStrengthLE (State := State) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  exact le_trans (h12 W) (h23 W)

theorem WMQueryEq.to_strengthLE {q₁ q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ →
    WMStrengthLE (State := State) (Query := Query) q₁ q₂ := by
  intro h W
  simp [WMQueryEq.to_queryStrength (State := State) (Query := Query) h W]

theorem WMStrengthLE.transport_left {q₁ q₁' q₂ : Query} :
    WMQueryEq (State := State) (Query := Query) q₁ q₁' →
    WMStrengthLE (State := State) (Query := Query) q₁' q₂ →
    WMStrengthLE (State := State) (Query := Query) q₁ q₂ := by
  intro hEq hLe W
  simpa [WMQueryEq.to_queryStrength (State := State) (Query := Query) hEq W]
    using hLe W

theorem WMStrengthLE.transport_right {q₁ q₂ q₂' : Query} :
    WMStrengthLE (State := State) (Query := Query) q₁ q₂ →
    WMQueryEq (State := State) (Query := Query) q₂ q₂' →
    WMStrengthLE (State := State) (Query := Query) q₁ q₂' := by
  intro hLe hEq W
  simpa [WMQueryEq.to_queryStrength (State := State) (Query := Query) hEq W]
    using hLe W

/-- A Σ-guarded consequence rule at strength level:
under side conditions, premise strength is bounded by conclusion strength. -/
structure WMConsequenceRule (State Query : Type*) [EvidenceType State] [WorldModel State Query] where
  side : Prop
  premise : Query
  conclusion : Query
  sound : side →
    WMStrengthLE (State := State) (Query := Query) premise conclusion

namespace WMConsequenceRule

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

theorem apply {r : WMConsequenceRule State Query} {W : State} :
    r.side → (⊢wm W) →
      WorldModel.queryStrength (State := State) (Query := Query) W r.premise ≤
        WorldModel.queryStrength (State := State) (Query := Query) W r.conclusion := by
  intro hSide _hW
  exact r.sound hSide W

theorem applyCtx {r : WMConsequenceRule State Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) →
      WorldModel.queryStrength (State := State) (Query := Query) W r.premise ≤
        WorldModel.queryStrength (State := State) (Query := Query) W r.conclusion := by
  intro hSide _hW
  exact r.sound hSide W

end WMConsequenceRule

/-- A state-indexed strength consequence rule:
side conditions are checked per-state instead of globally. -/
structure WMConsequenceRuleOn (State Query : Type*) [EvidenceType State] [WorldModel State Query] where
  side : State → Prop
  premise : Query
  conclusion : Query
  sound : ∀ {W : State},
    side W →
      WorldModel.queryStrength (State := State) (Query := Query) W premise ≤
        WorldModel.queryStrength (State := State) (Query := Query) W conclusion

namespace WMConsequenceRuleOn

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-- Apply a state-indexed consequence rule to a derivable WM state. -/
theorem apply {r : WMConsequenceRuleOn State Query} {W : State} :
    r.side W → (⊢wm W) →
      WorldModel.queryStrength (State := State) (Query := Query) W r.premise ≤
        WorldModel.queryStrength (State := State) (Query := Query) W r.conclusion := by
  intro hSide _hW
  exact r.sound hSide

/-- Apply a state-indexed consequence rule to a context-derivable WM state. -/
theorem applyCtx {r : WMConsequenceRuleOn State Query} {Γ : Set State} {W : State} :
    r.side W → (⊢wm[Γ] W) →
      WorldModel.queryStrength (State := State) (Query := Query) W r.premise ≤
        WorldModel.queryStrength (State := State) (Query := Query) W r.conclusion := by
  intro hSide _hW
  exact r.sound hSide

/-- Promote a global-side consequence rule to a state-indexed one. -/
def ofGlobal (r : WMConsequenceRule State Query) : WMConsequenceRuleOn State Query where
  side := fun _ => r.side
  premise := r.premise
  conclusion := r.conclusion
  sound := by
    intro W hSide
    exact r.sound hSide W

end WMConsequenceRuleOn

/-! ## Query-rewrite rules (Σ-guarded) -/
/-! ## Query-rewrite rules (Σ-guarded) -/

/-- A query-rewrite rule: if side conditions hold, a derived evidence term
matches the WM evidence for the conclusion query. -/
structure WMRewriteRule (State Query : Type*) [EvidenceType State] [WorldModel State Query] where
  /-- Side conditions (Σ), e.g. d-separation / screening-off hypotheses. -/
  side : Prop
  /-- The conclusion query the rule answers. -/
  conclusion : Query
  /-- Evidence derived from the WM state (may use other queries internally). -/
  derive : State → Evidence
  /-- Soundness: under Σ, the derived evidence equals the WM evidence. -/
  sound : side →
    ∀ W : State,
      derive W = WorldModel.evidence (State := State) (Query := Query) W conclusion

namespace WMRewriteRule

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-- Apply a rewrite rule to a derivable WM state. -/
theorem apply {r : WMRewriteRule State Query} {W : State} :
    r.side → (⊢wm W) → (⊢q W ⇓ r.conclusion ↦ r.derive W) := by
  intro hside hW
  refine ⟨hW, ?_⟩
  exact r.sound hside W

/-- Apply a rewrite rule to a context-derivable WM state. -/
theorem applyCtx {r : WMRewriteRule State Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢q[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hside hW
  refine ⟨hW, ?_⟩
  exact r.sound hside W

end WMRewriteRule

/-! ## Example templates: Σ-guarded rewrites -/

section RewriteExamples

variable {Atom State : Type*} [EvidenceType State] [WorldModel State (PLNQuery Atom)]

/-- Generic rewrite: if `Σ` proves query equivalence, we can rewrite `q₂` to `q₁`. -/
def rewrite_of_WMQueryEq
    (Sigma : Prop) (q₁ q₂ : PLNQuery Atom)
    (h : Sigma → WMQueryEq (State := State) (Query := PLNQuery Atom) q₁ q₂) :
    WMRewriteRule State (PLNQuery Atom) :=
  { side := Sigma
    conclusion := q₂
    derive := fun W => WorldModel.evidence (State := State) (Query := PLNQuery Atom) W q₁
    sound := by
      intro hSigma W
      exact (h hSigma W) }

/-- Deduction-style rewrite template under an explicit screening-off condition `Σ`. -/
def deduction_rewrite
    (A B C : Atom) (Sigma : Prop)
    (combine : Evidence → Evidence → Evidence)
    (hsound :
      Sigma →
        ∀ W : State,
          combine
              (PLNQuery.linkEvidence (State := State) (Atom := Atom) W A B)
              (PLNQuery.linkEvidence (State := State) (Atom := Atom) W B C) =
            PLNQuery.linkEvidence (State := State) (Atom := Atom) W A C) :
    WMRewriteRule State (PLNQuery Atom) :=
  { side := Sigma
    conclusion := PLNQuery.link A C
    derive := fun W =>
      combine
        (PLNQuery.linkEvidence (State := State) (Atom := Atom) W A B)
        (PLNQuery.linkEvidence (State := State) (Atom := Atom) W B C)
    sound := by
      intro hSigma W
      exact hsound hSigma W }

/-- Screening-off rewrite template: under `Σ`, link A→C can be rewritten via B→C. -/
def screeningOff_rewrite
    (A B C : Atom) (Sigma : Prop)
    (hsound :
      Sigma →
        ∀ W : State,
          PLNQuery.linkEvidence (State := State) (Atom := Atom) W A C =
            PLNQuery.linkEvidence (State := State) (Atom := Atom) W B C) :
    WMRewriteRule State (PLNQuery Atom) :=
  { side := Sigma
    conclusion := PLNQuery.link A C
    derive := fun W =>
      PLNQuery.linkEvidence (State := State) (Atom := Atom) W B C
    sound := by
      intro hSigma W
      simpa using (hsound hSigma W).symm }

/-- D-separation-style rewrite template: `Σ` yields query equivalence. -/
def dsep_rewrite
    (q₁ q₂ : PLNQuery Atom) (Sigma : Prop)
    (h : Sigma → WMQueryEq (State := State) (Query := PLNQuery Atom) q₁ q₂) :
    WMRewriteRule State (PLNQuery Atom) :=
  rewrite_of_WMQueryEq (State := State) (Atom := Atom) Sigma q₁ q₂ h

  end RewriteExamples

/-! ## Strength judgments (context-indexed) -/

/-- Context-indexed strength judgment: a scalar view of a query from a Γ-derivable state. -/
def WMStrengthJudgmentCtx {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (Γ : Set State) (W : State) (q : Query) (s : ℝ≥0∞) : Prop :=
  WMJudgmentCtx Γ W ∧
    s = WorldModel.queryStrength (State := State) (Query := Query) W q

notation:50 "⊢s[" Γ "] " W " ⇓ " q " ↦ " s => WMStrengthJudgmentCtx Γ W q s

/-! ## Strength-rewrite rules (Σ-guarded) -/

structure WMStrengthRule (State Query : Type*) [EvidenceType State] [WorldModel State Query] where
  side : Prop
  conclusion : Query
  derive : State → ℝ≥0∞
  sound : side →
    ∀ W : State,
      derive W =
        WorldModel.queryStrength (State := State) (Query := Query) W conclusion

namespace WMStrengthRule

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

theorem apply {r : WMStrengthRule State Query} {W : State} :
    r.side → (⊢wm W) → (⊢s W ⇓ r.conclusion ↦ r.derive W) := by
  intro hside hW
  refine ⟨hW, ?_⟩
  exact r.sound hside W

/-- Apply a strength rule to a context-derivable WM state. -/
theorem applyCtx {r : WMStrengthRule State Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢s[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hside hW
  refine ⟨hW, ?_⟩
  exact r.sound hside W

end WMStrengthRule

/-! ## Typed Query Rewrite Layer (Sort-Indexed)

Typed companion using sort-indexed queries `Query : Srt → Type`
packaged as `Sigma Query`.
-/

namespace WorldModelSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-! ## Typed query equivalence -/

/-- Two typed queries are equivalent if they extract identical evidence
from every WM state. -/
def WMQueryEqSigma (q₁ q₂ : Sigma Query) : Prop :=
  ∀ W : State, WorldModelSigma.evidence W q₁ = WorldModelSigma.evidence W q₂

theorem WMQueryEqSigma.refl (q : Sigma Query) :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q q := by
  intro W
  rfl

theorem WMQueryEqSigma.symm {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₂ q₁ := by
  intro h W
  simpa using (h W).symm

theorem WMQueryEqSigma.trans {q₁ q₂ q₃ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₂ q₃ →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

theorem WMQueryEqSigma.to_queryStrength {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
      ∀ W : State, queryStrength W q₁ = queryStrength W q₂ := by
  intro h W
  simpa [queryStrength] using congrArg Evidence.toStrength (h W)

/-! ## Typed weaker bridge notions -/

/-- Typed evidence-preorder bridge: `q₁` is pointwise no stronger than `q₂` in extracted evidence. -/
def WMEvidenceLESigma (q₁ q₂ : Sigma Query) : Prop :=
  ∀ W : State, WorldModelSigma.evidence W q₁ ≤ WorldModelSigma.evidence W q₂

theorem WMEvidenceLESigma.refl (q : Sigma Query) :
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q q := by
  intro W
  exact le_rfl

theorem WMEvidenceLESigma.trans {q₁ q₂ q₃ : Sigma Query} :
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₂ q₃ →
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₁ q₃ := by
  intro h12 h23 W
  exact le_trans (h12 W) (h23 W)

theorem WMQueryEqSigma.to_evidenceLE {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ := by
  intro h W
  simp [h W]

theorem WMEvidenceLESigma.antisymm_to_WMQueryEqSigma {q₁ q₂ : Sigma Query} :
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMEvidenceLESigma (State := State) (Srt := Srt) (Query := Query) q₂ q₁ →
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ := by
  intro h12 h21 W
  exact le_antisymm (h12 W) (h21 W)

/-- Typed view-level equivalence: two queries agree after applying a view to extracted evidence. -/
def WMViewEqSigma {α : Type*} (view : Evidence → α) (q₁ q₂ : Sigma Query) : Prop :=
  ∀ W : State, view (WorldModelSigma.evidence W q₁) = view (WorldModelSigma.evidence W q₂)

theorem WMViewEqSigma.refl {α : Type*} (view : Evidence → α) (q : Sigma Query) :
    WMViewEqSigma (State := State) (Srt := Srt) (Query := Query) view q q := by
  intro W
  rfl

theorem WMViewEqSigma.trans {α : Type*} (view : Evidence → α) {q₁ q₂ q₃ : Sigma Query} :
    WMViewEqSigma (State := State) (Srt := Srt) (Query := Query) view q₁ q₂ →
    WMViewEqSigma (State := State) (Srt := Srt) (Query := Query) view q₂ q₃ →
    WMViewEqSigma (State := State) (Srt := Srt) (Query := Query) view q₁ q₃ := by
  intro h12 h23 W
  simpa [h12 W] using h23 W

theorem WMQueryEqSigma.to_viewEq {α : Type*} (view : Evidence → α) {q₁ q₂ : Sigma Query} :
    WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂ →
    WMViewEqSigma (State := State) (Srt := Srt) (Query := Query) view q₁ q₂ := by
  intro h W
  simp [h W]

/-! ## Typed transport lemmas for standard views

Typed counterparts of the untyped WM transport families:

* equality transport: `to_queryStrengthWith`, `to_queryConfidence`, `to_queryInterpret`
* threshold transport: `to_queryStrengthWith_threshold`, `to_queryConfidence_threshold`
-/

theorem WMQueryEqSigma.to_queryStrength_threshold {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ queryStrength W q₁) :
    τ ≤ queryStrength W q₂ := by
  simpa [WMQueryEqSigma.to_queryStrength (State := State) (Srt := Srt) (Query := Query) h W] using hτ

theorem WMQueryEqSigma.to_queryStrengthWith {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : BinaryContext) (W : State) :
    queryStrengthWith (State := State) (Srt := Srt) (Query := Query) ctx W q₁ =
      queryStrengthWith (State := State) (Srt := Srt) (Query := Query) ctx W q₂ := by
  simpa [queryStrengthWith] using congrArg (Evidence.strengthWith ctx) (h W)

theorem WMQueryEqSigma.to_queryStrengthWith_threshold {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : BinaryContext) (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ queryStrengthWith (State := State) (Srt := Srt) (Query := Query) ctx W q₁) :
    τ ≤ queryStrengthWith (State := State) (Srt := Srt) (Query := Query) ctx W q₂ := by
  simpa [WMQueryEqSigma.to_queryStrengthWith
    (State := State) (Srt := Srt) (Query := Query) h ctx W] using hτ

theorem WMQueryEqSigma.to_queryConfidence {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) :
    queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W q₁ =
      queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W q₂ := by
  simpa [queryConfidence] using congrArg (Evidence.toConfidence κ) (h W)

theorem WMQueryEqSigma.to_queryConfidence_threshold {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (κ : ℝ≥0∞) (W : State) (τ : ℝ≥0∞)
    (hτ : τ ≤ queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W q₁) :
    τ ≤ queryConfidence (State := State) (Srt := Srt) (Query := Query) κ W q₂ := by
  simpa [WMQueryEqSigma.to_queryConfidence
    (State := State) (Srt := Srt) (Query := Query) h κ W] using hτ

theorem WMQueryEqSigma.to_queryInterpret
    {Ctx Val : Type*}
    [InterpretableEvidence Ctx Evidence Val]
    {q₁ q₂ : Sigma Query}
    (h : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
    (ctx : Ctx) (W : State) :
    queryInterpret (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx) (Val := Val) ctx W q₁ =
      queryInterpret (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx) (Val := Val) ctx W q₂ := by
  simpa [queryInterpret] using congrArg (InterpretableEvidence.interpret ctx) (h W)

/-! ## Typed rewrite templates -/

/-- If side conditions prove typed query equivalence, rewrite `q₂` using `q₁`. -/
def rewrite_of_WMQueryEqSigma
    (Side : Prop) (q₁ q₂ : Sigma Query)
    (h : Side →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂) :
    WMRewriteRuleSigma State Srt Query :=
  { side := Side
    conclusion := q₂
    derive := fun W => WorldModelSigma.evidence W q₁
    sound := by
      intro hSide W
      exact (h hSide W) }

/-- Strength-level rewrite induced by typed query equivalence. -/
noncomputable def strengthRewrite_of_WMQueryEqSigma
    (Side : Prop) (q₁ q₂ : Sigma Query)
    (h : Side →
      WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) q₁ q₂) :
    WMStrengthRuleSigma State Srt Query :=
  { side := Side
    conclusion := q₂
    derive := fun W => queryStrength W q₁
    sound := by
      intro hSide W
      exact (WMQueryEqSigma.to_queryStrength (State := State) (Srt := Srt) (Query := Query)
        (h hSide) W) }

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
