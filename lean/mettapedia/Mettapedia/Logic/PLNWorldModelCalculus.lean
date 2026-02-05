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

/-! ## Strength judgments (VE-facing view) -/

/-- Strength judgment: a scalar view of a query derived from a WM state. -/
def WMStrengthJudgment {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (W : State) (q : Query) (s : ℝ≥0∞) : Prop :=
  WMJudgment W ∧
    s = WorldModel.queryStrength (State := State) (Query := Query) W q

notation:50 "⊢s " W " ⇓ " q " ↦ " s => WMStrengthJudgment W q s

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

end WMRewriteRule

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

end WMStrengthRule

end Mettapedia.Logic.PLNWorldModel
