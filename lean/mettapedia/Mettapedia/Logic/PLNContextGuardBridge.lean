import Mettapedia.Logic.WorldModelITV

/-!
# Context-Guard Bridge for WM-PLN

This file isolates the small but load-bearing context discipline used by the
WM-calc reading of PLN rules: a rule may read evidence from a posterior state
only when that state is derivable from the active context.

The point is not to introduce a second context semantics.  The bridge reuses
`WMJudgmentCtx` from `BinaryWorldModel`: context-complete examples fire via
`query_of_base`, while the empty context has no base evidence to fire from.
-/

namespace Mettapedia.Logic.PLNContextGuardBridge

open scoped ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

/-! ## A transparent query model for executable context canaries -/

/-- A one-query demo model whose extracted evidence is exactly the state. -/
inductive ContextDemoQuery where
  | observed
  deriving DecidableEq

open ContextDemoQuery

/-- The demo model exposes the state as the evidence for the sole query. -/
noncomputable instance instContextDemoWorldModel :
    BinaryWorldModel BinaryEvidence ContextDemoQuery where
  evidence W _ := W
  evidence_add _ _ _ := rfl
  evidence_zero _ := rfl

/-- A small concrete evidence packet used by the canary theorems. -/
noncomputable def demoEvidence : BinaryEvidence :=
  ⟨3, 1⟩

/-- A second evidence packet used to witness context-union composition. -/
noncomputable def demoEvidence₂ : BinaryEvidence :=
  ⟨1, 4⟩

/-- Side condition for the one-query demo rule: the active query vocabulary has
only the observed-evidence query.  This is intentionally tiny, but it keeps the
rule in the same Σ-guarded shape as real WM rewrite rules. -/
def demoRuleSide : Prop :=
  ∀ q : ContextDemoQuery, q = observed

theorem demoRuleSide_ok : demoRuleSide := by
  intro q
  cases q
  rfl

/-- The context-demo rewrite rule answers the observed query by reading the
active evidence state itself. -/
noncomputable def observedIdentityRule :
    WMRewriteRule BinaryEvidence ContextDemoQuery where
  side := demoRuleSide
  conclusion := observed
  derive W := W
  sound := by
    intro _ W
    rfl

/-! ## Generic context weakening for query and ITV judgments -/

section GenericWeakening

variable {State Query Ctx : Type*}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State]
variable [BinaryWorldModel State Query]

/-- Query judgments are monotone in the active context: adding available
sources cannot invalidate a query that already fired. -/
theorem queryJudgmentCtx_mono {Γ Δ : Set State} {W : State} {q : Query}
    {e : BinaryEvidence}
    (hSub : Γ ⊆ Δ) (h : ⊢q[Γ] W ⇓ q ↦ e) :
    ⊢q[Δ] W ⇓ q ↦ e := by
  rcases h with ⟨hW, he⟩
  exact ⟨WMJudgmentCtx.mono hSub hW, he⟩

/-- ITV judgments are monotone in the active context for the same reason:
only the state derivation depends on the context; the extracted ITV is a
deterministic view of the same state and query. -/
theorem itvJudgmentCtx_mono
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {Γ Δ : Set State} {W : State} {q : Query}
    {itv : Mettapedia.Logic.PLNIndefiniteTruth.ITV}
    (hSub : Γ ⊆ Δ)
    (h : BinaryWorldModel.WMITVJudgmentCtx
      (State := State) (Query := Query) sem ctx Γ W q itv) :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := State) (Query := Query) sem ctx Δ W q itv := by
  rcases h with ⟨hW, hitv⟩
  exact ⟨WMJudgmentCtx.mono hSub hW, hitv⟩

/-- A side-checked WM rewrite may fire after revising two states that are
separately available from the left and right context.  This is the reusable
form of the context-union canary below: composition happens through the
existing `WMJudgmentCtx.union_revise`, not through a new context semantics. -/
theorem rewriteRule_applyCtx_union_revise
    {r : WMRewriteRule State Query} {Γ₁ Γ₂ : Set State} {W₁ W₂ : State}
    (hSide : r.side) (hW₁ : ⊢wm[Γ₁] W₁) (hW₂ : ⊢wm[Γ₂] W₂) :
    ⊢q[Γ₁ ∪ Γ₂] (W₁ + W₂) ⇓ r.conclusion ↦ r.derive (W₁ + W₂) := by
  exact WMRewriteRule.applyCtx (r := r) hSide
    (WMJudgmentCtx.union_revise hW₁ hW₂)

/-- The same union-context rule firing transported through the ITV judgment
surface.  The interval value is still the existing ITV view of the derived
state; this theorem only supplies the missing context provenance. -/
theorem rewriteRule_applyITVCtx_union_revise
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRule State Query} {Γ₁ Γ₂ : Set State} {W₁ W₂ : State}
    (hSide : r.side) (hW₁ : ⊢wm[Γ₁] W₁) (hW₂ : ⊢wm[Γ₂] W₂) :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := State) (Query := Query) sem ctx (Γ₁ ∪ Γ₂)
      (W₁ + W₂) r.conclusion (sem.eval ctx (r.derive (W₁ + W₂))) := by
  exact BinaryWorldModel.WMRewriteRule.applyITVCtx
    (State := State) (Query := Query)
    sem ctx (r := r) hSide
    (WMJudgmentCtx.union_revise hW₁ hW₂)

/-- Query evidence from separately justified contexts composes under the union
context.  This is the cross-context form of `WMJudgmentCtx.query_revise`: the
evidence arithmetic is still the existing `BinaryWorldModel.evidence_add'`, and
the provenance is exactly `WMJudgmentCtx.union_revise`. -/
theorem queryJudgmentCtx_union_revise
    {Γ₁ Γ₂ : Set State} {W₁ W₂ : State} {q : Query} {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢q[Γ₁] W₁ ⇓ q ↦ e₁) (h₂ : ⊢q[Γ₂] W₂ ⇓ q ↦ e₂) :
    ⊢q[Γ₁ ∪ Γ₂] (W₁ + W₂) ⇓ q ↦ (e₁ + e₂) := by
  rcases h₁ with ⟨hW₁, rfl⟩
  rcases h₂ with ⟨hW₂, rfl⟩
  refine ⟨WMJudgmentCtx.union_revise hW₁ hW₂, ?_⟩
  simpa using
    (BinaryWorldModel.evidence_add' (State := State) (Query := Query) W₁ W₂ q).symm

/-- Cross-context query composition exposed under a larger active context.
The larger context is admissible only when it contains the union of the two
source contexts. -/
theorem queryJudgmentCtx_union_revise_of_required_subset
    {Γ₁ Γ₂ Γactive : Set State} {W₁ W₂ : State} {q : Query}
    {e₁ e₂ : BinaryEvidence}
    (hReq : Γ₁ ∪ Γ₂ ⊆ Γactive)
    (h₁ : ⊢q[Γ₁] W₁ ⇓ q ↦ e₁) (h₂ : ⊢q[Γ₂] W₂ ⇓ q ↦ e₂) :
    ⊢q[Γactive] (W₁ + W₂) ⇓ q ↦ (e₁ + e₂) :=
  queryJudgmentCtx_mono (State := State) (Query := Query) hReq
    (queryJudgmentCtx_union_revise
      (State := State) (Query := Query) h₁ h₂)

/-- Required-context firing for query judgments.  A rule may be proven using a
small required source context, then exposed under a larger active context only
when the required context is included in the active one. -/
theorem rewriteRule_applyCtx_of_required_subset
    {r : WMRewriteRule State Query} {Γreq Γactive : Set State} {W : State}
    (hReq : Γreq ⊆ Γactive) (hSide : r.side) (hW : ⊢wm[Γreq] W) :
    ⊢q[Γactive] W ⇓ r.conclusion ↦ r.derive W :=
  queryJudgmentCtx_mono (State := State) (Query := Query) hReq
    (WMRewriteRule.applyCtx (r := r) hSide hW)

/-- Required-context firing transported through the ITV view.  This is still
only context/provenance plumbing; the ITV value is the existing deterministic
view of the same state. -/
theorem rewriteRule_applyITVCtx_of_required_subset
    (sem : ITVSemantics Ctx) (ctx : Ctx)
    {r : WMRewriteRule State Query} {Γreq Γactive : Set State} {W : State}
    (hReq : Γreq ⊆ Γactive) (hSide : r.side) (hW : ⊢wm[Γreq] W) :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := State) (Query := Query) sem ctx Γactive
      W r.conclusion (sem.eval ctx (r.derive W)) :=
  itvJudgmentCtx_mono
    (State := State) (Query := Query) sem ctx hReq
    (BinaryWorldModel.WMRewriteRule.applyITVCtx
      (State := State) (Query := Query) sem ctx (r := r) hSide hW)

end GenericWeakening

/-! ## Context-complete and context-missing canaries -/

/-- If the evidence packet is in the active context, querying it returns that
packet exactly.  This is the positive "context-complete" firing case. -/
theorem contextComplete_query_exact_canary :
    ⊢q[{demoEvidence}] demoEvidence ⇓ observed ↦ demoEvidence := by
  exact WMJudgmentCtx.query_of_base {demoEvidence} demoEvidence (by simp) observed

/-- The same positive case phrased through the Σ-guarded rewrite-rule API. -/
theorem contextComplete_applyRewriteCtx_canary :
    ⊢q[{demoEvidence}] demoEvidence ⇓ observed ↦ demoEvidence := by
  exact WMRewriteRule.applyCtx
    (r := observedIdentityRule)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))

/-- A context-complete rule application lifts through the existing ITV surface.
This is the first guarded-rule firing canary: the rule is allowed to compute an
ITV only because the state is derivable from the active context and the side
condition has been checked. -/
theorem contextComplete_applyITVCtx_canary :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := BinaryEvidence) (Query := ContextDemoQuery)
      ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
      {demoEvidence} demoEvidence observed
      (ITVSemantics.walleyIDMPredictive.eval
        IDMPredictiveContext.default demoEvidence) := by
  exact BinaryWorldModel.WMRewriteRule.applyITVCtx
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
    (r := observedIdentityRule)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))

/-- Two context-derivable evidence packets can be revised under the union
context, and the same side-checked rule can fire on the revised state. -/
theorem contextUnion_applyRewriteCtx_canary :
    ⊢q[{demoEvidence} ∪ {demoEvidence₂}]
      (demoEvidence + demoEvidence₂) ⇓ observed ↦ (demoEvidence + demoEvidence₂) := by
  exact rewriteRule_applyCtx_union_revise
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    (r := observedIdentityRule)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))
    (WMJudgmentCtx.base demoEvidence₂ (by simp))

/-- The direct query-composition theorem gives the same union-context evidence
without passing through a rewrite rule. -/
theorem contextUnion_queryRevisedEvidence_canary :
    ⊢q[{demoEvidence} ∪ {demoEvidence₂}]
      (demoEvidence + demoEvidence₂) ⇓ observed ↦ (demoEvidence + demoEvidence₂) := by
  exact queryJudgmentCtx_union_revise
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    contextComplete_query_exact_canary
    (WMJudgmentCtx.query_of_base {demoEvidence₂} demoEvidence₂ (by simp) observed)

/-- A cross-context evidence query can be exposed under a larger active context
only after proving that the union of required sources is included. -/
theorem contextUnion_queryRevisedEvidence_requiredSubset_canary :
    ⊢q[{demoEvidence} ∪ {demoEvidence₂} ∪ {demoEvidence + demoEvidence₂}]
      (demoEvidence + demoEvidence₂) ⇓ observed ↦ (demoEvidence + demoEvidence₂) := by
  exact queryJudgmentCtx_union_revise_of_required_subset
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    (Γ₁ := {demoEvidence}) (Γ₂ := {demoEvidence₂})
    (Γactive := {demoEvidence} ∪ {demoEvidence₂} ∪ {demoEvidence + demoEvidence₂})
    (by
      intro W hW
      rcases hW with hW | hW
      · exact Or.inl (Or.inl hW)
      · exact Or.inl (Or.inr hW))
    contextComplete_query_exact_canary
    (WMJudgmentCtx.query_of_base {demoEvidence₂} demoEvidence₂ (by simp) observed)

/-- Context-union composition also lifts to the ITV rule surface. -/
theorem contextUnion_applyITVCtx_canary :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := BinaryEvidence) (Query := ContextDemoQuery)
      ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
      ({demoEvidence} ∪ {demoEvidence₂})
      (demoEvidence + demoEvidence₂) observed
      (ITVSemantics.walleyIDMPredictive.eval
        IDMPredictiveContext.default (demoEvidence + demoEvidence₂)) := by
  exact rewriteRule_applyITVCtx_union_revise
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
    (r := observedIdentityRule)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))
    (WMJudgmentCtx.base demoEvidence₂ (by simp))

/-- Widening the active context with an irrelevant extra evidence packet does
not invalidate an already-fired query judgment. -/
theorem contextWiden_applyRewriteCtx_canary :
    ⊢q[{demoEvidence} ∪ {demoEvidence₂}]
      demoEvidence ⇓ observed ↦ demoEvidence := by
  exact queryJudgmentCtx_mono
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    (Γ := {demoEvidence}) (Δ := {demoEvidence} ∪ {demoEvidence₂})
    (by intro W hW; exact Or.inl hW)
    contextComplete_applyRewriteCtx_canary

/-- Widening the active context also preserves the ITV rule judgment. -/
theorem contextWiden_applyITVCtx_canary :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := BinaryEvidence) (Query := ContextDemoQuery)
      ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
      ({demoEvidence} ∪ {demoEvidence₂})
      demoEvidence observed
      (ITVSemantics.walleyIDMPredictive.eval
        IDMPredictiveContext.default demoEvidence) := by
  exact itvJudgmentCtx_mono
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
    (Γ := {demoEvidence}) (Δ := {demoEvidence} ∪ {demoEvidence₂})
    (by intro W hW; exact Or.inl hW)
    contextComplete_applyITVCtx_canary

/-- Required-context firing: the rule is proved from the singleton required
context and then exposed under a larger active context containing that source. -/
theorem requiredContext_subset_applyRewriteCtx_canary :
    ⊢q[{demoEvidence} ∪ {demoEvidence₂}]
      demoEvidence ⇓ observed ↦ demoEvidence := by
  exact rewriteRule_applyCtx_of_required_subset
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    (r := observedIdentityRule)
    (Γreq := {demoEvidence}) (Γactive := {demoEvidence} ∪ {demoEvidence₂})
    (by intro W hW; exact Or.inl hW)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))

/-- The same required-context firing on the ITV surface. -/
theorem requiredContext_subset_applyITVCtx_canary :
    BinaryWorldModel.WMITVJudgmentCtx
      (State := BinaryEvidence) (Query := ContextDemoQuery)
      ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
      ({demoEvidence} ∪ {demoEvidence₂})
      demoEvidence observed
      (ITVSemantics.walleyIDMPredictive.eval
        IDMPredictiveContext.default demoEvidence) := by
  exact rewriteRule_applyITVCtx_of_required_subset
    (State := BinaryEvidence) (Query := ContextDemoQuery)
    ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
    (r := observedIdentityRule)
    (Γreq := {demoEvidence}) (Γactive := {demoEvidence} ∪ {demoEvidence₂})
    (by intro W hW; exact Or.inl hW)
    demoRuleSide_ok
    (WMJudgmentCtx.base demoEvidence (by simp))

/-- The empty context derives no `BinaryEvidence` state. -/
theorem empty_context_derives_no_state (W : BinaryEvidence) :
    ¬ ⊢wm[(∅ : Set BinaryEvidence)] W := by
  intro h
  induction h with
  | base W hW =>
      simp at hW
  | revise _ _ ih₁ _ =>
      exact ih₁

/-- With no source state in context, no query judgment can fire for the demo
packet.  This is the negative "context-missing" case. -/
theorem contextMissing_blocks_query_canary :
    ¬ ∃ e, ⊢q[(∅ : Set BinaryEvidence)] demoEvidence ⇓ observed ↦ e := by
  rintro ⟨_, hq⟩
  exact empty_context_derives_no_state demoEvidence hq.1

/-- The empty context blocks ITV rule firing for the same reason: without a
context derivation of the state, there is no context-indexed ITV judgment. -/
theorem contextMissing_blocks_ITVCtx_canary :
    ¬ ∃ itv,
      BinaryWorldModel.WMITVJudgmentCtx
        (State := BinaryEvidence) (Query := ContextDemoQuery)
        ITVSemantics.walleyIDMPredictive IDMPredictiveContext.default
        (∅ : Set BinaryEvidence) demoEvidence observed itv := by
  rintro ⟨_, hitv⟩
  exact empty_context_derives_no_state demoEvidence hitv.1

/-- Any state derived only from `demoEvidence₂` has at most as much positive as
negative evidence.  This gives a small non-empty-context negative invariant. -/
theorem wrongSourceContext_pos_le_neg {W : BinaryEvidence}
    (h : ⊢wm[{demoEvidence₂}] W) : W.pos ≤ W.neg := by
  induction h with
  | base W hW =>
      simp [demoEvidence₂] at hW
      subst W
      norm_num [demoEvidence₂]
  | revise _ _ ih₁ ih₂ =>
      exact add_le_add ih₁ ih₂

/-- A non-empty but wrong context still blocks the required source: repeatedly
revising `demoEvidence₂` cannot derive `demoEvidence`. -/
theorem requiredContext_missing_source_blocks_state_canary :
    ¬ ⊢wm[{demoEvidence₂}] demoEvidence := by
  intro h
  have hle := wrongSourceContext_pos_le_neg h
  norm_num [demoEvidence] at hle

/-- Therefore the observed rule cannot fire for `demoEvidence` when the active
context contains only the wrong source packet. -/
theorem requiredContext_missing_source_blocks_query_canary :
    ¬ ∃ e, ⊢q[{demoEvidence₂}] demoEvidence ⇓ observed ↦ e := by
  rintro ⟨_, hq⟩
  exact requiredContext_missing_source_blocks_state_canary hq.1

end Mettapedia.Logic.PLNContextGuardBridge
