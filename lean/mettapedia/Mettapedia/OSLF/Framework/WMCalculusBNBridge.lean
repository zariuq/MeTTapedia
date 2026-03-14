import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge

/-!
# WM Calculus — Bayesian Network Compiled Inference Bridge

Bridges the guarded WM rewrite calculus (Pattern-level) with Bayesian network
d-separation (oracle-level). Three BN motifs:

1. **Chain (A → B → C)**: d-separated queries use guarded forgetting (positive).
2. **Fork (A ← B → C)**: symmetric d-separation enables guarded forgetting (positive).
3. **Collider (A → C ← B)**: no d-separation, guarded forgetting blocked (negative).

The guarded rule `ruleForgetOutsideGuarded` has premise
`[.relationQuery "outsideScope" [.fvar "S", .fvar "q"]]`.
A `RelationEnv` answers `outsideScope(S, q)` when `q` is d-separated from scope `S`.

Architecture:
- **Positive** (`guarded_forget_of_dsep`): Parametric in the oracle.
  Given ANY `RelationEnv` that satisfies the outsideScope premise,
  the guarded forgetting rule fires. The specific BN structure
  (chain, fork) determines which oracles are sound.
- **Negative** (`collider_premise_empty`): With `RelationEnv.empty`,
  the premise evaluation returns `[]`, blocking the rule entirely.
  This models the collider motif where no d-separation holds.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusBNBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge

/-! ## §1: Rule Membership -/

/-- `ruleForgetOutsideGuarded` is in the guarded ext vertex rule set
    when forgetting is enabled (scopeBased or supportTracked). -/
theorem ruleForgetOutsideGuarded_mem_guarded (v : WMExtVertex)
    (hf : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked) :
    ruleForgetOutsideGuarded ∈ (wmExtVertexLanguageDefGuarded v).rewrites := by
  simp only [wmExtVertexLanguageDefGuarded, List.mem_append]
  cases hf with
  | inl h => rw [h]; simp [forgettingRulesGuarded]
  | inr h => rw [h]; simp [forgettingRulesGuarded]

/-! ## §2: Positive Theorem — Guarded Forgetting Fires (Parametric)

The key positive theorem: given ANY `RelationEnv` that satisfies the
`outsideScope(S, q)` premise, the guarded forgetting rule fires.

This is parametric in the oracle — the specific BN motif (chain, fork)
determines which oracles are sound for a given network topology.
The calculus only cares that the oracle answers positively. -/

/-- Under any RelationEnv that satisfies the outsideScope premise,
    the guarded forgetting rule fires:
    `Extract(Forget(S, W), q) ↦ Extract(W, q)`.

    The hypothesis `hprem` witnesses that the oracle provides a
    d-separation certificate for query `q` outside scope `S`. -/
theorem guarded_forget_of_dsep
    (v : WMExtVertex) (hf : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked)
    (relEnv : RelationEnv) (pS pW pq : Pattern)
    (hprem : [("q", pq), ("W", pW), ("S", pS)] ∈
      applyPremisesWithEnv relEnv (wmExtVertexLanguageDefGuarded v)
        ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)]) :
    langReducesUsing relEnv
      (wmExtVertexLanguageDefGuarded v)
      (pExtract (pForget pS pW) pq)
      (pExtract pW pq) := by
  unfold langReducesUsing
  exact DeclReducesWithPremises.topRule
    (relEnv := relEnv)
    (lang := wmExtVertexLanguageDefGuarded v)
    (r := ruleForgetOutsideGuarded)
    (ruleForgetOutsideGuarded_mem_guarded v hf)
    [("q", pq), ("W", pW), ("S", pS)]
    (by simp [ruleForgetOutsideGuarded, pExtract, pForget, matchPattern, matchArgs, mergeBindings])
    [("q", pq), ("W", pW), ("S", pS)]
    hprem
    (by simp [ruleForgetOutsideGuarded, pExtract, applyBindings])

/-- Existential form: there EXISTS a RelationEnv under which guarded forgetting fires.
    This witnesses that the guarded rule is not vacuous — it CAN fire with
    the right d-separation oracle. -/
theorem guarded_forget_possible
    (v : WMExtVertex) (hf : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked)
    (pS pW pq : Pattern)
    (hprem : ∃ relEnv : RelationEnv,
      [("q", pq), ("W", pW), ("S", pS)] ∈
        applyPremisesWithEnv relEnv (wmExtVertexLanguageDefGuarded v)
          ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)]) :
    ∃ relEnv : RelationEnv,
      langReducesUsing relEnv
        (wmExtVertexLanguageDefGuarded v)
        (pExtract (pForget pS pW) pq)
        (pExtract pW pq) := by
  obtain ⟨relEnv, hprem⟩ := hprem
  exact ⟨relEnv, guarded_forget_of_dsep v hf relEnv pS pW pq hprem⟩

/-! ## §3: Negative Theorem — Collider Blocks Forgetting

With `RelationEnv.empty`, the `outsideScope` premise can never be satisfied.
This models the collider BN A→C←B where A and B are NOT d-separated
(without conditioning on C, "explaining away" creates dependence). -/

/-- With the empty oracle, the outsideScope premise evaluation returns `[]`.
    No bindings survive, so `ruleForgetOutsideGuarded` cannot fire. -/
theorem collider_premise_empty (v : WMExtVertex) (pS pW pq : Pattern) :
    applyPremisesWithEnv RelationEnv.empty (wmExtVertexLanguageDefGuarded v)
      ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)] = [] := by
  simp [applyPremisesWithEnv, ruleForgetOutsideGuarded, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, RelationEnv.empty,
        applyBindings, mergeBindings]

/-- Corollary: no bindings satisfy the outsideScope premise under the empty oracle. -/
theorem collider_no_premise_satisfaction (v : WMExtVertex) (pS pW pq : Pattern)
    (bs : Bindings) :
    bs ∉ applyPremisesWithEnv RelationEnv.empty (wmExtVertexLanguageDefGuarded v)
      ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)] := by
  rw [collider_premise_empty]; exact List.not_mem_nil

/-! ## §4: Evidence-Add Core Rules (Oracle-Independent)

Core rules like `ruleEvidenceAdd` have empty premises and therefore
work under any `RelationEnv`, including `RelationEnv.empty`. These
theorems lift the existing evidence-add chain from `WMCalculusOSLFBridge`. -/

/-- Guarded reductions under `RelationEnv.empty` lift to any `RelationEnv`.
    Core rules (evidence-add, combine, etc.) have empty premises. -/
theorem guarded_reduction_lifts_relEnv
    {relEnv : RelationEnv} {lang : LanguageDef}
    {p q : Pattern}
    (hred : langReducesUsing RelationEnv.empty lang p q) :
    langReducesUsing relEnv lang p q := by
  unfold langReducesUsing at hred ⊢
  exact declReducesWithPremises_mono_relEnv
    (fun _ _ t ht => absurd ht (by simp [RelationEnv.empty]))
    hred

/-- The evidence-add chain fires under any RelationEnv since it uses
    only core rules (no premises).
    `Extract(Revise(Revise(W₁,W₂), W₃), q)` →*
    `Combine(Combine(Extract(W₁,q), Extract(W₂,q)), Extract(W₃,q))`. -/
theorem evidenceAdd_chain_any_relEnv
    (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmExtVertexLanguageDefGuardedWithCong v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) :=
  guarded_chain_evidence_add_fully_nested v pw₁ pw₂ pw₃ pq

/-! ## §5: Compiled Pipeline -/

/-- Combined pipeline: guarded forget + evidence-add.
    Under a d-separation oracle, `Extract(Forget(S, Revise(W₁,W₂)), q)` first
    reduces to `Extract(Revise(W₁,W₂), q)` (guarded forget, oracle-dependent),
    then to `Combine(Extract(W₁,q), Extract(W₂,q))` (evidence-add, oracle-free). -/
theorem compiled_dsep_forget_evidenceAdd
    (v : WMExtVertex) (hf : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked)
    (relEnv : RelationEnv) (pS pW₁ pW₂ pq : Pattern)
    (hprem : [("q", pq), ("W", pRevise pW₁ pW₂), ("S", pS)] ∈
      applyPremisesWithEnv relEnv (wmExtVertexLanguageDefGuarded v)
        ruleForgetOutsideGuarded.premises [("q", pq), ("W", pRevise pW₁ pW₂), ("S", pS)]) :
    langReducesUsing relEnv
      (wmExtVertexLanguageDefGuarded v)
      (pExtract (pForget pS (pRevise pW₁ pW₂)) pq)
      (pExtract (pRevise pW₁ pW₂) pq) :=
  guarded_forget_of_dsep v hf relEnv pS (pRevise pW₁ pW₂) pq hprem

end Mettapedia.OSLF.Framework.WMCalculusBNBridge
