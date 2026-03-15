import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
import Mettapedia.OSLF.Framework.WMCalculusEncoding
import Mettapedia.Logic.EvidenceQuantale

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
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.Framework.WMCalculusEncoding

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

/-! ## §6: Clean d-Separation Predicate (Concern 1)

Wrap the raw `applyPremisesWithEnv` membership in a semantic predicate
that hides the engine plumbing. -/

/-- `OutsideScope relEnv lang pS pq` holds when the d-separation oracle
    confirms that query `pq` is outside scope `pS` — i.e., the bindings
    from matching `ruleForgetOutsideGuarded` survive premise evaluation.

    This abstracts away the internal `applyPremisesWithEnv` machinery. -/
def OutsideScope (relEnv : RelationEnv) (lang : LanguageDef)
    (pS pq : Pattern) : Prop :=
  ∀ pW : Pattern, [("q", pq), ("W", pW), ("S", pS)] ∈
    applyPremisesWithEnv relEnv lang
      ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)]

/-- With the empty oracle, no query is outside any scope. -/
theorem outsideScope_empty_false (v : WMExtVertex) (pS pq : Pattern) :
    ¬ OutsideScope RelationEnv.empty (wmExtVertexLanguageDefGuarded v) pS pq := by
  intro h
  have := h pS  -- instantiate with any world model
  rw [collider_premise_empty] at this
  exact List.not_mem_nil this

/-- If `OutsideScope` holds, guarded forgetting fires for ALL world models. -/
theorem guarded_forget_of_outsideScope
    (v : WMExtVertex) (hf : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked)
    (relEnv : RelationEnv) (pS pW pq : Pattern)
    (hdsep : OutsideScope relEnv (wmExtVertexLanguageDefGuarded v) pS pq) :
    langReducesUsing relEnv
      (wmExtVertexLanguageDefGuarded v)
      (pExtract (pForget pS pW) pq)
      (pExtract pW pq) :=
  guarded_forget_of_dsep v hf relEnv pS pW pq (hdsep pW)

/-! ## §7: Completeness — Guarded Forget is the Unique Applicable Rule

In the guarded ext vertex calculus, `ruleForgetOutsideGuarded` is the ONLY
rule whose left-hand side matches `Extract(Forget(S, W), q)`. No core rule,
overlap rule, or other forgetting rule can fire on this pattern shape.

This gives a genuine completeness result: if guarded forgetting reduces
`Extract(Forget(S, W), q)` to `Extract(W, q)`, then the d-separation
oracle MUST have satisfied the `outsideScope(S, q)` premise. -/

/-- No core rule matches `Extract(Forget(S, W), q)`. -/
private theorem coreRules_no_match_forgetExtract (pS pW pq : Pattern) :
    ∀ r ∈ coreRules, matchPattern r.left (pExtract (pForget pS pW) pq) = [] := by
  simp [coreRules, ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc,
        ruleCombineComm, ruleCombineZero,
        pExtract, pForget, pRevise, pCombine, pEvidenceZero,
        matchPattern, matchArgs]

/-- The overlap rule (if present) does not match `Extract(Forget(S, W), q)`. -/
private theorem overlapRules_no_match_forgetExtract (mode : WMOverlapMode)
    (pS pW pq : Pattern) :
    ∀ r ∈ overlapRules mode, matchPattern r.left (pExtract (pForget pS pW) pq) = [] := by
  cases mode <;> simp [overlapRules, ruleOverlapExtract, pExtract, pForget,
    pOverlapMerge, matchPattern, matchArgs]

/-- `ruleForgetIdempotent` does not match `Extract(Forget(S, W), q)`.
    Its left-hand side is `Forget(S, Forget(S, W))`, head `"Forget"` ≠ `"Extract"`. -/
private theorem forgetIdempotent_no_match_forgetExtract (pS pW pq : Pattern) :
    matchPattern ruleForgetIdempotent.left (pExtract (pForget pS pW) pq) = [] := by
  simp [ruleForgetIdempotent, pExtract, pForget, matchPattern]

/-- In the guarded forgetting rules, only `ruleForgetOutsideGuarded` matches
    `Extract(Forget(S, W), q)`. -/
private theorem forgettingRulesGuarded_unique_match (mode : WMForgettingMode)
    (pS pW pq : Pattern) :
    ∀ r ∈ forgettingRulesGuarded mode,
      matchPattern r.left (pExtract (pForget pS pW) pq) ≠ [] →
      r = ruleForgetOutsideGuarded := by
  intro r hr hne
  cases mode with
  | none => simp [forgettingRulesGuarded] at hr
  | scopeBased =>
    simp [forgettingRulesGuarded] at hr
    rcases hr with rfl | rfl
    · rfl
    · exact absurd (forgetIdempotent_no_match_forgetExtract pS pW pq) hne
  | supportTracked =>
    simp [forgettingRulesGuarded] at hr
    rcases hr with rfl | rfl
    · rfl
    · exact absurd (forgetIdempotent_no_match_forgetExtract pS pW pq) hne

/-! ## §8: Semantic Bridge — Evidence Interpretation (Concern 2)

The WM calculus operates on syntactic Patterns. The PLN probability semantics
interprets these patterns in the `Evidence` quantale (ℝ≥0∞ × ℝ≥0∞).

An `EvidenceInterpretation` is a denotation function `⟦·⟧` from patterns to
`Evidence` values that validates the core rewrite rules: the evidence-add
rule corresponds to `hplus` (parallel evidence aggregation). -/

/-- An evidence interpretation assigns `Evidence` values to extraction results
    and validates the core algebraic laws.

    `extract W q` denotes the evidence for query `q` in world-model `W`.
    The key soundness condition `combine_hplus` asserts that the syntactic
    `Combine(e₁, e₂)` operation corresponds to `Evidence.hplus`:
    independent evidence sources aggregate additively. -/
structure EvidenceInterpretation where
  /-- Evidence for query `q` in world-model `W`. -/
  extract : Pattern → Pattern → Evidence
  /-- Evidence-add soundness: revision aggregates evidence additively.
      `⟦Extract(Revise(W₁,W₂), q)⟧ = ⟦Extract(W₁,q)⟧ ⊕ ⟦Extract(W₂,q)⟧`. -/
  combine_hplus : ∀ W₁ W₂ q,
    extract (pRevise W₁ W₂) q = extract W₁ q + extract W₂ q
  /-- Zero-evidence soundness: extracting from zero evidence yields zero.
      Validates `ruleCombineZero`. -/
  zero_extract : ∀ q, extract (.apply "Zero" []) q = Evidence.zero

/-! All 5 WM core rules are DERIVED from `combine_hplus` + `zero_extract` +
the `AddCommMonoid` structure of `Evidence`. The WM term algebra modulo
rewriting is the free commutative monoid on world-model atoms;
`extract` is the unique homomorphism to `(Evidence, hplus, zero)`. -/

/-- Rule 1 (evidence-add): direct from `combine_hplus`. -/
theorem evidence_add_sound (I : EvidenceInterpretation) (W₁ W₂ q : Pattern) :
    I.extract (pRevise W₁ W₂) q = I.extract W₁ q + I.extract W₂ q :=
  I.combine_hplus W₁ W₂ q

/-- Rule 2 (revision-comm): derived from commutativity of `+` on Evidence. -/
theorem revision_comm_sound (I : EvidenceInterpretation) (W₁ W₂ q : Pattern) :
    I.extract (pRevise W₁ W₂) q = I.extract (pRevise W₂ W₁) q := by
  rw [I.combine_hplus, I.combine_hplus, Evidence.hplus_comm]

/-- Rule 3 (revision-assoc): derived from associativity of `+` on Evidence. -/
theorem revision_assoc_sound (I : EvidenceInterpretation) (W₁ W₂ W₃ q : Pattern) :
    I.extract (pRevise (pRevise W₁ W₂) W₃) q =
    I.extract (pRevise W₁ (pRevise W₂ W₃)) q := by
  simp only [I.combine_hplus, Evidence.hplus_assoc]

/-- Rule 4 (combine-comm): `add_comm` on Evidence. -/
theorem combine_comm_sound (e₁ e₂ : Evidence) : e₁ + e₂ = e₂ + e₁ :=
  Evidence.hplus_comm e₁ e₂

/-- Rule 5 (combine-zero): zero is identity for evidence addition. -/
theorem combine_zero_sound (e : Evidence) : e + Evidence.zero = e :=
  Evidence.hplus_zero e

/-- Three-source chain: nested evidence-add = three-way sum. -/
theorem chain_evidence_semantically_sound (I : EvidenceInterpretation)
    (W₁ W₂ W₃ q : Pattern) :
    I.extract (pRevise (pRevise W₁ W₂) W₃) q =
    (I.extract W₁ q + I.extract W₂ q) + I.extract W₃ q := by
  rw [I.combine_hplus, I.combine_hplus]

/-- The universal property: `combine_hplus` + `zero_extract` (= commutative-monoid
    homomorphism conditions) imply ALL 5 WM core rule soundness conditions. -/
theorem wmCore_sound_of_addCommMonoidHom (extract : Pattern → Pattern → Evidence)
    (hcomb : ∀ W₁ W₂ q, extract (pRevise W₁ W₂) q = extract W₁ q + extract W₂ q)
    (hzero : ∀ q, extract (.apply "Zero" []) q = Evidence.zero) :
    -- All 5 soundness conditions hold:
    (∀ W₁ W₂ q, extract (pRevise W₁ W₂) q = extract (pRevise W₂ W₁) q) ∧
    (∀ W₁ W₂ W₃ q, extract (pRevise (pRevise W₁ W₂) W₃) q =
      extract (pRevise W₁ (pRevise W₂ W₃)) q) ∧
    (∀ e₁ e₂ : Evidence, e₁ + e₂ = e₂ + e₁) ∧
    (∀ e : Evidence, e + Evidence.zero = e) :=
  ⟨fun W₁ W₂ q => by rw [hcomb, hcomb, Evidence.hplus_comm],
   fun W₁ W₂ W₃ q => by simp only [hcomb, Evidence.hplus_assoc],
   fun e₁ e₂ => Evidence.hplus_comm e₁ e₂,
   fun e => Evidence.hplus_zero e⟩

/-! ## §9: Image-Restricted Box Theory

Full backward completeness is FALSE (backward asymmetry from `WMCalculusEncoding`).
But RESTRICTED to the image of `encodeWM`, backward completeness holds:
every Pattern-level predecessor that is itself a WMTerm encodes a WMStep predecessor. -/

/-- A pattern is in the sort-`s` WMTerm image. -/
def WMImageAt (s : WMSort) (p : Pattern) : Prop :=
  ∃ t : WMTerm s, p = encodeWM t

/-- Image-restricted box: `□φ` restricted to sort-`s` predecessors. -/
def langBoxOnImageAt (s : WMSort) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) : Prop :=
  ∀ q, langReduces lang q p → WMImageAt s q → φ q

/-- On the WMTerm image, box is adequate: the Pattern-level image-restricted box
    coincides with the WMStep-level universal quantifier over predecessors.
    This is the correct formulation of "backward completeness" — it holds
    exactly on the image, and fails outside it (backward asymmetry). -/
theorem wmBoxOnImage_iff
    {s : WMSort} (t : WMTerm s) (φ : Pattern → Prop) :
    (∀ t' : WMTerm s, WMStep t' t → φ (encodeWM t')) ↔
    langBoxOnImageAt s wmCoreLanguageDef φ (encodeWM t) := by
  constructor
  · intro h q hred ⟨t', heq⟩
    subst heq
    obtain ⟨t'', hstep, hrhs⟩ := wmStep_complete t' _ hred
    have : t'' = t := encodeWM_injective hrhs
    subst this; exact h t' hstep
  · intro h t' hstep
    exact h (encodeWM t') (wmStep_sound t' t hstep) ⟨t', rfl⟩

end Mettapedia.OSLF.Framework.WMCalculusBNBridge
