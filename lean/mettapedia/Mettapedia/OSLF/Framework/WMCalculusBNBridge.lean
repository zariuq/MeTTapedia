import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
import Mettapedia.OSLF.Framework.WMCalculusEncoding
import Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# WM Calculus — Guarded Inference and Evidence Interpretation

The guarded rule `ruleForgetOutsideGuarded` has premise
`[.relationQuery "outsideScope" [.fvar "S", .fvar "q"]]`.
A `RelationEnv` supplies relation-query answers. These results describe what
happens when an `outsideScope(S, q)` answer survives premise evaluation; they do
not construct a Bayesian network or prove that a provider decides d-separation.
Such an interpretation requires a separate provider-soundness theorem.

Architecture:
- **Positive** (`guarded_forget_of_dsep`): Parametric in the oracle.
  Given ANY `RelationEnv` that satisfies the outsideScope premise,
  the guarded forgetting rule fires. The hypothesis is operational query
  success, not a checked d-separation certificate.
- **Negative** (`collider_premise_empty`): With `RelationEnv.empty`,
  the premise evaluation returns `[]`, blocking the rule entirely.
  This is an empty-provider control, not a collider-network instance. In a
  collider `A → C ← B`, the path is blocked without conditioning on `C` or a
  descendant and becomes open when such conditioning occurs.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusBNBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.PLN.Evidence.EvidenceQuantale
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

This is parametric in the provider. No network-topology interpretation or
provider-soundness result is assumed implicitly. -/

set_option backward.isDefEq.respectTransparency false in
/-- Under any RelationEnv that satisfies the outsideScope premise,
    the guarded forgetting rule fires:
    `Extract(Forget(S, W), q) ↦ Extract(W, q)`.

    The hypothesis `hprem` is membership in the premise evaluator's returned
    bindings. It does not establish a Bayesian interpretation of the answer. -/
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
  exact step_of_rule
    (relEnv := relEnv)
    (lang := wmExtVertexLanguageDefGuarded v)
    (rule := ruleForgetOutsideGuarded)
    (initialBindings := [("q", pq), ("W", pW), ("S", pS)])
    (finalBindings := [("q", pq), ("W", pW), ("S", pS)])
    (ruleForgetOutsideGuarded_mem_guarded v hf)
    (by simp [ruleForgetOutsideGuarded, pExtract, pForget,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule,
      matchPattern, matchArgs, mergeBindings])
    (.relationQuery .nil)
    hprem
    (by
      rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings
        _ _ _ (by decide +kernel)]
      simp [ruleForgetOutsideGuarded, pExtract, applyBindings])

/-- Transports an assumed successful provider to an existential reduction.
    This theorem does not itself construct a provider or a network witness. -/
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

/-! ## §3: Negative Theorem — Empty Provider Blocks the Premise

With `RelationEnv.empty`, the `outsideScope` premise can never be satisfied.
The legacy theorem names below do not supply a collider interpretation. -/

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

/-! ## §4: BinaryEvidence-Add Core Rules (Oracle-Independent)

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
  exact hred.mono_relEnv (RelationEnv.empty_le relEnv)

/-- The existing empty-provider evidence-add chain, using only core rules.
    Its steps can be lifted with `guarded_reduction_lifts_relEnv`; the relation
    in this statement itself has no provider parameter.
    `Extract(Revise(Revise(W₁,W₂), W₃), q)` →*
    `Combine(Combine(Extract(W₁,q), Extract(W₂,q)), Extract(W₃,q))`. -/
theorem evidenceAdd_chain_any_relEnv
    (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmExtVertexLanguageDefGuardedWithCong v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) :=
  guarded_chain_evidence_add_fully_nested v pw₁ pw₂ pw₃ pq

/-! ## §5: Compiled Pipeline -/

/-- The guarded-forgetting stage on a revised world model.
    This statement proves one step to `Extract(Revise(W₁,W₂), q)`, not the
    subsequent evidence-add step of a combined pipeline. -/
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

/-! ## §6: Operational Outside-Scope Predicate

Wrap the raw `applyPremisesWithEnv` membership without changing its meaning. -/

/-- `OutsideScope relEnv lang pS pq` holds when the bindings from matching
    `ruleForgetOutsideGuarded` survive premise evaluation for every `pW`.

    It abbreviates operational query success, not Bayesian d-separation. -/
def OutsideScope (relEnv : RelationEnv) (lang : LanguageDef)
    (pS pq : Pattern) : Prop :=
  ∀ pW : Pattern, [("q", pq), ("W", pW), ("S", pS)] ∈
    applyPremisesWithEnv relEnv lang
      ruleForgetOutsideGuarded.premises [("q", pq), ("W", pW), ("S", pS)]

/-- The operational `OutsideScope` predicate fails for the empty provider. -/
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

/-! ## §7: Raw Matcher Exclusions

The following lemmas exclude other rules using `matchPattern` on the literal
shape `Extract(Forget(S, W), q)`. They are not a converse theorem for the
rule-aware operational relation, matching modulo equations, or Bayesian
d-separation. -/

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

/-! ## §8: Additive Extraction Interpretation

An `EvidenceInterpretation` assigns extraction values in `BinaryEvidence`
(ℝ≥0∞ × ℝ≥0∞) and assumes additivity under revision and zero extraction.
The remaining algebraic equalities below follow from these laws. This record
does not define a denotation for every Pattern or construct an interpretation. -/

/-- An evidence interpretation assigns `BinaryEvidence` values to extraction results
    and validates the core algebraic laws.

    `extract W q` denotes the evidence for query `q` in world-model `W`.
    The law `combine_hplus` asserts that extraction under syntactic revision
    aggregates additively in this interpretation. No probabilistic
    independence theorem is part of the record. -/
structure EvidenceInterpretation where
  /-- BinaryEvidence for query `q` in world-model `W`. -/
  extract : Pattern → Pattern → BinaryEvidence
  /-- BinaryEvidence-add soundness: revision aggregates evidence additively.
      `⟦Extract(Revise(W₁,W₂), q)⟧ = ⟦Extract(W₁,q)⟧ ⊕ ⟦Extract(W₂,q)⟧`. -/
  combine_hplus : ∀ W₁ W₂ q,
    extract (pRevise W₁ W₂) q = extract W₁ q + extract W₂ q
  /-- Extracting from the literal zero world model yields zero evidence.
      This is separate from the additive identity used by `ruleCombineZero`. -/
  zero_extract : ∀ q, extract (.apply "Zero" []) q = BinaryEvidence.zero

/-! Revision commutativity and associativity follow from `combine_hplus`;
combine commutativity and zero are laws of `BinaryEvidence` itself. No free
term-algebra construction or uniqueness theorem is established here. -/

/-- Rule 1 (evidence-add): direct from `combine_hplus`. -/
theorem evidence_add_sound (I : EvidenceInterpretation) (W₁ W₂ q : Pattern) :
    I.extract (pRevise W₁ W₂) q = I.extract W₁ q + I.extract W₂ q :=
  I.combine_hplus W₁ W₂ q

/-- Rule 2 (revision-comm): derived from commutativity of `+` on BinaryEvidence. -/
theorem revision_comm_sound (I : EvidenceInterpretation) (W₁ W₂ q : Pattern) :
    I.extract (pRevise W₁ W₂) q = I.extract (pRevise W₂ W₁) q := by
  rw [I.combine_hplus, I.combine_hplus, BinaryEvidence.hplus_comm]

/-- Rule 3 (revision-assoc): derived from associativity of `+` on BinaryEvidence. -/
theorem revision_assoc_sound (I : EvidenceInterpretation) (W₁ W₂ W₃ q : Pattern) :
    I.extract (pRevise (pRevise W₁ W₂) W₃) q =
    I.extract (pRevise W₁ (pRevise W₂ W₃)) q := by
  simp only [I.combine_hplus, BinaryEvidence.hplus_assoc]

/-- Rule 4 (combine-comm): `add_comm` on BinaryEvidence. -/
theorem combine_comm_sound (e₁ e₂ : BinaryEvidence) : e₁ + e₂ = e₂ + e₁ :=
  BinaryEvidence.hplus_comm e₁ e₂

/-- Rule 5 (combine-zero): zero is identity for evidence addition. -/
theorem combine_zero_sound (e : BinaryEvidence) : e + BinaryEvidence.zero = e :=
  BinaryEvidence.hplus_zero e

/-- Three-source chain: nested evidence-add = three-way sum. -/
theorem chain_evidence_semantically_sound (I : EvidenceInterpretation)
    (W₁ W₂ W₃ q : Pattern) :
    I.extract (pRevise (pRevise W₁ W₂) W₃) q =
    (I.extract W₁ q + I.extract W₂ q) + I.extract W₃ q := by
  rw [I.combine_hplus, I.combine_hplus]

/-- Additivity of extraction under revision implies the four algebraic laws
    needed in addition to the evidence-add rule itself.  Zero extraction is a
    separate semantic law of `EvidenceInterpretation`; none of these five
    rewrite rules has `Extract(Zero, q)` as its left-hand side. -/
theorem wmCore_algebraic_laws_of_revision_additive
    (extract : Pattern → Pattern → BinaryEvidence)
    (hcomb : ∀ W₁ W₂ q,
      extract (pRevise W₁ W₂) q = extract W₁ q + extract W₂ q) :
    (∀ W₁ W₂ q, extract (pRevise W₁ W₂) q = extract (pRevise W₂ W₁) q) ∧
    (∀ W₁ W₂ W₃ q, extract (pRevise (pRevise W₁ W₂) W₃) q =
      extract (pRevise W₁ (pRevise W₂ W₃)) q) ∧
    (∀ e₁ e₂ : BinaryEvidence, e₁ + e₂ = e₂ + e₁) ∧
    (∀ e : BinaryEvidence, e + BinaryEvidence.zero = e) :=
  ⟨fun W₁ W₂ q => by rw [hcomb, hcomb, BinaryEvidence.hplus_comm],
   fun W₁ W₂ W₃ q => by simp only [hcomb, BinaryEvidence.hplus_assoc],
   fun e₁ e₂ => BinaryEvidence.hplus_comm e₁ e₂,
   fun e => BinaryEvidence.hplus_zero e⟩

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
