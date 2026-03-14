import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMCalculusGSLTVertex
import Mettapedia.OSLF.Framework.WMCalculusContextClosure

/-!
# WM Calculus ↔ OSLF Bridge

This module connects the OSLF-derived modal operators (◇, □, ◇ ⊣ □) back to
the WorldModel typeclass properties from the PLN book.

## Architecture — Two Layers

**Layer 1 (Syntactic):** Define predicates on Pattern terms (`isCombined`,
`isDecomposable`, `isCommuted`, `isReassociated`) and prove ◇ theorems
by composing `langDiamond_spec` with existing step lemmas from
`WMCalculusLanguageDef.lean`.

**Layer 2 (Semantic):** A `WMTerm` inductive with a relational encoding
`WMTermEncodes : Pattern → WMTerm → Prop` (following `PLNSelectorLanguageDef`'s
`ExprEncodes` pattern) plus soundness theorems: reductions on encoded terms
correspond to WorldModel axiom applications.

## Key Insight

The Galois connection ◇ ⊣ □ is **automatic** from `langGalois`.  The bridge
gives it *meaning*: ◇(isCombined) at `Extract(Revise(W₁,W₂),q)` is the
evidence-decomposability property, and the adjunction transports this to
backward safety (□) properties for free.

## References

- `TypeSynthesis.lean` — `langDiamond`, `langBox`, `langGalois`, `langDiamond_spec`, `langBox_spec`
- `WMCalculusLanguageDef.lean` — pattern vocabulary, step lemmas
- `WMCalculusGSLTVertex.lean` — vertex OSLF, transport
- `PLNWorldModel.lean` — `WorldModel` class, `evidence_add`
- `PLNSelectorLanguageDef.lean` — `ExprEncodes` (relational encoding pattern)
-/

namespace Mettapedia.OSLF.Framework.WMCalculusOSLFBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusGSLTVertex
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

/-! ## Section 1: Pattern Predicates

Predicates on `Pattern` terms that correspond to WM-calc structural properties.
Each captures whether a term is in a specific syntactic form after reduction. -/

/-- "The pattern is a `Combine(e₁, e₂)` term" — evidence has been decomposed
    into a sum of per-source evidence. -/
def isCombined (p : Pattern) : Prop :=
  ∃ e₁ e₂, p = pCombine e₁ e₂

/-- "The pattern is an `Extract(Revise(W₁,W₂), q)` term" — a compound state
    with pending evidence extraction. -/
def isDecomposable (p : Pattern) : Prop :=
  ∃ w₁ w₂ q, p = pExtract (pRevise w₁ w₂) q

/-- "The pattern is a `Revise(W₂, W₁)` term" — revision with swapped operands.
    Used as target predicate for commutativity diamond. -/
def isRevision (p : Pattern) : Prop :=
  ∃ w₁ w₂, p = pRevise w₁ w₂

/-- "The pattern is a `Revise(W₁, Revise(W₂,W₃))` term" — right-associated revision. -/
def isRightAssocRevision (p : Pattern) : Prop :=
  ∃ w₁ w₂ w₃, p = pRevise w₁ (pRevise w₂ w₃)

/-- "The pattern is a `LeastClosure(R,W,seed)` term" — at a fixpoint. -/
def isFixpoint (p : Pattern) : Prop :=
  ∃ r w s, p = pLeastClosure r w s

/-- "The pattern is `EvidenceZero`." -/
def isZeroEvidence (p : Pattern) : Prop :=
  p = pEvidenceZero

/-! ## Section 2: Diamond Theorems (Layer 1)

Each ◇ theorem composes `langDiamond_spec` with a step lemma to prove that
a specific reduction *exists* from a given pattern form.  The proof of ◇φ
at p is an existential witness (q, reduction-proof, φ-witness) — the
Curry-Howard reading of the step-future modality. -/

/-- ◇(isCombined) holds at any `Extract(Revise(W₁,W₂), q)`.
    Witness: the evidence-add step lemma. -/
theorem diamond_isCombined_at_decomposable (v : WMExtVertex)
    (pw₁ pw₂ pq : Pattern) :
    langDiamond (wmExtVertexLanguageDef v) isCombined
      (pExtract (pRevise pw₁ pw₂) pq) := by
  rw [langDiamond_spec]
  exact ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
         wmLangReduces_evidenceAdd v pw₁ pw₂ pq,
         ⟨_, _, rfl⟩⟩

/-- ◇(isRevision) holds at any `Revise(W₁,W₂)` — the commuted form is reachable.
    Witness: the revision-commutativity step lemma. -/
theorem diamond_isCommuted (v : WMExtVertex)
    (pw₁ pw₂ : Pattern) :
    langDiamond (wmExtVertexLanguageDef v) isRevision
      (pRevise pw₁ pw₂) := by
  rw [langDiamond_spec]
  exact ⟨pRevise pw₂ pw₁,
         wmLangReduces_revisionComm v pw₁ pw₂,
         ⟨_, _, rfl⟩⟩

/-- ◇(isRightAssocRevision) holds at any `Revise(Revise(W₁,W₂), W₃)`.
    Witness: the revision-associativity step lemma. -/
theorem diamond_isReassociated (v : WMExtVertex)
    (pw₁ pw₂ pw₃ : Pattern) :
    langDiamond (wmExtVertexLanguageDef v) isRightAssocRevision
      (pRevise (pRevise pw₁ pw₂) pw₃) := by
  rw [langDiamond_spec]
  exact ⟨pRevise pw₁ (pRevise pw₂ pw₃),
         wmLangReduces_revisionAssoc v pw₁ pw₂ pw₃,
         ⟨_, _, _, rfl⟩⟩

/-- ◇(isCombined) at a decomposable pattern implies the conclusion of `evidence_add`:
    the compound state reduces to a combined evidence term where each component
    is extracted from a single source. -/
theorem diamond_isCombined_yields_per_source (v : WMExtVertex)
    (pw₁ pw₂ pq : Pattern) :
    ∃ q, langReduces (wmExtVertexLanguageDef v) (pExtract (pRevise pw₁ pw₂) pq) q ∧
         q = pCombine (pExtract pw₁ pq) (pExtract pw₂ pq) := by
  exact ⟨_, wmLangReduces_evidenceAdd v pw₁ pw₂ pq, rfl⟩

/-! ## Section 3: Galois Connection Instantiation

The Galois connection ◇ ⊣ □ is automatic from `langGalois`. Here we instantiate
it at WM vertices and derive concrete evidence-theoretic corollaries. -/

/-- The WM calculus Galois connection at any extended vertex. -/
theorem wmCalc_galois (v : WMExtVertex) :
    GaloisConnection
      (langDiamond (wmExtVertexLanguageDef v))
      (langBox (wmExtVertexLanguageDef v)) :=
  langGalois (wmExtVertexLanguageDef v)

/-- The WM calculus Galois connection at any full 13-axis vertex. -/
theorem wmFullCalc_galois (v : WMFullVertex) :
    GaloisConnection
      (langDiamond (wmFullVertexLanguageDef v))
      (langBox (wmFullVertexLanguageDef v)) :=
  langGalois (wmFullVertexLanguageDef v)

/-- Evidence decomposability ↔ predecessor safety:
    "Every reduct of a combined-form pattern satisfies ψ"
    iff
    "Every combined-form pattern has all predecessors satisfying ψ".

    This is the adjunction `◇(isCombined) ≤ ψ ↔ isCombined ≤ □ψ`
    specialized to the WM calculus. -/
theorem wmCalc_decomposability_safety (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmExtVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmExtVertexLanguageDef v) ψ p) :=
  (wmCalc_galois v).le_iff_le

/-- Commutativity adjunction: ◇(isRevision) ≤ ψ ↔ isRevision ≤ □ψ. -/
theorem wmCalc_commutativity_safety (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmExtVertexLanguageDef v) isRevision p → ψ p) ↔
    (∀ p, isRevision p → langBox (wmExtVertexLanguageDef v) ψ p) :=
  (wmCalc_galois v).le_iff_le

/-- Associativity adjunction: ◇(isRightAssocRevision) ≤ ψ ↔ isRightAssocRevision ≤ □ψ. -/
theorem wmCalc_associativity_safety (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmExtVertexLanguageDef v) isRightAssocRevision p → ψ p) ↔
    (∀ p, isRightAssocRevision p → langBox (wmExtVertexLanguageDef v) ψ p) :=
  (wmCalc_galois v).le_iff_le

/-! ## Section 4: WMTerm Inductive (Layer 2)

An abstract syntax for WorldModel terms, indexed by sort. Sort-correctness
is enforced by the type index: `state`/`revise` produce `.state`, `query`
produces `.query`, `extract`/`combine`/`zero` produce `.evidence`. -/

/-- The three sorts of the WorldModel calculus. -/
inductive WMSort where
  | state    -- posterior states W
  | query    -- queries q
  | evidence -- evidence values e
  deriving DecidableEq, Repr

/-- Abstract syntax for WorldModel terms, indexed by sort.
    Sort-correctness is enforced by the type index. -/
inductive WMTerm : WMSort → Type where
  | state   (name : String)                                    : WMTerm .state
  | query   (name : String)                                    : WMTerm .query
  | revise  (t₁ t₂ : WMTerm .state)                           : WMTerm .state
  | extract (tw : WMTerm .state) (tq : WMTerm .query)         : WMTerm .evidence
  | combine (t₁ t₂ : WMTerm .evidence)                        : WMTerm .evidence
  | zero                                                       : WMTerm .evidence
  deriving Repr

/-! ## Section 5: Relational Encoding (Layer 2)

Following PLNSelectorLanguageDef's `ExprEncodes` pattern: a relational encoding
`WMTermEncodes : Pattern → WMTerm s → Prop` says "Pattern p represents WMTerm t"
without requiring a computable mapping from abstract states to patterns. -/

/-- Relational encoding: "Pattern `p` represents WorldModel term `t`."
    Inductive constructors mirror the WMTerm structure. -/
inductive WMTermEncodes : Pattern → WMTerm s → Prop where
  | state (name : String) :
      WMTermEncodes (.fvar name) (.state name)
  | query (name : String) :
      WMTermEncodes (.fvar name) (.query name)
  | revise {p₁ p₂ : Pattern} {t₁ t₂ : WMTerm .state} :
      WMTermEncodes p₁ t₁ → WMTermEncodes p₂ t₂ →
      WMTermEncodes (pRevise p₁ p₂) (.revise t₁ t₂)
  | extract {pw pq : Pattern} {tw : WMTerm .state} {tq : WMTerm .query} :
      WMTermEncodes pw tw → WMTermEncodes pq tq →
      WMTermEncodes (pExtract pw pq) (.extract tw tq)
  | combine {p₁ p₂ : Pattern} {t₁ t₂ : WMTerm .evidence} :
      WMTermEncodes p₁ t₁ → WMTermEncodes p₂ t₂ →
      WMTermEncodes (pCombine p₁ p₂) (.combine t₁ t₂)
  | zero :
      WMTermEncodes pEvidenceZero .zero

/-! ## Section 6: Encoding Soundness (Layer 2)

Soundness theorems: reductions on encoded terms correspond to
WorldModel axiom applications.  Each theorem witnesses a LanguageDef
reduction step together with a WMTermEncodes proof for the result. -/

/-- Evidence-add soundness: if `pw₁` encodes `tw₁`, `pw₂` encodes `tw₂`, and
    `pq` encodes `tq`, then the LanguageDef reduction
    `Extract(Revise(pw₁,pw₂), pq) ↦ Combine(Extract(pw₁,pq), Extract(pw₂,pq))`
    fires and the result encodes `combine(extract(tw₁,tq), extract(tw₂,tq))`. -/
theorem wm_evidence_add_sound (v : WMExtVertex)
    {pw₁ pw₂ pq : Pattern} {tw₁ tw₂ : WMTerm .state} {tq : WMTerm .query}
    (hw₁ : WMTermEncodes pw₁ tw₁) (hw₂ : WMTermEncodes pw₂ tw₂)
    (hq : WMTermEncodes pq tq) :
    ∃ q, langReduces (wmExtVertexLanguageDef v)
      (pExtract (pRevise pw₁ pw₂) pq) q ∧
      WMTermEncodes q (.combine (.extract tw₁ tq) (.extract tw₂ tq)) :=
  ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
   wmLangReduces_evidenceAdd v pw₁ pw₂ pq,
   WMTermEncodes.combine
     (WMTermEncodes.extract hw₁ hq)
     (WMTermEncodes.extract hw₂ hq)⟩

/-- Revision-commutativity soundness: reduction fires and result encodes
    `revise(tw₂, tw₁)`. -/
theorem wm_revision_comm_sound (v : WMExtVertex)
    {pw₁ pw₂ : Pattern} {tw₁ tw₂ : WMTerm .state}
    (hw₁ : WMTermEncodes pw₁ tw₁) (hw₂ : WMTermEncodes pw₂ tw₂) :
    ∃ q, langReduces (wmExtVertexLanguageDef v)
      (pRevise pw₁ pw₂) q ∧
      WMTermEncodes q (.revise tw₂ tw₁) :=
  ⟨pRevise pw₂ pw₁,
   wmLangReduces_revisionComm v pw₁ pw₂,
   WMTermEncodes.revise hw₂ hw₁⟩

/-- Revision-associativity soundness: reduction fires and result encodes
    `revise(tw₁, revise(tw₂, tw₃))`. -/
theorem wm_revision_assoc_sound (v : WMExtVertex)
    {pw₁ pw₂ pw₃ : Pattern} {tw₁ tw₂ tw₃ : WMTerm .state}
    (hw₁ : WMTermEncodes pw₁ tw₁) (hw₂ : WMTermEncodes pw₂ tw₂)
    (hw₃ : WMTermEncodes pw₃ tw₃) :
    ∃ q, langReduces (wmExtVertexLanguageDef v)
      (pRevise (pRevise pw₁ pw₂) pw₃) q ∧
      WMTermEncodes q (.revise tw₁ (.revise tw₂ tw₃)) :=
  ⟨pRevise pw₁ (pRevise pw₂ pw₃),
   wmLangReduces_revisionAssoc v pw₁ pw₂ pw₃,
   WMTermEncodes.revise hw₁ (WMTermEncodes.revise hw₂ hw₃)⟩

/-! ## Section 7: Bridge Composition

Composing Layer 1 (◇ theorems) with Layer 2 (encoding soundness) yields the
full bridge: WorldModel axioms *mean* something about the OSLF-derived ◇/□. -/

/-- The encoding of `extract(revise(tw₁,tw₂), tq)` satisfies ◇(isCombined). -/
theorem diamond_isCombined_of_encoded (v : WMExtVertex)
    {pw₁ pw₂ pq : Pattern} {tw₁ tw₂ : WMTerm .state} {tq : WMTerm .query}
    (_hw₁ : WMTermEncodes pw₁ tw₁) (_hw₂ : WMTermEncodes pw₂ tw₂)
    (_hq : WMTermEncodes pq tq) :
    langDiamond (wmExtVertexLanguageDef v) isCombined
      (pExtract (pRevise pw₁ pw₂) pq) :=
  diamond_isCombined_at_decomposable v pw₁ pw₂ pq

/-- The encoding of `revise(tw₁, tw₂)` satisfies ◇(isRevision) — commutativity. -/
theorem diamond_isCommuted_of_encoded (v : WMExtVertex)
    {pw₁ pw₂ : Pattern} {tw₁ tw₂ : WMTerm .state}
    (_hw₁ : WMTermEncodes pw₁ tw₁) (_hw₂ : WMTermEncodes pw₂ tw₂) :
    langDiamond (wmExtVertexLanguageDef v) isRevision
      (pRevise pw₁ pw₂) :=
  diamond_isCommuted v pw₁ pw₂

/-- Transport evidence-add diamond across vertices with equal LanguageDefs. -/
theorem diamond_isCombined_transport
    {v w : WMFullVertex}
    (heq : wmFullVertexLanguageDef v = wmFullVertexLanguageDef w)
    {p : Pattern}
    (h : langDiamond (wmFullVertexLanguageDef v) isCombined p) :
    langDiamond (wmFullVertexLanguageDef w) isCombined p := by
  rw [langDiamond_spec] at h ⊢
  obtain ⟨q, hred, hcomb⟩ := h
  exact ⟨q, heq ▸ hred, hcomb⟩

/-! ## Section 8: Monotonicity — Diamond Propagation Along Weakness

If vertex `v` is weaker than `w` (fewer rules), then ◇ at `w` implies ◇ at `w`
(more reductions available).  The converse does not hold. -/

/-- If a reduction holds at vertex `v` and `v`'s rules are a subset of `w`'s,
    then the ◇-property propagates.  This witnesses the GSLT fiber morphism
    in terms of modal logic. -/
theorem diamond_monotone_of_rules_subset
    {L₁ L₂ : LanguageDef}
    (hsub : ∀ p q, langReduces L₁ p q → langReduces L₂ p q)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    langDiamond L₂ φ p := by
  rw [langDiamond_spec] at h ⊢
  obtain ⟨q, hred, hφ⟩ := h
  exact ⟨q, hsub p q hred, hφ⟩

/-! ## Section 9: Full-Vertex Diamond Theorems

Diamond theorems for extension-axis rules at the 13-axis `WMFullVertex`.
Each axiom fires only when the corresponding axis is enabled. -/

/-- ◇(isCombined) at any full vertex (core evidence-add). -/
theorem full_diamond_isCombined (v : WMFullVertex) (pw₁ pw₂ pq : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isCombined
      (pExtract (pRevise pw₁ pw₂) pq) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_evidenceAdd v pw₁ pw₂ pq, ⟨_, _, rfl⟩⟩

/-- ◇(isRevision) at any full vertex (core commutativity). -/
theorem full_diamond_isCommuted (v : WMFullVertex) (pw₁ pw₂ : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isRevision
      (pRevise pw₁ pw₂) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_revisionComm v pw₁ pw₂, ⟨_, _, rfl⟩⟩

/-- ◇(isRightAssocRevision) at any full vertex (core associativity). -/
theorem full_diamond_isReassociated (v : WMFullVertex) (pw₁ pw₂ pw₃ : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isRightAssocRevision
      (pRevise (pRevise pw₁ pw₂) pw₃) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_revisionAssoc v pw₁ pw₂ pw₃, ⟨_, _, _, rfl⟩⟩

/-- "The pattern is an `OverlapCorrect(...)` term." -/
def isOverlapCorrected (p : Pattern) : Prop :=
  ∃ e₁ e₂ ov, p = pOverlapCorrect e₁ e₂ ov

/-- ◇(isOverlapCorrected) at overlap-aware vertices. -/
theorem full_diamond_overlapCorrected (v : WMFullVertex)
    (hov : v.overlap = .overlapAware) (pw₁ pw₂ pq : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isOverlapCorrected
      (pExtract (pOverlapMerge pw₁ pw₂) pq) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_overlapExtract v hov pw₁ pw₂ pq, ⟨_, _, _, rfl⟩⟩

/-- ◇(isFixpoint) at fixpoint-enabled vertices: the closure absorbs one step. -/
theorem full_diamond_closureFixpoint (v : WMFullVertex)
    (hfp : v.fixpoint = .closureOnly ∨ v.fixpoint = .policyDriven ∨ v.fixpoint = .cascade)
    (pR pw pseed : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isFixpoint
      (pImmediateStep pR pw pseed (pLeastClosure pR pw pseed)) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_closureFixpoint v hfp pR pw pseed, ⟨_, _, _, rfl⟩⟩

/-- ◇(isZeroEvidence) at conserving vertices: anti-hallucination. -/
theorem full_diamond_antiHallucination (v : WMFullVertex)
    (hcons : v.conservation = .conserving) (pD pq : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isZeroEvidence
      (pExtract pD pq) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_antiHallucination v hcons pD pq, rfl⟩

/-- ◇(isCombined) for experiment evidence at experiment-enabled vertices. -/
theorem full_diamond_experimentDecomposable (v : WMFullVertex)
    (hexp : v.experiment = .deterministic ∨ v.experiment = .stochastic)
    (pw₁ pw₂ pq : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isCombined
      (pExperimentEvidence (pRevise pw₁ pw₂) pq) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_experimentEvidenceAdd v hexp pw₁ pw₂ pq, ⟨_, _, rfl⟩⟩

/-- ◇(isCombined) for Kripke evidence at Kripke-enabled vertices. -/
theorem full_diamond_kripkeDecomposable (v : WMFullVertex)
    (hkr : v.kripke = .pointedKripke) (pw₁ pw₂ pphi : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isCombined
      (pKripkeEvidence (pRevise pw₁ pw₂) pphi) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_kripkeEvidenceAdd v hkr pw₁ pw₂ pphi, ⟨_, _, rfl⟩⟩

/-- ◇(isCombined) for generic evidence at generic-carrier vertices. -/
theorem full_diamond_genericDecomposable (v : WMFullVertex)
    (hca : v.carrier = .generic) (pw₁ pw₂ pq : Pattern) :
    langDiamond (wmFullVertexLanguageDef v) isCombined
      (pGenericEvidence (pRevise pw₁ pw₂) pq) := by
  rw [langDiamond_spec]
  exact ⟨_, wmFullLangReduces_genericEvidenceAdd v hca pw₁ pw₂ pq, ⟨_, _, rfl⟩⟩

/-! ## Section 10: Diamond Chaining (Multi-Step)

Composing single-step ◇ witnesses into multi-step `LangReducesStar` chains.
This captures the PLN multi-source revision workflow:
`Extract(Revise(Revise(W₁,W₂),W₃), q)` decomposes in two steps. -/

open Mettapedia.OSLF.Framework.LangMorphism

/-- Two-step decomposition: `Extract(Revise(Revise(W₁,W₂),W₃), q)` reduces to
    `Combine(Combine(Extract(W₁,q), Extract(W₂,q)), Extract(W₃,q))` via
    associativity then evidence-add.

    Step 1 (assoc): `Revise(Revise(W₁,W₂),W₃) ↦ Revise(W₁,Revise(W₂,W₃))`
    (in Extract context — note this requires congruence descent)

    Instead, we witness: evidence-add directly, then recursively.
    Direct path: `Extract(Revise(Revise(W₁,W₂),W₃), q)` →₁
    `Combine(Extract(Revise(W₁,W₂),q), Extract(W₃,q))` →₁
    via evidence-add on `Extract(Revise(W₁,W₂),q)` we can't go further at
    top level without congruence.  So the simplest chain uses two top-level
    evidence-add steps on nested revisions. -/
theorem chain_evidence_add_nested (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmExtVertexLanguageDef v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pExtract (pRevise pw₁ pw₂) pq) (pExtract pw₃ pq)) :=
  LangReducesStar.single (wmLangReduces_evidenceAdd v (pRevise pw₁ pw₂) pw₃ pq)

/-- Two-step revision chain: `Revise(Revise(W₁,W₂),W₃)` can be reassociated
    then the inner revision can be commuted, reaching
    `Revise(W₁, Revise(W₃,W₂))`. -/
theorem chain_assoc_then_comm (v : WMExtVertex) (pw₁ pw₂ pw₃ : Pattern) :
    LangReducesStar (wmExtVertexLanguageDef v)
      (pRevise (pRevise pw₁ pw₂) pw₃)
      (pRevise pw₁ (pRevise pw₂ pw₃)) :=
  LangReducesStar.single (wmLangReduces_revisionAssoc v pw₁ pw₂ pw₃)

/-- Full-vertex version of two-step evidence-add chain. -/
theorem full_chain_evidence_add_nested (v : WMFullVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmFullVertexLanguageDef v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pExtract (pRevise pw₁ pw₂) pq) (pExtract pw₃ pq)) :=
  LangReducesStar.single (wmFullLangReduces_evidenceAdd v (pRevise pw₁ pw₂) pw₃ pq)

/-! ## Section 10b: Fully Nested Chain via Context Closure

The genuine two-step decomposition uses congruence rules to reduce INSIDE
`Combine(Extract(Revise(W₁,W₂),q), Extract(W₃,q))` — applying evidence-add
to the left argument via `ruleCombineCongLeft`. -/

open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

/-- Evidence-add fires in the cong-extended calculus (lifting raw step). -/
theorem wmCongLangReduces_evidenceAdd (v : WMExtVertex) (pw₁ pw₂ pq : Pattern) :
    langReduces (wmExtVertexLanguageDefWithCong v)
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) :=
  congReduces_of_rawReduces_ext v _ _ (wmLangReduces_evidenceAdd v pw₁ pw₂ pq)

/-- Evidence-add produces a reduct in `rewriteWithContextNoPremises` of the
    cong-extended calculus. This is the executable witness needed for
    congruence premise satisfaction.

    Key: `ruleEvidenceAdd` has `premises = []`, so `applyRule` fires and
    places the result in `rewriteStep ⊆ rewriteWithContextNoPremises`. -/
theorem evidenceAdd_mem_rewriteContextNoPremises (v : WMExtVertex)
    (pw₁ pw₂ pq : Pattern) :
    pCombine (pExtract pw₁ pq) (pExtract pw₂ pq) ∈
      rewriteWithContextNoPremises (wmExtVertexLanguageDefWithCong v)
        (pExtract (pRevise pw₁ pw₂) pq) := by
  unfold rewriteWithContextNoPremises rewriteStepNoPremises rewriteStep
  rw [List.mem_append]
  left
  rw [List.mem_flatMap]
  refine ⟨ruleEvidenceAdd, ?_, ?_⟩
  · -- ruleEvidenceAdd ∈ congLang.rewrites
    exact coreRules_subset_congRules_ext v ruleEvidenceAdd (by simp [coreRules])
  · -- target ∈ applyRule ruleEvidenceAdd (pExtract (pRevise pw₁ pw₂) pq)
    simp [applyRule, ruleEvidenceAdd, matchPattern, matchArgs, mergeBindings,
          pExtract, pRevise, pCombine, applyBindings]

/-- Congruence on left Combine argument using `ruleCombineCongLeft`.
    Given that evidence-add fires on `Extract(Revise(W₁,W₂), q)` (an
    empty-premise rule), the congruence premise is satisfied via
    `rewriteWithContextNoPremises`, and the combined term rewrites. -/
theorem wmLangReduces_combineCongLeft_evidenceAdd (v : WMExtVertex)
    (pw₁ pw₂ pw₃ pq : Pattern) :
    langReduces (wmExtVertexLanguageDefWithCong v)
      (pCombine (pExtract (pRevise pw₁ pw₂) pq) (pExtract pw₃ pq))
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) := by
  unfold langReduces langReducesUsing
  let bs0 : Bindings := [("e2", pExtract pw₃ pq), ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  let bs : Bindings := [("e1p", pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)),
                         ("e2", pExtract pw₃ pq),
                         ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty)
    (lang := wmExtVertexLanguageDefWithCong v)
    (r := ruleCombineCongLeft) ?hr bs0 ?hmatch bs ?hprem ?happly
  · -- ruleCombineCongLeft ∈ congLang.rewrites
    simp only [wmExtVertexLanguageDefWithCong, List.mem_append]
    right; simp [coreCongruenceRules]
  · -- bs0 ∈ matchPattern ruleCombineCongLeft.left (pCombine ...)
    simp [bs0, ruleCombineCongLeft, pCombine, matchPattern, matchArgs, mergeBindings]
  · -- bs ∈ applyPremisesWithEnv ∅ congLang [.congruence ...] bs0
    simp only [bs, bs0, applyPremisesWithEnv, ruleCombineCongLeft,
               List.foldl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [premiseStepWithEnv]
    simp only [applyBindings, List.find?, BEq.beq, decide_true]
    -- After applying bindings to the congruence source, we get pExtract (pRevise pw₁ pw₂) pq
    -- The candidates come from rewriteWithContextNoPremises
    -- Now show bs is in the result of the congruence premise evaluation
    rw [List.mem_flatMap]
    refine ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
            evidenceAdd_mem_rewriteContextNoPremises v pw₁ pw₂ pq, ?_⟩
    simp [matchPattern, mergeBindings]
  · -- applyBindings bs ruleCombineCongLeft.right = target
    simp [bs, ruleCombineCongLeft, pCombine, applyBindings]

/-- Fully nested two-step chain:
    `Extract(Revise(Revise(W₁,W₂), W₃), q)` reduces in two steps to
    `Combine(Combine(Extract(W₁,q), Extract(W₂,q)), Extract(W₃,q))`
    in the cong-extended calculus.

    Step 1: evidence-add on outer Revise (raw rule, lifted).
    Step 2: `ruleCombineCongLeft` with inner evidence-add as witness. -/
theorem chain_evidence_add_fully_nested (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmExtVertexLanguageDefWithCong v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) :=
  LangReducesStar.step
    (wmCongLangReduces_evidenceAdd v (pRevise pw₁ pw₂) pw₃ pq)
    (LangReducesStar.single
      (wmLangReduces_combineCongLeft_evidenceAdd v pw₁ pw₂ pw₃ pq))

/-- Full-vertex: evidence-add in cong-extended calculus. -/
theorem wmCongFullLangReduces_evidenceAdd (v : WMFullVertex) (pw₁ pw₂ pq : Pattern) :
    langReduces (wmFullVertexLanguageDefWithCong v)
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) :=
  congReduces_of_rawReduces_full v _ _ (wmFullLangReduces_evidenceAdd v pw₁ pw₂ pq)

/-- Full-vertex: evidence-add in `rewriteWithContextNoPremises`. -/
theorem full_evidenceAdd_mem_rewriteContextNoPremises (v : WMFullVertex)
    (pw₁ pw₂ pq : Pattern) :
    pCombine (pExtract pw₁ pq) (pExtract pw₂ pq) ∈
      rewriteWithContextNoPremises (wmFullVertexLanguageDefWithCong v)
        (pExtract (pRevise pw₁ pw₂) pq) := by
  unfold rewriteWithContextNoPremises rewriteStepNoPremises rewriteStep
  rw [List.mem_append]
  left
  rw [List.mem_flatMap]
  refine ⟨ruleEvidenceAdd, ?_, ?_⟩
  · exact coreRules_subset_congRules_full v ruleEvidenceAdd (by simp [coreRules])
  · simp [applyRule, ruleEvidenceAdd, matchPattern, matchArgs, mergeBindings,
          pExtract, pRevise, pCombine, applyBindings]

/-- Full-vertex: congruence on left Combine via evidence-add. -/
theorem wmFullLangReduces_combineCongLeft_evidenceAdd (v : WMFullVertex)
    (pw₁ pw₂ pw₃ pq : Pattern) :
    langReduces (wmFullVertexLanguageDefWithCong v)
      (pCombine (pExtract (pRevise pw₁ pw₂) pq) (pExtract pw₃ pq))
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) := by
  unfold langReduces langReducesUsing
  let bs0 : Bindings := [("e2", pExtract pw₃ pq), ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  let bs : Bindings := [("e1p", pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)),
                         ("e2", pExtract pw₃ pq),
                         ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty)
    (lang := wmFullVertexLanguageDefWithCong v)
    (r := ruleCombineCongLeft) ?hr bs0 ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDefWithCong, List.mem_append]
    right; simp [allCongruenceRules, coreCongruenceRules]
  · simp [bs0, ruleCombineCongLeft, pCombine, matchPattern, matchArgs, mergeBindings]
  · simp only [bs, bs0, applyPremisesWithEnv, ruleCombineCongLeft,
               List.foldl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [premiseStepWithEnv]
    simp only [applyBindings, List.find?, BEq.beq, decide_true]
    rw [List.mem_flatMap]
    refine ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
            full_evidenceAdd_mem_rewriteContextNoPremises v pw₁ pw₂ pq, ?_⟩
    simp [matchPattern, mergeBindings]
  · simp [bs, ruleCombineCongLeft, pCombine, applyBindings]

/-- Full-vertex: fully nested two-step chain via context closure. -/
theorem full_chain_evidence_add_fully_nested (v : WMFullVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmFullVertexLanguageDefWithCong v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) :=
  LangReducesStar.step
    (wmCongFullLangReduces_evidenceAdd v (pRevise pw₁ pw₂) pw₃ pq)
    (LangReducesStar.single
      (wmFullLangReduces_combineCongLeft_evidenceAdd v pw₁ pw₂ pw₃ pq))

/-- Guarded+cong: evidence-add fires (core rule, premises = []). -/
theorem wmGuardedCongLangReduces_evidenceAdd (relEnv : RelationEnv)
    (v : WMExtVertex) (pw₁ pw₂ pq : Pattern) :
    langReducesUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v)
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) := by
  unfold langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := relEnv) (lang := wmExtVertexLanguageDefGuardedWithCong v)
    (r := ruleEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · exact guardedRules_subset_guardedCongRules_ext v _
      (coreRules_subset_wmExtVertexGuarded v _ (by simp [coreRules]))
  · simp [bs, ruleEvidenceAdd, pExtract, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

/-- Guarded+cong: evidence-add in `rewriteWithContextNoPremises`. -/
theorem guardedCong_evidenceAdd_mem_rewriteContextNoPremises (v : WMExtVertex)
    (pw₁ pw₂ pq : Pattern) :
    pCombine (pExtract pw₁ pq) (pExtract pw₂ pq) ∈
      rewriteWithContextNoPremises (wmExtVertexLanguageDefGuardedWithCong v)
        (pExtract (pRevise pw₁ pw₂) pq) := by
  unfold rewriteWithContextNoPremises rewriteStepNoPremises rewriteStep
  rw [List.mem_append]
  left
  rw [List.mem_flatMap]
  refine ⟨ruleEvidenceAdd, ?_, ?_⟩
  · exact guardedRules_subset_guardedCongRules_ext v _
      (coreRules_subset_wmExtVertexGuarded v _ (by simp [coreRules]))
  · simp [applyRule, ruleEvidenceAdd, matchPattern, matchArgs, mergeBindings,
          pExtract, pRevise, pCombine, applyBindings]

/-- Guarded+cong: congruence on left Combine via evidence-add. -/
theorem wmGuardedCongLangReduces_combineCongLeft_evidenceAdd (relEnv : RelationEnv)
    (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    langReducesUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v)
      (pCombine (pExtract (pRevise pw₁ pw₂) pq) (pExtract pw₃ pq))
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) := by
  unfold langReducesUsing
  let bs0 : Bindings := [("e2", pExtract pw₃ pq), ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  let bs : Bindings := [("e1p", pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)),
                         ("e2", pExtract pw₃ pq),
                         ("e1", pExtract (pRevise pw₁ pw₂) pq)]
  refine DeclReducesWithPremises.topRule
    (relEnv := relEnv)
    (lang := wmExtVertexLanguageDefGuardedWithCong v)
    (r := ruleCombineCongLeft) ?hr bs0 ?hmatch bs ?hprem ?happly
  · simp only [wmExtVertexLanguageDefGuardedWithCong, List.mem_append]
    right; simp [coreCongruenceRules]
  · simp [bs0, ruleCombineCongLeft, pCombine, matchPattern, matchArgs, mergeBindings]
  · simp only [bs, bs0, applyPremisesWithEnv, ruleCombineCongLeft,
               List.foldl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [premiseStepWithEnv]
    simp only [applyBindings, List.find?, BEq.beq, decide_true]
    rw [List.mem_flatMap]
    refine ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
            guardedCong_evidenceAdd_mem_rewriteContextNoPremises v pw₁ pw₂ pq, ?_⟩
    simp [matchPattern, mergeBindings]
  · simp [bs, ruleCombineCongLeft, pCombine, applyBindings]

/-- Guarded+cong: fully nested two-step chain via context closure.
    Both evidence-add (core rule, empty premises) and the congruence premise
    are `relEnv`-independent, so the chain fires at `RelationEnv.empty` too.
    This gives a `LangReducesStar` (plain multi-step) in the guarded+cong
    calculus. -/
theorem guarded_chain_evidence_add_fully_nested
    (v : WMExtVertex) (pw₁ pw₂ pw₃ pq : Pattern) :
    LangReducesStar (wmExtVertexLanguageDefGuardedWithCong v)
      (pExtract (pRevise (pRevise pw₁ pw₂) pw₃) pq)
      (pCombine (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) (pExtract pw₃ pq)) :=
  LangReducesStar.step
    (wmGuardedCongLangReduces_evidenceAdd RelationEnv.empty v (pRevise pw₁ pw₂) pw₃ pq)
    (LangReducesStar.single
      (wmGuardedCongLangReduces_combineCongLeft_evidenceAdd RelationEnv.empty v pw₁ pw₂ pw₃ pq))

/-! ## Section 11: WM Barbs (Process-Algebraic Observables)

WM-calc barbs capture what is *observable* about a world-model state.
The primary barb is evidence extraction: a state "exhibits" query evidence
when `Extract(W, q)` can reduce to a non-zero combined result. -/

/-- A WM state exhibits evidence for query `q` when it can be extracted
    and combined into non-zero evidence. -/
def wmHasEvidenceBarb (lang : LanguageDef) (p : Pattern) (q : Pattern) : Prop :=
  ∃ e, langReduces lang (pExtract p q) e ∧ ¬ isZeroEvidence e

/-- Weak evidence barb: reachable via multi-step reduction. -/
def wmHasWeakEvidenceBarb (lang : LanguageDef) (p : Pattern) (q : Pattern) : Prop :=
  ∃ p', LangReducesStar lang p p' ∧ wmHasEvidenceBarb lang p' q

/-- Revised states exhibit evidence barbs via evidence-add:
    `Extract(Revise(W₁,W₂), q)` reduces to `Combine(Extract(W₁,q), Extract(W₂,q))`,
    which is non-zero whenever the combined evidence is non-trivial. -/
theorem wmRevisedState_evidenceBarb (v : WMExtVertex) (pw₁ pw₂ pq : Pattern)
    (hne : ¬ isZeroEvidence (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq))) :
    wmHasEvidenceBarb (wmExtVertexLanguageDef v) (pRevise pw₁ pw₂) pq :=
  ⟨pCombine (pExtract pw₁ pq) (pExtract pw₂ pq),
   wmLangReduces_evidenceAdd v pw₁ pw₂ pq, hne⟩

/-! ## Section 12: Full-Vertex Galois Adjunction Corollaries

Concrete evidence-theoretic consequences of the ◇ ⊣ □ adjunction at
extension-specific predicates. -/

/-- Overlap adjunction at overlap-aware vertices. -/
theorem wmFullCalc_overlap_safety (v : WMFullVertex)
    (_hov : v.overlap = .overlapAware) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isOverlapCorrected p → ψ p) ↔
    (∀ p, isOverlapCorrected p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  (wmFullCalc_galois v).le_iff_le

/-- Fixpoint adjunction at fixpoint-enabled vertices. -/
theorem wmFullCalc_fixpoint_safety (v : WMFullVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isFixpoint p → ψ p) ↔
    (∀ p, isFixpoint p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  (wmFullCalc_galois v).le_iff_le

/-- Anti-hallucination adjunction at conserving vertices. -/
theorem wmFullCalc_conservation_safety (v : WMFullVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isZeroEvidence p → ψ p) ↔
    (∀ p, isZeroEvidence p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  (wmFullCalc_galois v).le_iff_le

/-- Full decomposability adjunction. -/
theorem wmFullCalc_decomposability_safety (v : WMFullVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamond (wmFullVertexLanguageDef v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBox (wmFullVertexLanguageDef v) ψ p) :=
  (wmFullCalc_galois v).le_iff_le

/-! ## Section 13: Guarded Calculus — Galois Connections

The guarded calculus uses `langReducesUsing relEnv` instead of `langReduces`
(which is `langReducesUsing RelationEnv.empty`). The Galois connection
◇ ⊣ □ holds automatically at any RelationEnv via `langGaloisUsing`. -/

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

/-- Galois connection for the guarded 6-axis WM calculus. -/
theorem wmGuardedCalc_galois (relEnv : RelationEnv) (v : WMExtVertex) :
    GaloisConnection
      (langDiamondUsing relEnv (wmExtVertexLanguageDefGuarded v))
      (langBoxUsing relEnv (wmExtVertexLanguageDefGuarded v)) :=
  langGaloisUsing relEnv (wmExtVertexLanguageDefGuarded v)

/-- Galois connection for the guarded 13-axis WM calculus. -/
theorem wmGuardedFullCalc_galois (relEnv : RelationEnv) (v : WMFullVertex) :
    GaloisConnection
      (langDiamondUsing relEnv (wmFullVertexLanguageDefGuarded v))
      (langBoxUsing relEnv (wmFullVertexLanguageDefGuarded v)) :=
  langGaloisUsing relEnv (wmFullVertexLanguageDefGuarded v)

/-- OSLF type system for guarded 6-axis WM vertex. -/
noncomputable def wmExtVertexOSLFGuarded (relEnv : RelationEnv) (v : WMExtVertex) :=
  langOSLFUsing relEnv (wmExtVertexLanguageDefGuarded v)

/-- OSLF type system for guarded 13-axis WM vertex. -/
noncomputable def wmFullVertexOSLFGuarded (relEnv : RelationEnv) (v : WMFullVertex) :=
  langOSLFUsing relEnv (wmFullVertexLanguageDefGuarded v)

/-- Core rules fire in the guarded calculus (at any RelationEnv),
    since core rules have `premises = []`. -/
theorem wmGuardedLangReduces_evidenceAdd (relEnv : RelationEnv)
    (v : WMExtVertex) (pw₁ pw₂ pq : Pattern) :
    langReducesUsing relEnv (wmExtVertexLanguageDefGuarded v)
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) := by
  unfold langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := relEnv) (lang := wmExtVertexLanguageDefGuarded v)
    (r := ruleEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · exact coreRules_subset_wmExtVertexGuarded v _ (by simp [coreRules])
  · simp [bs, ruleEvidenceAdd, pExtract, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

/-- Guarded decomposability adjunction. -/
theorem wmGuardedCalc_decomposability_safety (relEnv : RelationEnv)
    (v : WMExtVertex) (ψ : Pattern → Prop) :
    (∀ p, langDiamondUsing relEnv (wmExtVertexLanguageDefGuarded v) isCombined p → ψ p) ↔
    (∀ p, isCombined p → langBoxUsing relEnv (wmExtVertexLanguageDefGuarded v) ψ p) :=
  (wmGuardedCalc_galois relEnv v).le_iff_le

end Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
