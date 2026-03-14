import Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# WM Calculus as LanguageDef Family (GSLT-Oriented)

This module packages the world-model posterior-state calculus as a family of
`LanguageDef`s indexed by `WMVertex` (the 4-axis WM hypercube from
`PLNWMHypercubeBasis`).

## Architecture

The WM calculus has three sorts:
- **State**: world-model posterior states (revisable via `+`)
- **Query**: evidence queries (propositions, links, conditionals)
- **Evidence**: extracted evidence values

Core rewrite rules encode the WM axioms:
- `evidence_add`: `Extract(Revise(W₁,W₂), q) ↦ Combine(Extract(W₁,q), Extract(W₂,q))`
- `revision_comm`: `Revise(W₁,W₂) ↦ Revise(W₂,W₁)`
- `revision_assoc`: `Revise(Revise(W₁,W₂),W₃) ↦ Revise(W₁,Revise(W₂,W₃))`
- `combine_comm`: `Combine(e₁,e₂) ↦ Combine(e₂,e₁)`

Each WM vertex adds axis-dependent rules (logic, truth-value, interval,
typing).  The weaker vertex has strictly fewer rules, so forward simulation
along the weakness order is `id`-on-terms with rule-subset containment.

## References

- `PLNWorldModel.lean` — `WorldModel` class, `WMJudgment`, `WMQueryJudgment`
- `PLNWorldModelCalculus.lean` — query-rewrite layer
- `PLNWorldModelOverlap.lean` — `OverlapLayer`
- `GenericWorldModelForgetting.lean` — `ForgettingLayer`
- `PLNSelectorLanguageDef.lean` — analogous PLN selector LanguageDef (pattern)
-/

namespace Mettapedia.OSLF.Framework.WMCalculusLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

/-! ## Pattern Vocabulary -/

/-- Revision (parallel composition of posterior states). -/
def pRevise (w₁ w₂ : Pattern) : Pattern := .apply "Revise" [w₁, w₂]

/-- Evidence extraction (observation). -/
def pExtract (w q : Pattern) : Pattern := .apply "Extract" [w, q]

/-- Evidence combination (additive fusion). -/
def pCombine (e₁ e₂ : Pattern) : Pattern := .apply "Combine" [e₁, e₂]

/-- Evidence zero (identity for combination). -/
def pEvidenceZero : Pattern := .apply "EvidenceZero" []

/-- Scalar strength projection. -/
def pStrength (e : Pattern) : Pattern := .apply "Strength" [e]

/-- Interval bounds extraction (lower, upper). -/
def pLowerBound (e : Pattern) : Pattern := .apply "LowerBound" [e]
def pUpperBound (e : Pattern) : Pattern := .apply "UpperBound" [e]

/-- Forgetting operator (restriction/hiding). -/
def pForget (scope w : Pattern) : Pattern := .apply "Forget" [scope, w]

/-- Overlap-aware merge. -/
def pOverlapMerge (w₁ w₂ : Pattern) : Pattern := .apply "OverlapMerge" [w₁, w₂]

/-- Overlap correction factor. -/
def pOverlapCorrect (e₁ e₂ ov : Pattern) : Pattern :=
  .apply "OverlapCorrect" [e₁, e₂, ov]

/-- Overlap factor computation. -/
def pOverlapFactor (w₁ w₂ q : Pattern) : Pattern :=
  .apply "OverlapFactor" [w₁, w₂, q]

/-! ## Core Rewrite Rules (shared across all vertices) -/

/-- `evidence_add`: Extract(Revise(W₁,W₂), q) ↦ Combine(Extract(W₁,q), Extract(W₂,q))
    This is the fundamental WM axiom: evidence extraction distributes over revision. -/
def ruleEvidenceAdd : RewriteRule := {
  name := "WM_EvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pExtract (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pExtract (.fvar "W1") (.fvar "q")) (pExtract (.fvar "W2") (.fvar "q"))
}

/-- `revision_comm`: Revise(W₁,W₂) ↦ Revise(W₂,W₁)
    Revision is commutative (evidence order doesn't matter). -/
def ruleRevisionComm : RewriteRule := {
  name := "WM_RevisionComm"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []
  left := pRevise (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W2") (.fvar "W1")
}

/-- `revision_assoc`: Revise(Revise(W₁,W₂),W₃) ↦ Revise(W₁,Revise(W₂,W₃))
    Revision is associative. -/
def ruleRevisionAssoc : RewriteRule := {
  name := "WM_RevisionAssoc"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("W3", .base "State")]
  premises := []
  left := pRevise (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "W3")
  right := pRevise (.fvar "W1") (pRevise (.fvar "W2") (.fvar "W3"))
}

/-- `combine_comm`: Combine(e₁,e₂) ↦ Combine(e₂,e₁)
    Evidence combination is commutative. -/
def ruleCombineComm : RewriteRule := {
  name := "WM_CombineComm"
  typeContext := [("e1", .base "Evidence"), ("e2", .base "Evidence")]
  premises := []
  left := pCombine (.fvar "e1") (.fvar "e2")
  right := pCombine (.fvar "e2") (.fvar "e1")
}

/-- `combine_zero`: Combine(e, EvidenceZero) ↦ e
    EvidenceZero is identity for combination. -/
def ruleCombineZero : RewriteRule := {
  name := "WM_CombineZero"
  typeContext := [("e", .base "Evidence")]
  premises := []
  left := pCombine (.fvar "e") pEvidenceZero
  right := .fvar "e"
}

/-- The core WM rules shared by all vertices. -/
def coreRules : List RewriteRule :=
  [ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc,
   ruleCombineComm, ruleCombineZero]

/-- The core WM calculus LanguageDef: only the 5 unconditional core rules
    (evidence-add, revision-comm, revision-assoc, combine-comm, combine-zero).
    Used as the "raw core" shared by all vertices, and as the reference
    LanguageDef for encoding faithfulness (WMStep ↔ langReduces). -/
def wmCoreLanguageDef : LanguageDef := {
  name := "WMCalculusCore"
  types := ["State", "Query", "Evidence"]
  terms := []
  equations := []
  rewrites := coreRules
}

/-- Core rules are a subset of the core LanguageDef's rules (trivially). -/
theorem coreRules_subset_wmCore :
    ∀ r ∈ coreRules, r ∈ wmCoreLanguageDef.rewrites := by
  intro r hr; exact hr

/-! ## Axis-Dependent Rules -/

/-- Logic axis rules.
    - `boolean`: no additional rules
    - `heyting`: evidence distributes over meets (conjunction) -/
def logicRules : WMLogic → List RewriteRule
  | .boolean => []
  | .heyting => []  -- heyting adds no rewrite rules at the LanguageDef level;
                     -- the difference is in the predicate algebra (Frame vs Boolean)

/-- Truth-value axis rules.
    - `point`: scalar strength projection available
    - `bounds`: interval bounds projections available -/
def tvRules : WMTruthValue → List RewriteRule
  | .point => []   -- Strength is a view (derived), not a rewrite
  | .bounds => []  -- Bounds are views, not rewrites

/-- Interval semantics axis rules.
    - `bayesNormal`: Combine is ordinary addition (no extra rules)
    - `bayesExact`: Combine carries conjugate update structure
    - `walleyIDM`: Combine uses IDM envelope -/
def intervalRules : WMIntervalSemantics → List RewriteRule
  | .bayesNormal => []
  | .bayesExact => []   -- difference is semantic (combine interpretation), not syntactic
  | .walleyIDM => []

/-- Typing axis rules.
    - `untyped`: no side-condition premises on rules
    - `typedSigma`: type-checking premises added (Σ-guards) -/
def typingRules : WMQueryTyping → List RewriteRule
  | .untyped => []
  | .typedSigma => []  -- Σ-guards are premise-level, already in the core rules

/-! ## Extended Axes: Overlap and Forgetting -/

/-- Overlap axis: whether the calculus has overlap-aware merge rules. -/
inductive WMOverlapMode where
  | additive     : WMOverlapMode  -- pure additive (no overlap correction)
  | overlapAware : WMOverlapMode  -- with OverlapLayer correction rules
  deriving DecidableEq, Repr

instance : LE WMOverlapMode where
  le a b := match a, b with
    | .overlapAware, _ => True | _, .additive => True | .additive, .overlapAware => False

instance : Preorder WMOverlapMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Forgetting axis: whether the calculus has forgetting/restriction rules. -/
inductive WMForgettingMode where
  | none           : WMForgettingMode  -- no forgetting
  | scopeBased     : WMForgettingMode  -- ForgettingLayer rules
  | supportTracked : WMForgettingMode  -- SupportTrackedForgettingLayer rules
  deriving DecidableEq, Repr

instance : LE WMForgettingMode where
  le a b := match a, b with
    | .supportTracked, _ => True | _, .none => True
    | .scopeBased, .scopeBased => True | .none, .scopeBased => False
    | .none, .supportTracked => False | .scopeBased, .supportTracked => False

instance : Preorder WMForgettingMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Overlap-specific rewrite rules.

    `overlapAware`:
    - Extract(OverlapMerge(W₁,W₂), q) ↦ OverlapCorrect(Extract(W₁,q), Extract(W₂,q), OverlapFactor(W₁,W₂,q))
    This captures the non-additive correction from `OverlapLayer.evidence_merge`. -/
def ruleOverlapExtract : RewriteRule := {
  name := "WM_OverlapExtract"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pExtract (pOverlapMerge (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pOverlapCorrect
    (pExtract (.fvar "W1") (.fvar "q"))
    (pExtract (.fvar "W2") (.fvar "q"))
    (pOverlapFactor (.fvar "W1") (.fvar "W2") (.fvar "q"))
}

def overlapRules : WMOverlapMode → List RewriteRule
  | .additive => []
  | .overlapAware => [ruleOverlapExtract]

/-- Forgetting-specific rewrite rules.

    `scopeBased`:
    - Extract(Forget(S, W), q) ↦ Extract(W, q)  [when q ∉ scope S]
    This captures `ForgettingLayer.outsideInvariant`. -/
def ruleForgetOutside : RewriteRule := {
  name := "WM_ForgetOutside"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("q", .base "Query")]
  premises := []  -- side condition (q ∉ scope S) is semantic, not syntactic
  left := pExtract (pForget (.fvar "S") (.fvar "W")) (.fvar "q")
  right := pExtract (.fvar "W") (.fvar "q")
}

/-- Forgetting idempotence: Forget(S, Forget(S, W)) ↦ Forget(S, W) -/
def ruleForgetIdempotent : RewriteRule := {
  name := "WM_ForgetIdempotent"
  typeContext := [("S", .base "Scope"), ("W", .base "State")]
  premises := []
  left := pForget (.fvar "S") (pForget (.fvar "S") (.fvar "W"))
  right := pForget (.fvar "S") (.fvar "W")
}

def forgettingRules : WMForgettingMode → List RewriteRule
  | .none => []
  | .scopeBased => [ruleForgetOutside, ruleForgetIdempotent]
  | .supportTracked => [ruleForgetOutside, ruleForgetIdempotent]
      -- supportTracked adds the exact-inverse theorem but that is a
      -- WorldModel-level theorem, not a new rewrite rule

/-! ## Support-Tracked Forgetting Rules -/

/-- Exact inverse: Forget(S, Revise(W, Δ)) ↦ W when support(Δ) ⊆ scopeFootprint(S).
    From `SupportTrackedForgettingLayer.exactInverse_of_supported`. -/
def ruleExactInverse : RewriteRule := {
  name := "WM_ExactInverse"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("D", .base "State")]
  premises := []  -- side condition: support(Δ) ⊆ scopeFootprint(S)
  left := pForget (.fvar "S") (pRevise (.fvar "W") (.fvar "D"))
  right := .fvar "W"
}

def supportTrackedRules : WMForgettingMode → List RewriteRule
  | .supportTracked => [ruleExactInverse]
  | _ => []

/-! ## Extended Pattern Vocabulary -/

/-- Source compatibility predicate (Kripke weighted overlap). -/
def pSourceCompatible (w₁ w₂ : Pattern) : Pattern :=
  .apply "SourceCompatible" [w₁, w₂]

/-- Partial revision (succeeds only when source-compatible). -/
def pPartialRevision (w₁ w₂ : Pattern) : Pattern :=
  .apply "PartialRevision" [w₁, w₂]

/-- Fallback revision (additive when compatible, left-biased otherwise). -/
def pFallbackRevision (w₁ w₂ : Pattern) : Pattern :=
  .apply "FallbackRevision" [w₁, w₂]

/-- Trusted gate (filters untrusted sources). -/
def pTrustedGate (trusted w : Pattern) : Pattern :=
  .apply "TrustedGate" [trusted, w]

/-- Source-selective forgetting. -/
def pForgetSources (drop w : Pattern) : Pattern :=
  .apply "ForgetSources" [drop, w]

/-- Universal trust policy (trusts all sources). -/
def pTrustedAll : Pattern := .apply "TrustedAll" []

/-- Evidence value one (positive singleton). -/
def pEvidenceOne : Pattern := .apply "EvidenceOne" []

/-- Fixpoint closure operators. -/
def pImmediateStep (rules w seed current : Pattern) : Pattern :=
  .apply "ImmediateStep" [rules, w, seed, current]

def pLeastClosure (rules w seed : Pattern) : Pattern :=
  .apply "LeastClosure" [rules, w, seed]

def pImmediateIter (rules w seed n : Pattern) : Pattern :=
  .apply "ImmediateIter" [rules, w, seed, n]

/-- Successor pattern for iteration index. -/
def pSucc (n : Pattern) : Pattern := .apply "Succ" [n]

/-- Cardinality bound pattern. -/
def pCard (q : Pattern) : Pattern := .apply "Card" [q]

/-- Policy-revised state. -/
def pPolicyRevisedState (trusted w₁ w₂ : Pattern) : Pattern :=
  .apply "PolicyRevisedState" [trusted, w₁, w₂]

/-- Cost/order anomaly operators. -/
def pSwapAnomaly (w₁ w₂ q : Pattern) : Pattern :=
  .apply "SwapAnomaly" [w₁, w₂, q]

def pScheduleError (base steps₁ steps₂ q : Pattern) : Pattern :=
  .apply "ScheduleError" [base, steps₁, steps₂, q]

def pRunSchedule (base steps : Pattern) : Pattern :=
  .apply "RunSchedule" [base, steps]

/-- Conservation / anti-hallucination operators. -/
def pLeakageBudget (scope delta budget : Pattern) : Pattern :=
  .apply "LeakageBudget" [scope, delta, budget]

/-- Experiment channel operators. -/
def pExperimentEvidence (w q : Pattern) : Pattern :=
  .apply "ExperimentEvidence" [w, q]

def pBlackwellPullback (kappa q : Pattern) : Pattern :=
  .apply "BlackwellPullback" [kappa, q]

def pChannelComp (ch₁ ch₂ : Pattern) : Pattern :=
  .apply "ChannelComp" [ch₁, ch₂]

def pChannelId : Pattern := .apply "ChannelId" []

/-- Stochastic channel operators. -/
def pStochEvidence (w q : Pattern) : Pattern :=
  .apply "StochEvidence" [w, q]

def pExpectedUtility (prior ch policy util : Pattern) : Pattern :=
  .apply "ExpectedUtility" [prior, ch, policy, util]

def pOptimalValue (prior ch util : Pattern) : Pattern :=
  .apply "OptimalValue" [prior, ch, util]

def pLiftPolicy (kappa policy : Pattern) : Pattern :=
  .apply "LiftPolicy" [kappa, policy]

def pStochId : Pattern := .apply "StochId" []

/-- Kripke modal operators. -/
def pKripkeEvidence (w phi : Pattern) : Pattern :=
  .apply "KripkeEvidence" [w, phi]

def pSingleton (pk : Pattern) : Pattern :=
  .apply "Singleton" [pk]

/-- Generic carrier operators. -/
def pGenericEvidence (w q : Pattern) : Pattern :=
  .apply "GenericEvidence" [w, q]

/-! ## Provenance Rules (Kripke Weighted Overlap) -/

/-- Provenance axis: source-tracking and compatibility-gated revision. -/
inductive WMProvenanceMode where
  | none              : WMProvenanceMode
  | sourceLabeled     : WMProvenanceMode  -- source compatibility + fallback
  deriving DecidableEq, Repr

instance : LE WMProvenanceMode where
  le a b := match a, b with
    | .sourceLabeled, _ => True | _, .none => True | .none, .sourceLabeled => False

instance : Preorder WMProvenanceMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- SourceCompatible(W₁,W₂) ↦ SourceCompatible(W₂,W₁) -/
def ruleCompatibleSymm : RewriteRule := {
  name := "WM_CompatibleSymm"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []
  left := pSourceCompatible (.fvar "W1") (.fvar "W2")
  right := pSourceCompatible (.fvar "W2") (.fvar "W1")
}

/-- FallbackRevision(W₁,W₂) ↦ Revise(W₁,W₂) when compatible. -/
def ruleFallbackCompatible : RewriteRule := {
  name := "WM_FallbackCompatible"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []  -- side condition: SourceCompatible(W₁,W₂)
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- FallbackRevision(W₁,W₂) ↦ W₁ when incompatible. -/
def ruleFallbackIncompatible : RewriteRule := {
  name := "WM_FallbackIncompatible"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []  -- side condition: ¬ SourceCompatible(W₁,W₂)
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := .fvar "W1"
}

/-- PartialRevision(W₁,W₂) ↦ Revise(W₁,W₂) when compatible. -/
def rulePartialRevisionCompatible : RewriteRule := {
  name := "WM_PartialRevisionCompatible"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []  -- side condition: SourceCompatible(W₁,W₂)
  left := pPartialRevision (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- TrustedGate(TrustedAll, W) ↦ W — universal trust is identity. -/
def ruleTrustedGateAll : RewriteRule := {
  name := "WM_TrustedGateAll"
  typeContext := [("W", .base "State")]
  premises := []
  left := pTrustedGate pTrustedAll (.fvar "W")
  right := .fvar "W"
}

/-- Evidence additivity under compatible fallback revision.
    Extract(FallbackRevision(W₁,W₂), q) ↦ Combine(Extract(W₁,q), Extract(W₂,q))
    [when compatible] -/
def ruleSourceEvidenceAdd : RewriteRule := {
  name := "WM_SourceEvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []  -- side condition: SourceCompatible(W₁,W₂)
  left := pExtract (pFallbackRevision (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pExtract (.fvar "W1") (.fvar "q")) (pExtract (.fvar "W2") (.fvar "q"))
}

def provenanceRules : WMProvenanceMode → List RewriteRule
  | .none => []
  | .sourceLabeled => [ruleCompatibleSymm, ruleFallbackCompatible,
      ruleFallbackIncompatible, rulePartialRevisionCompatible,
      ruleTrustedGateAll, ruleSourceEvidenceAdd]

/-! ## Fixpoint Rules -/

/-- Fixpoint axis: iterative rule closure and cascade. -/
inductive WMFixpointMode where
  | none          : WMFixpointMode
  | closureOnly   : WMFixpointMode  -- least fixpoint closure
  | policyDriven  : WMFixpointMode  -- policy-adapted closure
  | cascade       : WMFixpointMode  -- bounded cascade with card bound
  deriving DecidableEq, Repr

instance : LE WMFixpointMode where
  le a b := match a, b with
    | .cascade, _ => True | _, .none => True
    | .policyDriven, .policyDriven => True | .policyDriven, .closureOnly => True
    | .closureOnly, .closureOnly => True
    | .none, _ => False | .closureOnly, .policyDriven => False
    | .closureOnly, .cascade => False | .policyDriven, .cascade => False

instance : Preorder WMFixpointMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- ImmediateStep(R, W, seed, LeastClosure(R, W, seed)) ↦ LeastClosure(R, W, seed)
    Closure is a fixpoint of the immediate step operator. -/
def ruleClosureFixpoint : RewriteRule := {
  name := "WM_ClosureFixpoint"
  typeContext := [("R", .base "RuleSet"), ("W", .base "State"), ("seed", .base "QuerySet")]
  premises := []
  left := pImmediateStep (.fvar "R") (.fvar "W") (.fvar "seed")
    (pLeastClosure (.fvar "R") (.fvar "W") (.fvar "seed"))
  right := pLeastClosure (.fvar "R") (.fvar "W") (.fvar "seed")
}

/-- ImmediateIter(R, W, seed, n+1) ↦ ImmediateStep(R, W, seed, ImmediateIter(R, W, seed, n))
    Iteration unfolds by one step. -/
def ruleIterUnfolding : RewriteRule := {
  name := "WM_IterUnfolding"
  typeContext := [("R", .base "RuleSet"), ("W", .base "State"),
                  ("seed", .base "QuerySet"), ("n", .base "Nat")]
  premises := []
  left := pImmediateIter (.fvar "R") (.fvar "W") (.fvar "seed") (pSucc (.fvar "n"))
  right := pImmediateStep (.fvar "R") (.fvar "W") (.fvar "seed")
    (pImmediateIter (.fvar "R") (.fvar "W") (.fvar "seed") (.fvar "n"))
}

/-- PolicyRevisedState(TrustedAll, W₁, W₂) ↦ Revise(W₁, W₂) when compatible.
    All-trusted policy with compatible sources reduces to plain revision. -/
def rulePolicyTrustedAllCompatible : RewriteRule := {
  name := "WM_PolicyTrustedAllCompatible"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := []  -- side condition: SourceCompatible(W₁,W₂)
  left := pPolicyRevisedState pTrustedAll (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- ImmediateIter(R, W, seed, Card(Q)) ↦ LeastClosure(R, W, seed)
    On finite query spaces, iteration stabilizes at cardinality bound. -/
def ruleCascadeAtCard : RewriteRule := {
  name := "WM_CascadeAtCard"
  typeContext := [("R", .base "RuleSet"), ("W", .base "State"),
                  ("seed", .base "QuerySet"), ("Q", .base "QuerySpace")]
  premises := []  -- side condition: Fintype Q
  left := pImmediateIter (.fvar "R") (.fvar "W") (.fvar "seed") (pCard (.fvar "Q"))
  right := pLeastClosure (.fvar "R") (.fvar "W") (.fvar "seed")
}

def fixpointRules : WMFixpointMode → List RewriteRule
  | .none => []
  | .closureOnly => [ruleClosureFixpoint, ruleIterUnfolding]
  | .policyDriven => [ruleClosureFixpoint, ruleIterUnfolding,
      rulePolicyTrustedAllCompatible]
  | .cascade => [ruleClosureFixpoint, ruleIterUnfolding,
      rulePolicyTrustedAllCompatible, ruleCascadeAtCard]

/-! ## Cost / Order Bounds Rules -/

/-- Cost axis: swap anomaly and schedule error tracking. -/
inductive WMCostMode where
  | none        : WMCostMode
  | costTracked : WMCostMode
  deriving DecidableEq, Repr

instance : LE WMCostMode where
  le a b := match a, b with
    | .costTracked, _ => True | _, .none => True | .none, .costTracked => False

instance : Preorder WMCostMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- SwapAnomaly(W₁,W₂,q) ↦ SwapAnomaly(W₂,W₁,q) — symmetry of swap cost. -/
def ruleSwapAnomalySymm : RewriteRule := {
  name := "WM_SwapAnomalySymm"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pSwapAnomaly (.fvar "W1") (.fvar "W2") (.fvar "q")
  right := pSwapAnomaly (.fvar "W2") (.fvar "W1") (.fvar "q")
}

/-- SwapAnomaly(W₁,W₂,q) ↦ EvidenceZero when observation counts are equal. -/
def ruleSwapAnomalyZero : RewriteRule := {
  name := "WM_SwapAnomalyZero"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []  -- side condition: count(W₁,W₂,q) = count(W₂,W₁,q)
  left := pSwapAnomaly (.fvar "W1") (.fvar "W2") (.fvar "q")
  right := pEvidenceZero
}

/-- ScheduleError(b,s₁,s₂,q) ↦ ScheduleError(b,s₂,s₁,q) — symmetric in schedules. -/
def ruleScheduleErrorSymm : RewriteRule := {
  name := "WM_ScheduleErrorSymm"
  typeContext := [("b", .base "State"), ("s1", .base "Schedule"),
                  ("s2", .base "Schedule"), ("q", .base "Query")]
  premises := []
  left := pScheduleError (.fvar "b") (.fvar "s1") (.fvar "s2") (.fvar "q")
  right := pScheduleError (.fvar "b") (.fvar "s2") (.fvar "s1") (.fvar "q")
}

def costRules : WMCostMode → List RewriteRule
  | .none => []
  | .costTracked => [ruleSwapAnomalySymm, ruleSwapAnomalyZero, ruleScheduleErrorSymm]

/-! ## Conservation / Anti-Hallucination Rules -/

/-- Conservation axis: Noether-style evidence conservation under forgetting. -/
inductive WMConservationMode where
  | none       : WMConservationMode
  | conserving : WMConservationMode
  deriving DecidableEq, Repr

instance : LE WMConservationMode where
  le a b := match a, b with
    | .conserving, _ => True | _, .none => True | .none, .conserving => False

instance : Preorder WMConservationMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Anti-hallucination: Extract(Δ, q) ↦ EvidenceZero when q is outside scope and
    Δ is a scoped revision with exact inverse. -/
def ruleAntiHallucination : RewriteRule := {
  name := "WM_AntiHallucination"
  typeContext := [("D", .base "State"), ("q", .base "Query")]
  premises := []  -- side conditions: q ∉ scope, exact-inverse property
  left := pExtract (.fvar "D") (.fvar "q")
  right := pEvidenceZero
}

/-- Noether conservation: Extract(Revise(W,Δ), q) ↦ Extract(W, q)
    Outside-scope evidence is transparent to scoped revision. -/
def ruleNoetherConservation : RewriteRule := {
  name := "WM_NoetherConservation"
  typeContext := [("W", .base "State"), ("D", .base "State"), ("q", .base "Query")]
  premises := []  -- side condition: q ∉ scope of Δ
  left := pExtract (pRevise (.fvar "W") (.fvar "D")) (.fvar "q")
  right := pExtract (.fvar "W") (.fvar "q")
}

/-- Zero leakage: LeakageBudget(S, Δ, 0) holds under exact-inverse forgetting. -/
def ruleZeroLeakage : RewriteRule := {
  name := "WM_ZeroLeakage"
  typeContext := [("S", .base "Scope"), ("D", .base "State")]
  premises := []  -- side condition: exact-inverse property
  left := pLeakageBudget (.fvar "S") (.fvar "D") pEvidenceZero
  right := pLeakageBudget (.fvar "S") (.fvar "D") pEvidenceZero
}

def conservationRules : WMConservationMode → List RewriteRule
  | .none => []
  | .conserving => [ruleAntiHallucination, ruleNoetherConservation]

/-! ## Experiment Channel Rules -/

/-- Experiment axis: deterministic and stochastic experiment channels. -/
inductive WMExperimentMode where
  | none          : WMExperimentMode
  | deterministic : WMExperimentMode  -- ExperimentChannel (Θ → Ω)
  | stochastic    : WMExperimentMode  -- StochasticChannel (Θ → PMF Ω)
  deriving DecidableEq, Repr

instance : LE WMExperimentMode where
  le a b := match a, b with
    | .stochastic, _ => True | _, .none => True
    | .deterministic, .deterministic => True | .none, .deterministic => False
    | .none, .stochastic => False | .deterministic, .stochastic => False

instance : Preorder WMExperimentMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Experiment evidence additivity:
    ExperimentEvidence(Revise(W₁,W₂), q) ↦ Combine(ExperimentEvidence(W₁,q), ExperimentEvidence(W₂,q)) -/
def ruleExperimentEvidenceAdd : RewriteRule := {
  name := "WM_ExperimentEvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pExperimentEvidence (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pExperimentEvidence (.fvar "W1") (.fvar "q"))
                     (pExperimentEvidence (.fvar "W2") (.fvar "q"))
}

/-- Blackwell factorization pullback:
    ExperimentEvidence(W, BlackwellPullback(κ, q)) ↦ ExperimentEvidence(W, q)
    When weak = strong ∘ κ, pulled-back queries preserve evidence. -/
def ruleBlackwellPullback : RewriteRule := {
  name := "WM_BlackwellPullback"
  typeContext := [("W", .base "State"), ("k", .base "Channel"), ("q", .base "Query")]
  premises := []  -- side condition: factorization holds
  left := pExperimentEvidence (.fvar "W") (pBlackwellPullback (.fvar "k") (.fvar "q"))
  right := pExperimentEvidence (.fvar "W") (.fvar "q")
}

/-- Channel composition identity: ChannelComp(Ch, ChannelId) ↦ Ch -/
def ruleChannelCompId : RewriteRule := {
  name := "WM_ChannelCompId"
  typeContext := [("Ch", .base "Channel")]
  premises := []
  left := pChannelComp (.fvar "Ch") pChannelId
  right := .fvar "Ch"
}

/-- Stochastic evidence additivity:
    StochEvidence(Revise(W₁,W₂), q) ↦ Combine(StochEvidence(W₁,q), StochEvidence(W₂,q)) -/
def ruleStochEvidenceAdd : RewriteRule := {
  name := "WM_StochEvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pStochEvidence (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pStochEvidence (.fvar "W1") (.fvar "q"))
                     (pStochEvidence (.fvar "W2") (.fvar "q"))
}

/-- Channel composition associativity:
    ChannelComp(ChannelComp(f,g), h) ↦ ChannelComp(f, ChannelComp(g,h)) -/
def ruleChannelCompAssoc : RewriteRule := {
  name := "WM_ChannelCompAssoc"
  typeContext := [("f", .base "Channel"), ("g", .base "Channel"), ("h", .base "Channel")]
  premises := []
  left := pChannelComp (pChannelComp (.fvar "f") (.fvar "g")) (.fvar "h")
  right := pChannelComp (.fvar "f") (pChannelComp (.fvar "g") (.fvar "h"))
}

/-- Blackwell utility transport:
    ExpectedUtility(π, Weak, δ, u) ↦ ExpectedUtility(π, Strong, LiftPolicy(κ,δ), u)
    Under Blackwell factorization, utility is preserved by policy lifting. -/
def ruleBlackwellUtilityTransport : RewriteRule := {
  name := "WM_BlackwellUtilityTransport"
  typeContext := [("pi", .base "Prior"), ("Weak", .base "Channel"),
                  ("Strong", .base "Channel"), ("k", .base "Channel"),
                  ("d", .base "Policy"), ("u", .base "Utility")]
  premises := []  -- side condition: Weak = Strong ≫ κ
  left := pExpectedUtility (.fvar "pi") (.fvar "Weak") (.fvar "d") (.fvar "u")
  right := pExpectedUtility (.fvar "pi") (.fvar "Strong")
    (pLiftPolicy (.fvar "k") (.fvar "d")) (.fvar "u")
}

/-- Kleisli identity: ChannelComp(Ch, StochId) ↦ Ch -/
def ruleKleisliIdentity : RewriteRule := {
  name := "WM_KleisliIdentity"
  typeContext := [("Ch", .base "Channel")]
  premises := []
  left := pChannelComp (.fvar "Ch") pStochId
  right := .fvar "Ch"
}

def experimentRules : WMExperimentMode → List RewriteRule
  | .none => []
  | .deterministic => [ruleExperimentEvidenceAdd, ruleBlackwellPullback, ruleChannelCompId]
  | .stochastic => [ruleExperimentEvidenceAdd, ruleBlackwellPullback, ruleChannelCompId,
      ruleStochEvidenceAdd, ruleChannelCompAssoc, ruleBlackwellUtilityTransport,
      ruleKleisliIdentity]

/-! ## Kripke Modal Rules -/

/-- Kripke axis: pointed Kripke model semantics for modal queries. -/
inductive WMKripkeMode where
  | none          : WMKripkeMode
  | pointedKripke : WMKripkeMode
  deriving DecidableEq, Repr

instance : LE WMKripkeMode where
  le a b := match a, b with
    | .pointedKripke, _ => True | _, .none => True | .none, .pointedKripke => False

instance : Preorder WMKripkeMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Kripke evidence additivity:
    KripkeEvidence(Revise(W₁,W₂), φ) ↦ Combine(KripkeEvidence(W₁,φ), KripkeEvidence(W₂,φ)) -/
def ruleKripkeEvidenceAdd : RewriteRule := {
  name := "WM_KripkeEvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("phi", .base "ModalQuery")]
  premises := []
  left := pKripkeEvidence (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "phi")
  right := pCombine (pKripkeEvidence (.fvar "W1") (.fvar "phi"))
                     (pKripkeEvidence (.fvar "W2") (.fvar "phi"))
}

/-- Singleton satisfaction: KripkeEvidence(Singleton(pk), φ) ↦ EvidenceOne [when pk ⊨ φ] -/
def ruleKripkeSingletonSat : RewriteRule := {
  name := "WM_KripkeSingletonSat"
  typeContext := [("pk", .base "PointedKripke"), ("phi", .base "ModalQuery")]
  premises := []  -- side condition: pk ⊨ φ
  left := pKripkeEvidence (pSingleton (.fvar "pk")) (.fvar "phi")
  right := pEvidenceOne
}

/-- Singleton refutation: KripkeEvidence(Singleton(pk), φ) ↦ EvidenceZero [when pk ⊭ φ] -/
def ruleKripkeSingletonNotSat : RewriteRule := {
  name := "WM_KripkeSingletonNotSat"
  typeContext := [("pk", .base "PointedKripke"), ("phi", .base "ModalQuery")]
  premises := []  -- side condition: ¬ pk ⊨ φ
  left := pKripkeEvidence (pSingleton (.fvar "pk")) (.fvar "phi")
  right := pEvidenceZero
}

def kripkeRules : WMKripkeMode → List RewriteRule
  | .none => []
  | .pointedKripke => [ruleKripkeEvidenceAdd, ruleKripkeSingletonSat,
      ruleKripkeSingletonNotSat]

/-! ## Generic Carrier Rules -/

/-- Carrier axis: concrete (ℝ≥0∞ pairs) vs generic (AddCommMonoid). -/
inductive WMCarrierMode where
  | concrete : WMCarrierMode  -- fixed Evidence = (ℝ≥0∞ × ℝ≥0∞)
  | generic  : WMCarrierMode  -- polymorphic over AddCommMonoid
  deriving DecidableEq, Repr

instance : LE WMCarrierMode where
  le a b := match a, b with
    | .generic, _ => True | _, .concrete => True | .concrete, .generic => False

instance : Preorder WMCarrierMode where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [LE.le]

/-- Generic evidence additivity (the core WorldModel axiom in abstract form):
    GenericEvidence(Revise(W₁,W₂), q) ↦ Combine(GenericEvidence(W₁,q), GenericEvidence(W₂,q)) -/
def ruleGenericEvidenceAdd : RewriteRule := {
  name := "WM_GenericEvidenceAdd"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := []
  left := pGenericEvidence (pRevise (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pGenericEvidence (.fvar "W1") (.fvar "q"))
                     (pGenericEvidence (.fvar "W2") (.fvar "q"))
}

/-- Query equivalence transport:
    GenericEvidence(W, q₁) ↦ GenericEvidence(W, q₂) [when q₁ ≈ q₂] -/
def ruleQueryEquivTransport : RewriteRule := {
  name := "WM_QueryEquivTransport"
  typeContext := [("W", .base "State"), ("q1", .base "Query"), ("q2", .base "Query")]
  premises := []  -- side condition: ∀ W', evidence(W', q₁) = evidence(W', q₂)
  left := pGenericEvidence (.fvar "W") (.fvar "q1")
  right := pGenericEvidence (.fvar "W") (.fvar "q2")
}

def carrierRules : WMCarrierMode → List RewriteRule
  | .concrete => []
  | .generic => [ruleGenericEvidenceAdd, ruleQueryEquivTransport]

/-! ## Guarded Rule Variants

Each side-conditioned rule gets a guarded variant using `Premise.relationQuery`.
The guarded variant has the same `left`/`right` but non-empty `premises`.
A `RelationEnv` must supply the side-condition oracle at reduction time. -/

-- Forgetting guards --

/-- Guarded: Extract(Forget(S, W), q) ↦ Extract(W, q) when q ∉ scope S. -/
def ruleForgetOutsideGuarded : RewriteRule := {
  name := "WM_ForgetOutside_Guarded"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("q", .base "Query")]
  premises := [.relationQuery "outsideScope" [.fvar "S", .fvar "q"]]
  left := pExtract (pForget (.fvar "S") (.fvar "W")) (.fvar "q")
  right := pExtract (.fvar "W") (.fvar "q")
}

/-- Guarded: Forget(S, Revise(W, Δ)) ↦ W when support(Δ) ⊆ scopeFootprint(S). -/
def ruleExactInverseGuarded : RewriteRule := {
  name := "WM_ExactInverse_Guarded"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("D", .base "State")]
  premises := [.relationQuery "supportedBy" [.fvar "D", .fvar "S"]]
  left := pForget (.fvar "S") (pRevise (.fvar "W") (.fvar "D"))
  right := .fvar "W"
}

-- Provenance guards --

/-- Guarded: FallbackRevision(W₁,W₂) ↦ Revise(W₁,W₂) when compatible. -/
def ruleFallbackCompatibleGuarded : RewriteRule := {
  name := "WM_FallbackCompatible_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := [.relationQuery "sourceCompatible" [.fvar "W1", .fvar "W2"]]
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- Guarded: FallbackRevision(W₁,W₂) ↦ W₁ when incompatible. -/
def ruleFallbackIncompatibleGuarded : RewriteRule := {
  name := "WM_FallbackIncompatible_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := [.relationQuery "notSourceCompatible" [.fvar "W1", .fvar "W2"]]
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := .fvar "W1"
}

/-- Guarded: PartialRevision(W₁,W₂) ↦ Revise(W₁,W₂) when compatible. -/
def rulePartialRevisionCompatibleGuarded : RewriteRule := {
  name := "WM_PartialRevisionCompatible_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := [.relationQuery "sourceCompatible" [.fvar "W1", .fvar "W2"]]
  left := pPartialRevision (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- Guarded: Extract(FallbackRevision(W₁,W₂), q) ↦ Combine(Extract(W₁,q), Extract(W₂,q))
    when compatible. -/
def ruleSourceEvidenceAddGuarded : RewriteRule := {
  name := "WM_SourceEvidenceAdd_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := [.relationQuery "sourceCompatible" [.fvar "W1", .fvar "W2"]]
  left := pExtract (pFallbackRevision (.fvar "W1") (.fvar "W2")) (.fvar "q")
  right := pCombine (pExtract (.fvar "W1") (.fvar "q")) (pExtract (.fvar "W2") (.fvar "q"))
}

-- Fixpoint guards --

/-- Guarded: PolicyRevisedState(TrustedAll, W₁, W₂) ↦ Revise(W₁, W₂) when compatible. -/
def rulePolicyTrustedAllCompatibleGuarded : RewriteRule := {
  name := "WM_PolicyTrustedAllCompatible_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State")]
  premises := [.relationQuery "sourceCompatible" [.fvar "W1", .fvar "W2"]]
  left := pPolicyRevisedState pTrustedAll (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2")
}

/-- Guarded: ImmediateIter(R, W, seed, Card(Q)) ↦ LeastClosure(R, W, seed)
    when Q is finite. -/
def ruleCascadeAtCardGuarded : RewriteRule := {
  name := "WM_CascadeAtCard_Guarded"
  typeContext := [("R", .base "RuleSet"), ("W", .base "State"),
                  ("seed", .base "QuerySet"), ("Q", .base "QuerySpace")]
  premises := [.relationQuery "finiteSpace" [.fvar "Q"]]
  left := pImmediateIter (.fvar "R") (.fvar "W") (.fvar "seed") (pCard (.fvar "Q"))
  right := pLeastClosure (.fvar "R") (.fvar "W") (.fvar "seed")
}

-- Cost guards --

/-- Guarded: SwapAnomaly(W₁,W₂,q) ↦ EvidenceZero when counts are equal. -/
def ruleSwapAnomalyZeroGuarded : RewriteRule := {
  name := "WM_SwapAnomalyZero_Guarded"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("q", .base "Query")]
  premises := [.relationQuery "equalCounts" [.fvar "W1", .fvar "W2", .fvar "q"]]
  left := pSwapAnomaly (.fvar "W1") (.fvar "W2") (.fvar "q")
  right := pEvidenceZero
}

-- Conservation guards --

/-- Guarded: Extract(Δ, q) ↦ EvidenceZero when q ∉ scope and exact-inverse holds. -/
def ruleAntiHallucinationGuarded : RewriteRule := {
  name := "WM_AntiHallucination_Guarded"
  typeContext := [("D", .base "State"), ("q", .base "Query")]
  premises := [.relationQuery "outsideScope" [.fvar "D", .fvar "q"],
               .relationQuery "exactInverseProperty" [.fvar "D"]]
  left := pExtract (.fvar "D") (.fvar "q")
  right := pEvidenceZero
}

/-- Guarded: Extract(Revise(W,Δ), q) ↦ Extract(W, q) when q ∉ scope of Δ. -/
def ruleNoetherConservationGuarded : RewriteRule := {
  name := "WM_NoetherConservation_Guarded"
  typeContext := [("W", .base "State"), ("D", .base "State"), ("q", .base "Query")]
  premises := [.relationQuery "outsideScope" [.fvar "D", .fvar "q"]]
  left := pExtract (pRevise (.fvar "W") (.fvar "D")) (.fvar "q")
  right := pExtract (.fvar "W") (.fvar "q")
}

/-- Guarded: ZeroLeakage when exact-inverse holds. -/
def ruleZeroLeakageGuarded : RewriteRule := {
  name := "WM_ZeroLeakage_Guarded"
  typeContext := [("S", .base "Scope"), ("D", .base "State")]
  premises := [.relationQuery "exactInverseProperty" [.fvar "D"]]
  left := pLeakageBudget (.fvar "S") (.fvar "D") pEvidenceZero
  right := pLeakageBudget (.fvar "S") (.fvar "D") pEvidenceZero
}

-- Experiment guards --

/-- Guarded: Blackwell pullback when factorization holds. -/
def ruleBlackwellPullbackGuarded : RewriteRule := {
  name := "WM_BlackwellPullback_Guarded"
  typeContext := [("W", .base "State"), ("k", .base "Channel"), ("q", .base "Query")]
  premises := [.relationQuery "blackwellFactors" [.fvar "k", .fvar "q"]]
  left := pExperimentEvidence (.fvar "W") (pBlackwellPullback (.fvar "k") (.fvar "q"))
  right := pExperimentEvidence (.fvar "W") (.fvar "q")
}

/-- Guarded: Blackwell utility transport when Weak = Strong ≫ κ. -/
def ruleBlackwellUtilityTransportGuarded : RewriteRule := {
  name := "WM_BlackwellUtilityTransport_Guarded"
  typeContext := [("pi", .base "Prior"), ("Weak", .base "Channel"),
                  ("Strong", .base "Channel"), ("k", .base "Channel"),
                  ("d", .base "Policy"), ("u", .base "Utility")]
  premises := [.relationQuery "blackwellFactors" [.fvar "Weak", .fvar "Strong", .fvar "k"]]
  left := pExpectedUtility (.fvar "pi") (.fvar "Weak") (.fvar "d") (.fvar "u")
  right := pExpectedUtility (.fvar "pi") (.fvar "Strong")
    (pLiftPolicy (.fvar "k") (.fvar "d")) (.fvar "u")
}

-- Kripke guards --

/-- Guarded: KripkeEvidence(Singleton(pk), φ) ↦ EvidenceOne when pk ⊨ φ. -/
def ruleKripkeSingletonSatGuarded : RewriteRule := {
  name := "WM_KripkeSingletonSat_Guarded"
  typeContext := [("pk", .base "PointedKripke"), ("phi", .base "ModalQuery")]
  premises := [.relationQuery "kripkeSat" [.fvar "pk", .fvar "phi"]]
  left := pKripkeEvidence (pSingleton (.fvar "pk")) (.fvar "phi")
  right := pEvidenceOne
}

/-- Guarded: KripkeEvidence(Singleton(pk), φ) ↦ EvidenceZero when pk ⊭ φ. -/
def ruleKripkeSingletonNotSatGuarded : RewriteRule := {
  name := "WM_KripkeSingletonNotSat_Guarded"
  typeContext := [("pk", .base "PointedKripke"), ("phi", .base "ModalQuery")]
  premises := [.relationQuery "kripkeNotSat" [.fvar "pk", .fvar "phi"]]
  left := pKripkeEvidence (pSingleton (.fvar "pk")) (.fvar "phi")
  right := pEvidenceZero
}

-- Carrier guards --

/-- Guarded: GenericEvidence(W, q₁) ↦ GenericEvidence(W, q₂) when queries are equivalent. -/
def ruleQueryEquivTransportGuarded : RewriteRule := {
  name := "WM_QueryEquivTransport_Guarded"
  typeContext := [("W", .base "State"), ("q1", .base "Query"), ("q2", .base "Query")]
  premises := [.relationQuery "queryEquiv" [.fvar "q1", .fvar "q2"]]
  left := pGenericEvidence (.fvar "W") (.fvar "q1")
  right := pGenericEvidence (.fvar "W") (.fvar "q2")
}

/-! ### Guarded Axis Rule Selectors -/

def forgettingRulesGuarded : WMForgettingMode → List RewriteRule
  | .none => []
  | .scopeBased => [ruleForgetOutsideGuarded, ruleForgetIdempotent]
  | .supportTracked => [ruleForgetOutsideGuarded, ruleForgetIdempotent]

def supportTrackedRulesGuarded : WMForgettingMode → List RewriteRule
  | .supportTracked => [ruleExactInverseGuarded]
  | _ => []

def provenanceRulesGuarded : WMProvenanceMode → List RewriteRule
  | .none => []
  | .sourceLabeled => [ruleCompatibleSymm, ruleFallbackCompatibleGuarded,
      ruleFallbackIncompatibleGuarded, rulePartialRevisionCompatibleGuarded,
      ruleTrustedGateAll, ruleSourceEvidenceAddGuarded]

def fixpointRulesGuarded : WMFixpointMode → List RewriteRule
  | .none => []
  | .closureOnly => [ruleClosureFixpoint, ruleIterUnfolding]
  | .policyDriven => [ruleClosureFixpoint, ruleIterUnfolding,
      rulePolicyTrustedAllCompatibleGuarded]
  | .cascade => [ruleClosureFixpoint, ruleIterUnfolding,
      rulePolicyTrustedAllCompatibleGuarded, ruleCascadeAtCardGuarded]

def costRulesGuarded : WMCostMode → List RewriteRule
  | .none => []
  | .costTracked => [ruleSwapAnomalySymm, ruleSwapAnomalyZeroGuarded, ruleScheduleErrorSymm]

def conservationRulesGuarded : WMConservationMode → List RewriteRule
  | .none => []
  | .conserving => [ruleAntiHallucinationGuarded, ruleNoetherConservationGuarded]

def experimentRulesGuarded : WMExperimentMode → List RewriteRule
  | .none => []
  | .deterministic => [ruleExperimentEvidenceAdd, ruleBlackwellPullbackGuarded,
      ruleChannelCompId]
  | .stochastic => [ruleExperimentEvidenceAdd, ruleBlackwellPullbackGuarded,
      ruleChannelCompId, ruleStochEvidenceAdd, ruleChannelCompAssoc,
      ruleBlackwellUtilityTransportGuarded, ruleKleisliIdentity]

def kripkeRulesGuarded : WMKripkeMode → List RewriteRule
  | .none => []
  | .pointedKripke => [ruleKripkeEvidenceAdd, ruleKripkeSingletonSatGuarded,
      ruleKripkeSingletonNotSatGuarded]

def carrierRulesGuarded : WMCarrierMode → List RewriteRule
  | .concrete => []
  | .generic => [ruleGenericEvidenceAdd, ruleQueryEquivTransportGuarded]

/-! ## Extended WM Vertex (6-axis, backward compatible) -/

/-- A 6-axis WM vertex: the original 4 axes plus overlap and forgetting. -/
structure WMExtVertex where
  base : WMVertex
  overlap : WMOverlapMode
  forgetting : WMForgettingMode

instance : LE WMExtVertex where
  le v w := v.overlap ≤ w.overlap ∧ v.forgetting ≤ w.forgetting

instance : Preorder WMExtVertex where
  le_refl v := ⟨le_refl _, le_refl _⟩
  le_trans v₁ v₂ v₃ h₁₂ h₂₃ := ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

/-- The weakest extended vertex: pure additive, no forgetting. -/
def wmExtVertexMinimal : WMExtVertex := {
  base := wmVertexClassicalFast
  overlap := .additive
  forgetting := .none
}

/-- The richest extended vertex: heyting, bounds, exact, typed, overlap-aware,
    support-tracked forgetting. -/
def wmExtVertexFull : WMExtVertex := {
  base := wmVertexGeneralExact
  overlap := .overlapAware
  forgetting := .supportTracked
}

/-! ## Full WM Vertex (13-axis) -/

/-- A 13-axis WM vertex covering all extension families.
    The 4 base axes (logic, truthValue, interval, typing) are model-level
    (same LanguageDef, different semantics). The 9 extension axes add
    genuinely new rewrite rules. -/
structure WMFullVertex where
  base         : WMVertex
  overlap      : WMOverlapMode
  forgetting   : WMForgettingMode
  provenance   : WMProvenanceMode
  fixpoint     : WMFixpointMode
  cost         : WMCostMode
  conservation : WMConservationMode
  experiment   : WMExperimentMode
  kripke       : WMKripkeMode
  carrier      : WMCarrierMode

instance : LE WMFullVertex where
  le v w := v.overlap ≤ w.overlap ∧ v.forgetting ≤ w.forgetting ∧
    v.provenance ≤ w.provenance ∧ v.fixpoint ≤ w.fixpoint ∧
    v.cost ≤ w.cost ∧ v.conservation ≤ w.conservation ∧
    v.experiment ≤ w.experiment ∧ v.kripke ≤ w.kripke ∧
    v.carrier ≤ w.carrier

instance : Preorder WMFullVertex where
  le_refl v := ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _,
    le_refl _, le_refl _, le_refl _, le_refl _⟩
  le_trans v₁ v₂ v₃ h₁₂ h₂₃ := ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2.1 h₂₃.2.1,
    le_trans h₁₂.2.2.1 h₂₃.2.2.1, le_trans h₁₂.2.2.2.1 h₂₃.2.2.2.1,
    le_trans h₁₂.2.2.2.2.1 h₂₃.2.2.2.2.1, le_trans h₁₂.2.2.2.2.2.1 h₂₃.2.2.2.2.2.1,
    le_trans h₁₂.2.2.2.2.2.2.1 h₂₃.2.2.2.2.2.2.1,
    le_trans h₁₂.2.2.2.2.2.2.2.1 h₂₃.2.2.2.2.2.2.2.1,
    le_trans h₁₂.2.2.2.2.2.2.2.2 h₂₃.2.2.2.2.2.2.2.2⟩

/-- The minimal full vertex: all extensions disabled. -/
def wmFullVertexMinimal : WMFullVertex := {
  base := wmVertexClassicalFast
  overlap := .additive
  forgetting := .none
  provenance := .none
  fixpoint := .none
  cost := .none
  conservation := .none
  experiment := .none
  kripke := .none
  carrier := .concrete
}

/-- The maximal full vertex: all extensions enabled at strongest level. -/
def wmFullVertexMaximal : WMFullVertex := {
  base := wmVertexGeneralExact
  overlap := .overlapAware
  forgetting := .supportTracked
  provenance := .sourceLabeled
  fixpoint := .cascade
  cost := .costTracked
  conservation := .conserving
  experiment := .stochastic
  kripke := .pointedKripke
  carrier := .generic
}

/-- Embed a 6-axis vertex into the full 13-axis vertex. -/
def wmExtToFull (v : WMExtVertex) : WMFullVertex := {
  base := v.base
  overlap := v.overlap
  forgetting := v.forgetting
  provenance := .none
  fixpoint := .none
  cost := .none
  conservation := .none
  experiment := .none
  kripke := .none
  carrier := .concrete
}

/-! ## LanguageDef Construction -/

/-- All types used by the WM calculus at a given vertex. -/
def wmTypes (v : WMExtVertex) : List String :=
  match v.forgetting with
  | .none => ["State", "Query", "Evidence"]
  | _ => ["State", "Query", "Evidence", "Scope"]

/-- All types used by the full WM calculus. -/
def wmFullTypes (v : WMFullVertex) : List String :=
  let base := ["State", "Query", "Evidence"]
  let scope := match v.forgetting with | .none => [] | _ => ["Scope"]
  let source := match v.provenance with | .none => [] | _ => ["Source", "Policy"]
  let ruleset := match v.fixpoint with | .none => [] | _ => ["RuleSet", "QuerySet", "Nat"]
  let schedule := match v.cost with | .none => [] | _ => ["Schedule"]
  let channel := match v.experiment with
    | .none => []
    | .deterministic => ["Channel"]
    | .stochastic => ["Channel", "Prior", "Policy", "Utility"]
  let modal := match v.kripke with | .none => [] | _ => ["ModalQuery", "PointedKripke"]
  base ++ scope ++ source ++ ruleset ++ schedule ++ channel ++ modal

/-- Assemble the WM calculus LanguageDef for a given extended vertex.
    Each vertex gets the core rules plus axis-dependent rules. -/
def wmExtVertexLanguageDef (v : WMExtVertex) : LanguageDef := {
  name := s!"WMCalculus"
  types := wmTypes v
  terms := []
  equations := []
  rewrites := coreRules
    ++ logicRules (v.base .logic)
    ++ tvRules (v.base .truthValue)
    ++ intervalRules (v.base .interval)
    ++ typingRules (v.base .typing)
    ++ overlapRules v.overlap
    ++ forgettingRules v.forgetting
}

/-- Assemble the full WM calculus LanguageDef for a 13-axis vertex.
    Each axis contributes its own set of rewrite rules. -/
def wmFullVertexLanguageDef (v : WMFullVertex) : LanguageDef := {
  name := "WMCalculusFull"
  types := wmFullTypes v
  terms := []
  equations := []
  rewrites := coreRules
    ++ logicRules (v.base .logic)
    ++ tvRules (v.base .truthValue)
    ++ intervalRules (v.base .interval)
    ++ typingRules (v.base .typing)
    ++ overlapRules v.overlap
    ++ forgettingRules v.forgetting
    ++ supportTrackedRules v.forgetting
    ++ provenanceRules v.provenance
    ++ fixpointRules v.fixpoint
    ++ costRules v.cost
    ++ conservationRules v.conservation
    ++ experimentRules v.experiment
    ++ kripkeRules v.kripke
    ++ carrierRules v.carrier
}

/-- LanguageDef for the basic 4-axis vertex (no overlap/forgetting). -/
def wmVertexLanguageDef (v : WMVertex) : LanguageDef :=
  wmExtVertexLanguageDef { base := v, overlap := .additive, forgetting := .none }

/-! ### Guarded LanguageDef Constructors -/

/-- Guarded WM calculus LanguageDef for a 6-axis vertex.
    Uses guarded variants of side-conditioned rules; core rules are unchanged. -/
def wmExtVertexLanguageDefGuarded (v : WMExtVertex) : LanguageDef := {
  name := s!"WMCalculusGuarded"
  types := wmTypes v
  terms := []
  equations := []
  rewrites := coreRules
    ++ logicRules (v.base .logic)
    ++ tvRules (v.base .truthValue)
    ++ intervalRules (v.base .interval)
    ++ typingRules (v.base .typing)
    ++ overlapRules v.overlap
    ++ forgettingRulesGuarded v.forgetting
}

/-- Guarded WM calculus LanguageDef for a 13-axis vertex.
    All side-conditioned rules use `Premise.relationQuery` guards. -/
def wmFullVertexLanguageDefGuarded (v : WMFullVertex) : LanguageDef := {
  name := "WMCalculusFullGuarded"
  types := wmFullTypes v
  terms := []
  equations := []
  rewrites := coreRules
    ++ logicRules (v.base .logic)
    ++ tvRules (v.base .truthValue)
    ++ intervalRules (v.base .interval)
    ++ typingRules (v.base .typing)
    ++ overlapRules v.overlap
    ++ forgettingRulesGuarded v.forgetting
    ++ supportTrackedRulesGuarded v.forgetting
    ++ provenanceRulesGuarded v.provenance
    ++ fixpointRulesGuarded v.fixpoint
    ++ costRulesGuarded v.cost
    ++ conservationRulesGuarded v.conservation
    ++ experimentRulesGuarded v.experiment
    ++ kripkeRulesGuarded v.kripke
    ++ carrierRulesGuarded v.carrier
}

/-- The 6-axis and full LanguageDefs have the same rewrite rules (when extra axes are off).
    The names differ ("WMCalculus" vs "WMCalculusFull") and supportTracked adds
    the exact-inverse rule in the full version. -/
theorem wmExtToFull_rewrites_eq (v : WMExtVertex)
    (hf : v.forgetting ≠ .supportTracked) :
    (wmFullVertexLanguageDef (wmExtToFull v)).rewrites =
    (wmExtVertexLanguageDef v).rewrites := by
  cases hfg : v.forgetting with
  | none =>
    simp [wmFullVertexLanguageDef, wmExtVertexLanguageDef, wmExtToFull, hfg,
          supportTrackedRules, provenanceRules, fixpointRules, costRules,
          conservationRules, experimentRules, kripkeRules, carrierRules]
  | scopeBased =>
    simp [wmFullVertexLanguageDef, wmExtVertexLanguageDef, wmExtToFull, hfg,
          supportTrackedRules, provenanceRules, fixpointRules, costRules,
          conservationRules, experimentRules, kripkeRules, carrierRules]
  | supportTracked => simp [hfg] at hf

/-! ## Rule Subset Lemmas -/

/-- The core rules are a subset of any 6-axis vertex's rules. -/
theorem coreRules_subset_wmExtVertex (v : WMExtVertex) :
    ∀ r ∈ coreRules, r ∈ (wmExtVertexLanguageDef v).rewrites := by
  intro r hr
  simp only [wmExtVertexLanguageDef, List.mem_append] at hr ⊢
  left; left; left; left; left; left; exact hr

/-- The core rules are a subset of any full vertex's rules. -/
theorem coreRules_subset_wmFullVertex (v : WMFullVertex) :
    ∀ r ∈ coreRules, r ∈ (wmFullVertexLanguageDef v).rewrites := by
  intro r hr
  simp only [wmFullVertexLanguageDef, List.mem_append] at hr ⊢
  repeat (first | exact hr | left)

/-- The core rules are a subset of any guarded 6-axis vertex's rules. -/
theorem coreRules_subset_wmExtVertexGuarded (v : WMExtVertex) :
    ∀ r ∈ coreRules, r ∈ (wmExtVertexLanguageDefGuarded v).rewrites := by
  intro r hr
  simp only [wmExtVertexLanguageDefGuarded, List.mem_append] at hr ⊢
  left; left; left; left; left; left; exact hr

/-- The core rules are a subset of any guarded full vertex's rules. -/
theorem coreRules_subset_wmFullVertexGuarded (v : WMFullVertex) :
    ∀ r ∈ coreRules, r ∈ (wmFullVertexLanguageDefGuarded v).rewrites := by
  intro r hr
  simp only [wmFullVertexLanguageDefGuarded, List.mem_append] at hr ⊢
  repeat (first | exact hr | left)

/-! ### Guarded ⊆ Raw: Forgetful Relationship

A guarded rule has `premises ≠ []`, while the corresponding raw rule has
`premises = []`. Dropping premises only enables MORE reductions (every
guarded reduction is also a raw reduction). The direction is:
  guarded → raw (for each rule pair).

The key insight: for a rule with `premises = []`, `applyPremisesWithEnv` is
the identity on bindings. For a guarded rule, `applyPremisesWithEnv` filters
bindings through the RelationEnv. Since both rules share `left`/`right`, any
bindings that survive premise checking also match the raw rule. -/

/-- Every guarded rule in `forgettingRulesGuarded` has a same-`left`/`right`
    counterpart in `forgettingRules`. -/
theorem forgettingRulesGuarded_left_right_match (mode : WMForgettingMode) :
    ∀ rg ∈ forgettingRulesGuarded mode,
    ∃ rr ∈ forgettingRules mode,
      rg.left = rr.left ∧ rg.right = rr.right := by
  intro rg hrg
  cases mode with
  | none => simp [forgettingRulesGuarded] at hrg
  | scopeBased =>
    simp only [forgettingRulesGuarded, List.mem_cons, List.mem_nil_iff, or_false] at hrg
    rcases hrg with rfl | rfl
    · exact ⟨ruleForgetOutside, by simp [forgettingRules], rfl, rfl⟩
    · exact ⟨ruleForgetIdempotent, by simp [forgettingRules], rfl, rfl⟩
  | supportTracked =>
    simp only [forgettingRulesGuarded, List.mem_cons, List.mem_nil_iff, or_false] at hrg
    rcases hrg with rfl | rfl
    · exact ⟨ruleForgetOutside, by simp [forgettingRules], rfl, rfl⟩
    · exact ⟨ruleForgetIdempotent, by simp [forgettingRules], rfl, rfl⟩

/-! ## LanguageDef Step Lemmas -/

/-- Abbreviation for WM calculus reduction at a given extended vertex. -/
abbrev wmLangReduces (v : WMExtVertex) (p q : Pattern) : Prop :=
  langReduces (wmExtVertexLanguageDef v) p q

/-- Abbreviation for full WM calculus reduction. -/
abbrev wmFullLangReduces (v : WMFullVertex) (p q : Pattern) : Prop :=
  langReduces (wmFullVertexLanguageDef v) p q

/-- The evidence-add rule fires at any vertex. -/
theorem wmLangReduces_evidenceAdd (v : WMExtVertex) (pw₁ pw₂ pq : Pattern) :
    wmLangReduces v
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) := by
  unfold wmLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmExtVertexLanguageDef v)
    (r := ruleEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmExtVertexLanguageDef, coreRules]
  · simp [bs, ruleEvidenceAdd, pExtract, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

/-- The revision-commutativity rule fires at any vertex. -/
theorem wmLangReduces_revisionComm (v : WMExtVertex) (pw₁ pw₂ : Pattern) :
    wmLangReduces v
      (pRevise pw₁ pw₂)
      (pRevise pw₂ pw₁) := by
  unfold wmLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmExtVertexLanguageDef v)
    (r := ruleRevisionComm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmExtVertexLanguageDef, coreRules]
  · simp [bs, ruleRevisionComm, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionComm, applyPremisesWithEnv]
  · simp [bs, ruleRevisionComm, pRevise, applyBindings]

/-- The revision-associativity rule fires at any vertex. -/
theorem wmLangReduces_revisionAssoc (v : WMExtVertex) (pw₁ pw₂ pw₃ : Pattern) :
    wmLangReduces v
      (pRevise (pRevise pw₁ pw₂) pw₃)
      (pRevise pw₁ (pRevise pw₂ pw₃)) := by
  unfold wmLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W3", pw₃), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmExtVertexLanguageDef v)
    (r := ruleRevisionAssoc)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp [wmExtVertexLanguageDef, coreRules]
  · simp [bs, ruleRevisionAssoc, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionAssoc, applyPremisesWithEnv]
  · simp [bs, ruleRevisionAssoc, pRevise, applyBindings]

/-! ## Full-Vertex Step Lemmas

Step lemmas for `wmFullLangReduces` (13-axis vertex).  Core rules fire at any
vertex; extension-axis rules fire when the corresponding axis is enabled. -/

/-- Core evidence-add at any full vertex. -/
theorem wmFullLangReduces_evidenceAdd (v : WMFullVertex) (pw₁ pw₂ pq : Pattern) :
    wmFullLangReduces v
      (pExtract (pRevise pw₁ pw₂) pq)
      (pCombine (pExtract pw₁ pq) (pExtract pw₂ pq)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · exact coreRules_subset_wmFullVertex v _ (by simp [coreRules])
  · simp [bs, ruleEvidenceAdd, pExtract, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleEvidenceAdd, pExtract, pCombine, applyBindings]

/-- Core revision-commutativity at any full vertex. -/
theorem wmFullLangReduces_revisionComm (v : WMFullVertex) (pw₁ pw₂ : Pattern) :
    wmFullLangReduces v
      (pRevise pw₁ pw₂)
      (pRevise pw₂ pw₁) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleRevisionComm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · exact coreRules_subset_wmFullVertex v _ (by simp [coreRules])
  · simp [bs, ruleRevisionComm, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionComm, applyPremisesWithEnv]
  · simp [bs, ruleRevisionComm, pRevise, applyBindings]

/-- Core revision-associativity at any full vertex. -/
theorem wmFullLangReduces_revisionAssoc (v : WMFullVertex) (pw₁ pw₂ pw₃ : Pattern) :
    wmFullLangReduces v
      (pRevise (pRevise pw₁ pw₂) pw₃)
      (pRevise pw₁ (pRevise pw₂ pw₃)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W3", pw₃), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleRevisionAssoc)
    ?hr bs ?hmatch bs ?hprem ?happly
  · exact coreRules_subset_wmFullVertex v _ (by simp [coreRules])
  · simp [bs, ruleRevisionAssoc, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleRevisionAssoc, applyPremisesWithEnv]
  · simp [bs, ruleRevisionAssoc, pRevise, applyBindings]

/-! ### Extension Axis Step Lemmas -/

/-- Helper: a rule in an axis rule list is in the full vertex's rewrites. -/
private theorem axisRule_mem_wmFullVertex (v : WMFullVertex)
    (r : RewriteRule)
    (axisList : List RewriteRule)
    (hr : r ∈ axisList)
    (haxis : axisList ⊆ (wmFullVertexLanguageDef v).rewrites) :
    r ∈ (wmFullVertexLanguageDef v).rewrites :=
  haxis hr

/-- Overlap-extract at an overlap-aware full vertex. -/
theorem wmFullLangReduces_overlapExtract (v : WMFullVertex)
    (hov : v.overlap = .overlapAware) (pw₁ pw₂ pq : Pattern) :
    wmFullLangReduces v
      (pExtract (pOverlapMerge pw₁ pw₂) pq)
      (pOverlapCorrect (pExtract pw₁ pq) (pExtract pw₂ pq)
                       (pOverlapFactor pw₁ pw₂ pq)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleOverlapExtract)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hov, overlapRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleOverlapExtract, pExtract, pOverlapMerge, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleOverlapExtract, applyPremisesWithEnv]
  · simp [bs, ruleOverlapExtract, pExtract, pOverlapCorrect, pOverlapFactor, applyBindings]

/-- Forget-outside at a forgetting-enabled full vertex. -/
theorem wmFullLangReduces_forgetOutside (v : WMFullVertex)
    (hfg : v.forgetting = .scopeBased ∨ v.forgetting = .supportTracked)
    (pS pw pq : Pattern) :
    wmFullLangReduces v
      (pExtract (pForget pS pw) pq)
      (pExtract pw pq) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W", pw), ("S", pS)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleForgetOutside)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, List.mem_append]
    rcases hfg with hfg | hfg <;> simp [hfg, forgettingRules]
  · simp [bs, ruleForgetOutside, pExtract, pForget, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleForgetOutside, applyPremisesWithEnv]
  · simp [bs, ruleForgetOutside, pExtract, applyBindings]

/-- Exact-inverse at a support-tracked full vertex. -/
theorem wmFullLangReduces_exactInverse (v : WMFullVertex)
    (hfg : v.forgetting = .supportTracked)
    (pS pw pD : Pattern) :
    wmFullLangReduces v
      (pForget pS (pRevise pw pD))
      pw := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W", pw), ("D", pD), ("S", pS)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleExactInverse)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hfg, supportTrackedRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleExactInverse, pForget, pRevise, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleExactInverse, applyPremisesWithEnv]
  · simp [bs, ruleExactInverse, applyBindings]

/-- Compatible-symmetry at a provenance-enabled full vertex. -/
theorem wmFullLangReduces_compatibleSymm (v : WMFullVertex)
    (hprov : v.provenance = .sourceLabeled) (pw₁ pw₂ : Pattern) :
    wmFullLangReduces v
      (pSourceCompatible pw₁ pw₂)
      (pSourceCompatible pw₂ pw₁) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleCompatibleSymm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hprov, provenanceRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleCompatibleSymm, pSourceCompatible, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleCompatibleSymm, applyPremisesWithEnv]
  · simp [bs, ruleCompatibleSymm, pSourceCompatible, applyBindings]

/-- Closure fixpoint at a fixpoint-enabled full vertex. -/
theorem wmFullLangReduces_closureFixpoint (v : WMFullVertex)
    (hfp : v.fixpoint = .closureOnly ∨ v.fixpoint = .policyDriven ∨ v.fixpoint = .cascade)
    (pR pw pseed : Pattern) :
    wmFullLangReduces v
      (pImmediateStep pR pw pseed (pLeastClosure pR pw pseed))
      (pLeastClosure pR pw pseed) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W", pw), ("seed", pseed), ("R", pR)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleClosureFixpoint)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, List.mem_append]
    rcases hfp with hfp | hfp | hfp <;> simp [hfp, fixpointRules]
  · simp [bs, ruleClosureFixpoint, pImmediateStep, pLeastClosure,
          matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleClosureFixpoint, applyPremisesWithEnv]
  · simp [bs, ruleClosureFixpoint, pLeastClosure, applyBindings]

/-- Swap-anomaly symmetry at a cost-tracked full vertex. -/
theorem wmFullLangReduces_swapAnomalySymm (v : WMFullVertex)
    (hcost : v.cost = .costTracked) (pw₁ pw₂ pq : Pattern) :
    wmFullLangReduces v
      (pSwapAnomaly pw₁ pw₂ pq)
      (pSwapAnomaly pw₂ pw₁ pq) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("W2", pw₂), ("q", pq), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleSwapAnomalySymm)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hcost, costRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleSwapAnomalySymm, pSwapAnomaly, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleSwapAnomalySymm, applyPremisesWithEnv]
  · simp [bs, ruleSwapAnomalySymm, pSwapAnomaly, applyBindings]

/-- Anti-hallucination at a conserving full vertex. -/
theorem wmFullLangReduces_antiHallucination (v : WMFullVertex)
    (hcons : v.conservation = .conserving) (pD pq : Pattern) :
    wmFullLangReduces v
      (pExtract pD pq)
      pEvidenceZero := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("D", pD)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleAntiHallucination)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hcons, conservationRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleAntiHallucination, pExtract, matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleAntiHallucination, applyPremisesWithEnv]
  · simp [bs, ruleAntiHallucination, pEvidenceZero, applyBindings]

/-- Experiment evidence additivity at an experiment-enabled full vertex. -/
theorem wmFullLangReduces_experimentEvidenceAdd (v : WMFullVertex)
    (hexp : v.experiment = .deterministic ∨ v.experiment = .stochastic)
    (pw₁ pw₂ pq : Pattern) :
    wmFullLangReduces v
      (pExperimentEvidence (pRevise pw₁ pw₂) pq)
      (pCombine (pExperimentEvidence pw₁ pq) (pExperimentEvidence pw₂ pq)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleExperimentEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, List.mem_append]
    rcases hexp with hexp | hexp <;> simp [hexp, experimentRules]
  · simp [bs, ruleExperimentEvidenceAdd, pExperimentEvidence, pRevise,
          matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleExperimentEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleExperimentEvidenceAdd, pExperimentEvidence, pCombine, applyBindings]

/-- Kripke evidence additivity at a Kripke-enabled full vertex. -/
theorem wmFullLangReduces_kripkeEvidenceAdd (v : WMFullVertex)
    (hkr : v.kripke = .pointedKripke) (pw₁ pw₂ pphi : Pattern) :
    wmFullLangReduces v
      (pKripkeEvidence (pRevise pw₁ pw₂) pphi)
      (pCombine (pKripkeEvidence pw₁ pphi) (pKripkeEvidence pw₂ pphi)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("phi", pphi), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleKripkeEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hkr, kripkeRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleKripkeEvidenceAdd, pKripkeEvidence, pRevise,
          matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleKripkeEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleKripkeEvidenceAdd, pKripkeEvidence, pCombine, applyBindings]

/-- Generic evidence additivity at a generic-carrier full vertex. -/
theorem wmFullLangReduces_genericEvidenceAdd (v : WMFullVertex)
    (hca : v.carrier = .generic) (pw₁ pw₂ pq : Pattern) :
    wmFullLangReduces v
      (pGenericEvidence (pRevise pw₁ pw₂) pq)
      (pCombine (pGenericEvidence pw₁ pq) (pGenericEvidence pw₂ pq)) := by
  unfold wmFullLangReduces langReduces langReducesUsing
  let bs : Bindings := [("q", pq), ("W2", pw₂), ("W1", pw₁)]
  refine DeclReducesWithPremises.topRule
    (relEnv := RelationEnv.empty) (lang := wmFullVertexLanguageDef v)
    (r := ruleGenericEvidenceAdd)
    ?hr bs ?hmatch bs ?hprem ?happly
  · simp only [wmFullVertexLanguageDef, hca, carrierRules, List.mem_append,
               List.mem_cons, List.mem_nil_iff]
    tauto
  · simp [bs, ruleGenericEvidenceAdd, pGenericEvidence, pRevise,
          matchPattern, matchArgs, mergeBindings]
  · simp [bs, ruleGenericEvidenceAdd, applyPremisesWithEnv]
  · simp [bs, ruleGenericEvidenceAdd, pGenericEvidence, pCombine, applyBindings]

/-! ## OSLF Per Vertex (Automatic) -/

/-- OSLF type system for any extended WM vertex.
    The Galois connection ◇ ⊣ □ is derived automatically by `langOSLF`. -/
noncomputable def wmExtVertexOSLF (v : WMExtVertex) :=
  langOSLF (wmExtVertexLanguageDef v)

/-- OSLF type system for basic 4-axis WM vertex. -/
noncomputable def wmVertexOSLF (v : WMVertex) :=
  langOSLF (wmVertexLanguageDef v)

/-- OSLF type system for full 13-axis WM vertex. -/
noncomputable def wmFullVertexOSLF (v : WMFullVertex) :=
  langOSLF (wmFullVertexLanguageDef v)

end Mettapedia.OSLF.Framework.WMCalculusLanguageDef
