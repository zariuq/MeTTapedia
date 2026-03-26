import Mettapedia.Languages.GF.HandCrafted.Core
import Mettapedia.Logic.EvidenceKind
import Mathlib.Algebra.Group.Defs

/-!
# SUMO Repair BinaryEvidence Model

Structured evidence framework for the SUMO ontology repair pipeline.
Designed for multi-agent review (Claude Code, Codex, GPT-5.2 Pro, human)
with PLN-compatible truth values and Beta-distribution assurance scoring.

## Architecture

BinaryEvidence atoms from heterogeneous sources (checkLang, stratum scans,
KIF citations, literature, LLM reviews, human reviews, English docs)
are normalized into a common schema. Each atom carries source type,
strength, confidence, and an independence group (to avoid
double-counting correlated evidence).

Assurance is computed via weighted Beta aggregation:
- Archetype prior (alpha0, beta0) captures "how easy this error kind is to trust"
- Each evidence atom contributes weighted pseudo-counts
- The ass-number = lower 95% bound of Beta(alpha, beta)

## Compatibility

- BinaryEvidence counts (n⁺, n⁻) align with `Mettapedia.Logic.EvidenceQuantale`
- Strength/confidence align with PLN SimpleTruthValue
- Review votes are meta-evidence with source_type = llmReview/humanReview

## Policy

- autoFixable = candidate eligible for auto-fix (not "apply now")
- Apply only when: required witnesses + assurance ≥ threshold + review quorum
- No KIF or SUMO-GF repairs without evidence gate passing
- englishDoc evidence is corroborative only, never sole authority
-/

namespace Mettapedia.Languages.GF.SUMO.EvidenceModel

/-! ## Repair Archetypes (prior strength by error kind)

Error kind determines base prior (alpha0, beta0).
Higher alpha0 relative to beta0 = easier to trust from less evidence. -/

inductive RepairArchetype where
  | syntaxArity              -- exist→exists, missing args, arity mismatch
  | argSwapTyped             -- typed argument swap (e.g., D24)
  | domainNarrowing          -- domain too tight (e.g., D26 Group→AutonomousAgent)
  | hierarchyGap             -- missing intermediate subclass edge (e.g., D23)
  | ontologyReclassification -- reclassify concept branch (e.g., D1 Pain)
  | worldSemanticClaim       -- deep semantic/world-model judgment
  deriving Repr, BEq

def archetypePrior : RepairArchetype → Float × Float
  | .syntaxArity              => (12.0, 1.0)
  | .argSwapTyped             => (10.0, 1.5)
  | .domainNarrowing          => (7.0, 3.0)
  | .hierarchyGap             => (6.0, 3.5)
  | .ontologyReclassification => (4.0, 4.0)
  | .worldSemanticClaim       => (3.0, 5.0)

/-! ## BinaryEvidence Sources -/

inductive SourceType where
  | checkLang    -- proven-sound reachability test (checkLangUsing_sat_sound)
  | stratumScan  -- constraint_check.py output
  | kifCitation  -- direct KIF file:line reference
  | kifRendered  -- deterministic KIF axiom → controlled English via SUMO format templates
  | engGFParsed  -- English parses to unique GF tree matching KIF structure
  | docGFParsed  -- SUMO doc definition parses to GF tree, cross-checked against KIF
  | literature   -- encyclopedia, medical standard, etc.
  | llmReview    -- Claude Code / Codex / GPT-5.2 Pro vote
  | englishDoc   -- corroborative hint from SUMO (documentation ...) string
  | humanReview  -- human expert vote
  deriving Repr, BEq

/-- Base weight by source type. checkLang is highest (proven sound).
    kifRendered is above literature (deterministic, faithful to KIF structure).
    englishDoc is lowest (prose-level, not logic-level). -/
def sourceWeight : SourceType → Float
  | .checkLang    => 1.00
  | .stratumScan  => 0.75
  | .kifCitation  => 0.65
  | .kifRendered  => 0.50  -- deterministic template rendering of KIF axioms
  | .engGFParsed  => 0.60  -- GF runtime: unique parse tree + roundtrip verified
  | .docGFParsed  => 0.50  -- doc definition: GF-parsed + KIF cross-checked
  | .literature   => 0.45
  | .llmReview    => 0.35
  | .englishDoc   => 0.30
  | .humanReview  => 0.60

inductive EvidenceDirection where
  | supports | contradicts
  deriving Repr, BEq

/-! ## WM Result (typed reachability test outcome) -/

/-- Typed result of a world-model reachability test.
    Replaces untyped String "sat"/"unsat"/"na" for static checking. -/
inductive WMResult where
  | sat   -- reachability query returned satisfiable
  | unsat -- reachability query returned unsatisfiable
  | na    -- test not applicable at this decision point
  deriving Repr, BEq

instance : ToString WMResult where
  toString | .sat => "sat" | .unsat => "unsat" | .na => "na"

/-! ## WM Witnesses (persisted checkLang results)

Each witness records one reachabilityTest call from SumoNTT's
Comprehensive Audit, with expected and observed results. -/

structure WMWitness where
  id : String          -- e.g., "D24a"
  query : String       -- e.g., "reachabilityTest \"CognitiveAgent\" \"process\""
  expected : WMResult  -- typed: .sat | .unsat | .na
  observed : WMResult  -- typed: .sat | .unsat | .na
  passed : Bool
  sourceRef : String   -- e.g., "SumoNTT.lean:1124"
  note : String := ""
  deriving Repr

/-! ## BinaryEvidence Atoms (normalized, all types)

Every piece of evidence — whether from checkLang, a KIF citation,
a literature source, an LLM review, or an English doc extraction —
is stored in this schema. -/

structure EvidenceAtom where
  claimId : String              -- e.g., "D24.arg_swap.pre"
  decisionId : Nat
  archetype : RepairArchetype
  direction : EvidenceDirection
  sourceType : SourceType
  sourceRef : String            -- file:line or run-id
  formalExpr : String           -- OSLF expression or scanner fact
  strength : Float              -- 0..1
  confidence : Float            -- 0..1
  independenceGroup : String    -- same group → downweight
  artifactHash : String         -- reproducibility hash
  deriving Repr

/-! ## Doc Claims (English documentation evidence)

Typed claims extracted from SUMO English documentation strings by
the Python extraction pipeline (sumo_doc_to_evidence_atoms.py).
English-doc evidence is corroborative only: weight 0.30, caps at
strength/confidence ≤ 0.60. Cannot override hard KIF/typed evidence. -/

inductive DocClaimKind where
  | subclassHint      -- doc suggests term is a subclass of X
  | instanceHint      -- doc suggests term is an instance of X
  | domainHint        -- doc suggests a relation has a domain constraint
  | termLabelMatch    -- termFormat agrees with documentation text
  | termLabelConflict -- termFormat label conflicts with documentation text
  deriving Repr, BEq

structure DocClaim where
  term : String            -- the SUMO term being documented
  claimKind : DocClaimKind
  targetTerm : String      -- the related concept (superclass, type, etc.)
  confidence : Float       -- extraction confidence (0..1); max 0.6 per policy
  sourceFile : String      -- which KIF file
  sourceLine : Nat         -- line number of documentation entry
  rawText : String         -- the documentation text (truncated to 200 chars)
  extractedBy : String     -- regex pattern ID that matched (e.g., "P1", "P3")
  deriving Repr

/-! ## Review Voting -/

inductive ReviewVerdict where
  | approve | reject | abstain
  deriving Repr, BEq

structure ReviewVote where
  decisionId : Nat
  reviewer : String       -- "claude_code" | "codex" | "gpt52_pro" | "human"
  verdict : ReviewVerdict
  confidence : Float      -- 0..1
  rationaleHash : String  -- hash of rationale text
  evidenceHash : String   -- hash of evidence bundle reviewed
  deriving Repr

/-! ## Review State (lifecycle of a repair decision) -/

inductive ReviewState where
  | pendingReview    -- awaiting reviews
  | reviewApproved   -- quorum met, evidence sufficient
  | applied          -- fix applied to KIF/SUMO-GF
  | verified         -- post-apply regression checks passed
  | rejected         -- strong contradictory evidence
  deriving Repr, BEq

/-! ## Assurance Scoring (Beta distribution)

Computed from archetype prior + weighted evidence atoms.
The ass-number (assuranceLower95) is the key automation threshold. -/

structure AssuranceSummary where
  decisionId : Nat
  alpha : Float                -- pseudo-count positive
  beta : Float                 -- pseudo-count negative
  posteriorMean : Float        -- alpha / (alpha + beta)
  assuranceLower95 : Float     -- lower 95% CI bound (the "ass-number")
  evidenceCompleteness : Float -- fraction of required witnesses present (0..1)
  contradictionMass : Float    -- beta - beta0
  deriving Repr

/-! ## Assurance Computation

Wilson score lower-bound approximation for the Beta posterior.
Uses normal approximation to Beta CDF:
  lower = (p̂ + z²/(2n) - z·√(p̂(1-p̂)/n + z²/(4n²))) / (1 + z²/n)
where z = 1.645 (one-sided 95%), n = alpha + beta.

This is a Float-level computation for pipeline scoring.
The formal algebraic treatment is in EvidenceQuantale.lean (ℝ≥0∞ level). -/

def wilsonLower95 (alpha beta : Float) : Float :=
  let z : Float := 1.645  -- 95% one-sided
  let n := alpha + beta
  if n < 1.0 then 0.0
  else
    let p := alpha / n
    let z2 := z * z
    let denom := 1.0 + z2 / n
    let inner := p * (1.0 - p) / n + z2 / (4.0 * n * n)
    let num := p + z2 / (2.0 * n) - z * Float.sqrt (if inner < 0.0 then 0.0 else inner)
    let result := num / denom
    if result < 0.0 then 0.0 else result

/-- Effective weight of an evidence atom: sourceWeight * strength * confidence. -/
def atomWeight (a : EvidenceAtom) : Float :=
  sourceWeight a.sourceType * a.strength * a.confidence

/-- Deduplicate atoms by independence group: keep only the highest-weight
    atom per group. This prevents double-counting correlated evidence
    (e.g., multiple LLM reviews from the same model family). -/
def deduplicateByGroup (atoms : List EvidenceAtom) : List EvidenceAtom :=
  let grouped := atoms.foldl (fun (acc : List (String × EvidenceAtom)) a =>
    match acc.find? fun (k, _) => k == a.independenceGroup with
    | none => (a.independenceGroup, a) :: acc
    | some (_, existing) =>
      if atomWeight a > atomWeight existing then
        acc.map fun (k, v) =>
          if k == a.independenceGroup then (k, a) else (k, v)
      else acc) []
  grouped.map Prod.snd

/-- Aggregate evidence atoms for a single decision into an AssuranceSummary.
    Applies archetype prior then adds weighted pseudo-counts per atom.
    Independence groups are deduplicated (max weight per group). -/
def computeAssuranceWith (decisionId : Nat) (archetype : RepairArchetype)
    (atoms : List EvidenceAtom) (completeness : Float) : AssuranceSummary :=
  let deduped := deduplicateByGroup atoms
  let (alpha0, beta0) := archetypePrior archetype
  let (posW, negW) := deduped.foldl (fun (acc : Float × Float) a =>
    let w := atomWeight a
    match a.direction with
    | .supports    => (acc.1 + w, acc.2)
    | .contradicts => (acc.1, acc.2 + w)) (0.0, 0.0)
  let alpha := alpha0 + posW
  let beta_ := beta0 + negW
  { decisionId             := decisionId
  , alpha                  := alpha
  , beta                   := beta_
  , posteriorMean          := if alpha + beta_ > 0 then alpha / (alpha + beta_) else 0.0
  , assuranceLower95       := wilsonLower95 alpha beta_
  , evidenceCompleteness   := completeness
  , contradictionMass      := negW }

/-! ## Thresholds

These govern automatic state transitions:
- ≥ autoApply: eligible for auto-application (if review quorum met)
- ≥ holdForReview: hold for additional reviewer
- < holdForReview: remain logged/deferred -/

def autoApplyThreshold : Float := 0.98
def holdForReviewThreshold : Float := 0.93

/-! ## Binary Evidence Counts (Nat-valued)

Nat-valued evidence pairs for kernel-checkable arithmetic. The contribution
IS the pseudo-count (Morita et al. 2008): ESS = pos + neg. -/

structure BinEvNat where
  pos : Nat
  neg : Nat
  deriving DecidableEq, BEq, Repr

instance : Add BinEvNat := ⟨fun a b => ⟨a.pos + b.pos, a.neg + b.neg⟩⟩
instance : Zero BinEvNat := ⟨⟨0, 0⟩⟩

@[ext] theorem BinEvNat.ext {a b : BinEvNat} (hp : a.pos = b.pos) (hn : a.neg = b.neg) :
    a = b := by cases a; cases b; simp_all

instance : AddCommMonoid BinEvNat where
  add_assoc a b c := BinEvNat.ext (Nat.add_assoc ..) (Nat.add_assoc ..)
  zero_add a := BinEvNat.ext (Nat.zero_add ..) (Nat.zero_add ..)
  add_zero a := BinEvNat.ext (Nat.add_zero ..) (Nat.add_zero ..)
  add_comm a b := BinEvNat.ext (Nat.add_comm ..) (Nat.add_comm ..)
  nsmul := nsmulRec

def BinEvNat.ess (e : BinEvNat) : Nat := e.pos + e.neg

/-! ## Evidence Envelope — Epistemic Assessment Layer

The core `EvidenceAtom` records *what* was observed. The `EvidenceEnvelope`
wraps an atom with epistemic metadata: *what kind* of evidence it is and
*how much* pseudo-count backing it has.

This separates observation from assessment (O'Hagan 2019, Morita et al. 2008).
The envelope is an optional enrichment — existing atoms work without it.

The `contribution` field IS the evidence (Skilling/Goertzel): a "strong against"
judgment with ESS=3 is `⟨0, 3⟩`. Mixed evidence like "partially supports" is
`⟨1, 2⟩`. The ESS is `contribution.pos + contribution.neg` (derived, not stored). -/

open Mettapedia.Logic in
structure EvidenceEnvelope where
  atom : EvidenceAtom
  kind : EvidenceKind
  contribution : BinEvNat          -- the pseudo-count IS the evidence
  derivedFrom : List String := []  -- lightweight provenance: source atom IDs
  deriving Repr

end Mettapedia.Languages.GF.SUMO.EvidenceModel
