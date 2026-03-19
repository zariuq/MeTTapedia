import Mettapedia.Logic.BinEvNat
import Mettapedia.Logic.EvidenceKind
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.BinaryEvidence

/-!
# Evidential Ledger — Generic Evidence Aggregation Framework

A domain-independent framework for multi-source evidence aggregation with
compositionality, source forgetting, and AdditiveWorldModel integration.

## Architecture (GPT-5.4 Pro / council consensus)

**Additive WM is the base evidence-composition layer.**
It is not supposed to encode every aspect of trust, dependence, or governance
by itself. Source reliability, dependence management, and governance policy
sit above it as extension layers.

## Pipeline

    List (SourceItem Source Candidate)     -- typed evidence ledger
      → aggregate items candidate          -- fold support vectors (hplus)
        → toState items                    -- embed as world-model state
          → toState_append                 -- compositionality law
            → forget source items          -- sensitivity via list filter

## References

- O'Hagan 2019: expert elicitation (SHELF framework)
- Morita et al. 2008: effective sample size = pos + neg
- Green et al. 2007: provenance semirings
- Sutton & Abrams 2001: Bayesian evidence synthesis
-/

namespace Mettapedia.Logic.EvidentialLedger

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. Source items: one per source, vector over all candidates -/

/-- A single evidence source contributing a support vector over all candidates.
    Each source says something about EVERY candidate simultaneously —
    splitting into per-candidate records would pretend correlated judgments
    are independent. -/
structure SourceItem (Source Candidate : Type*) where
  source : Source
  kind : EvidenceKind
  support : Candidate → BinEvNat
  note : String

/-! ## 2. Aggregation: fold support vectors by candidate -/

/-- Aggregate evidence from a ledger for a given candidate.
    This IS the hplus aggregation — independent sources contribute additively.
    The fold is the explicit, auditable aggregation policy. -/
def aggregate [BEq Candidate] (items : List (SourceItem Source Candidate))
    (c : Candidate) : BinEvNat :=
  (items.map (fun item => item.support c)).foldl (· + ·) 0

/-! ## 3. Generic source forgetting -/

/-- Remove all evidence from a given source. Sensitivity analysis is then
    `aggregate (forget s ledger) c` — a one-liner for any source. -/
def forget [DecidableEq Source] (s : Source)
    (items : List (SourceItem Source Candidate)) : List (SourceItem Source Candidate) :=
  items.filter (fun item => !decide (item.source = s))

/-! ## 4. World-model integration -/

instance : EvidenceType BinEvNat := {}
instance (Candidate : Type*) : EvidenceType (Candidate → BinEvNat) := {}

/-- The state is `Candidate → BinEvNat`: a function from queries to evidence.
    Pi types get `AddCommMonoid` for free, so `extract_add` is `rfl`. -/
noncomputable instance (Candidate : Type*) :
    AdditiveWorldModel (Candidate → BinEvNat) Candidate BinEvNat where
  extract state c := state c
  extract_add _ _ _ := rfl

/-- Embed a ledger into a world-model state. -/
def toState [BEq Candidate] (items : List (SourceItem Source Candidate)) :
    Candidate → BinEvNat :=
  fun c => aggregate items c

/-! ## 5. Compositionality -/

/-- Accumulator shift for BinEvNat foldl. -/
private theorem foldl_add_acc (l : List BinEvNat) (init : BinEvNat) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih, ih (init := hd)]
    exact add_assoc init hd _

/-- Evidence from two groups of sources combines additively in the state.
    This is the compositionality property that makes WM-PLN non-ad-hoc:
    you can reason about subsets without recomputing from scratch. -/
theorem toState_append [BEq Candidate] (l₁ l₂ : List (SourceItem Source Candidate)) :
    toState (l₁ ++ l₂) = fun c => toState l₁ c + toState l₂ c := by
  funext c; simp only [toState, aggregate, List.map_append, List.foldl_append]
  exact foldl_add_acc _ _

/-! ## 6. Weighted aggregation (Layer 2 extension)

Reliability-weighted evidence synthesis: each source's contribution is
scaled by an integer weight before aggregation. Higher weight = more
trusted source. Uses Nat (not Float) per Codex/council consensus. -/

/-- A weighted evidence source: the base SourceItem plus a reliability weight. -/
structure WeightedSourceItem (Source Candidate : Type*) extends SourceItem Source Candidate where
  weight : Nat

/-- Scale a BinEvNat by a Nat weight. -/
def BinEvNat.scale (w : Nat) (e : BinEvNat) : BinEvNat := ⟨w * e.pos, w * e.neg⟩

/-- Weighted aggregation: each source's contribution scaled by its weight. -/
def weightedAggregate [BEq Candidate] (items : List (WeightedSourceItem Source Candidate))
    (c : Candidate) : BinEvNat :=
  (items.map (fun item => BinEvNat.scale item.weight (item.toSourceItem.support c))).foldl (· + ·) 0

/-- Weighted embedding into world-model state. -/
def weightedToState [BEq Candidate] (items : List (WeightedSourceItem Source Candidate)) :
    Candidate → BinEvNat :=
  fun c => weightedAggregate items c

/-- Forget a source from a weighted ledger. -/
def weightedForget [DecidableEq Source] (s : Source)
    (items : List (WeightedSourceItem Source Candidate)) :
    List (WeightedSourceItem Source Candidate) :=
  items.filter (fun item => !decide (item.toSourceItem.source = s))

/-- Weighted compositionality: evidence from two weighted source groups
    combines additively. Same algebraic structure as unweighted case. -/
theorem weightedToState_append [BEq Candidate]
    (l₁ l₂ : List (WeightedSourceItem Source Candidate)) :
    weightedToState (l₁ ++ l₂) = fun c => weightedToState l₁ c + weightedToState l₂ c := by
  funext c; simp only [weightedToState, weightedAggregate, List.map_append, List.foldl_append]
  exact foldl_add_acc _ _

/-! ## 7. Data-backed state: raw observations alongside compressed statistics

The sufficient statistic is a lossy compression of the raw data. Keeping both
lets you switch models without re-collecting data. The key property: compression
is a monoid homomorphism from `(List Bool, ++)` to `(BinEvNat, +)`.

Connection to Goertzel's factor-graph paper (§5.7): STV → DTV embedding is
exactly this compression — the STV is the compressed view, the DTV/histogram
is the richer carrier that preserves the distribution shape. -/

/-- Compress a list of binary observations into a BinEvNat pseudo-count. -/
def compress (obs : List Bool) : BinEvNat :=
  ⟨obs.countP id, obs.countP (!·)⟩

/-- Compression is a monoid homomorphism: appending observations = adding counts. -/
theorem compress_append (l₁ l₂ : List Bool) :
    compress (l₁ ++ l₂) = compress l₁ + compress l₂ := by
  simp only [compress, List.countP_append]
  exact BinEvNat.ext rfl rfl

/-- A data-backed evidence state: raw observations + compressed summary + consistency. -/
structure DataBackedState where
  raw : List Bool
  compressed : BinEvNat
  consistent : compressed = compress raw

/-- Revision of data-backed states: append data, recompress. -/
def DataBackedState.revise (s₁ s₂ : DataBackedState) : DataBackedState where
  raw := s₁.raw ++ s₂.raw
  compressed := s₁.compressed + s₂.compressed
  consistent := by rw [s₁.consistent, s₂.consistent, compress_append]

/-- Data-backed revision is additive in the compressed component. -/
theorem DataBackedState.revise_compressed (s₁ s₂ : DataBackedState) :
    (s₁.revise s₂).compressed = s₁.compressed + s₂.compressed := rfl

/-! ## 8. Bridge to formal BinaryEvidence (ℝ≥0∞) -/

noncomputable def BinEvNat.toBinaryEvidence (e : BinEvNat) :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence :=
  ⟨↑e.pos, ↑e.neg⟩

end Mettapedia.Logic.EvidentialLedger
