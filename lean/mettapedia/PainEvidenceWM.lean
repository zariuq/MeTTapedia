import Mettapedia.Languages.GF.SUMO.EvidenceModel
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.BinaryEvidence
import Provenance.Semirings.Which

/-!
# WM-PLN Evidence Analysis: Pain Reclassification

Evidence-driven ontology repair PoC using the vector-per-source model recommended
by the expert elicitation literature (O'Hagan 2019, SHELF/Dirichlet).

## Pipeline

    7 SourceItems (one per source, each with support vector over 4 candidates)
      → aggregate : List SourceItem → PainCandidate → BinEvNat   (fold)
        → ranking theorems                                        (by decide)
          → forget : PainSource → List SourceItem → List SourceItem  (filter)
            → sensitivity theorems                                (by decide)

## Key design decision

Each source contributes a support vector over ALL candidates simultaneously.
IASP's "unpleasant sensory and emotional experience" is evidence against
PathologicProcess AND for StateOfMind AND weakly for EmotionalState — at once.
Splitting into separate per-candidate records would pretend these are independent
observations. They are not.

## References

- O'Hagan 2019: expert elicitation methodology (SHELF framework)
- Morita et al. 2008: effective sample size = pos + neg (the contribution IS the ESS)
- Green et al. 2007: provenance semirings (Which tracks source identity)
- SumoNTT.lean: Decision 1 informal evidence analysis
- RepairLog.lean: RepairDecision record for Pain
-/

namespace Mettapedia.Languages.GF.SUMO.PainEvidenceWM

open Mettapedia.Logic
open Mettapedia.Languages.GF.SUMO.EvidenceModel

/-! ## 1. Sources and candidates -/

inductive PainSource
  | iasp | stanfordSEP | snomedCT | sumoAxiom | sumoProcess | enacheGF | wikipedia
  deriving DecidableEq, BEq, Repr

inductive PainCandidate
  | pathologicProcess | emotionalState | stateOfMind | split
  deriving DecidableEq, BEq, Repr

/-! ## 2. Source items: one per source, vector over all candidates

Each source contributes a `PainCandidate → BinEvNat` support vector.
The pseudo-counts encode both direction and strength:
  strong-for = ⟨3,0⟩, moderate-against = ⟨0,2⟩, mixed = ⟨1,2⟩, no opinion = ⟨0,0⟩.
The ESS of each item for a candidate is pos + neg (Morita et al. 2008). -/

structure SourceItem where
  source : PainSource
  kind : EvidenceKind
  support : PainCandidate → BinEvNat
  note : String

def painEvidence : List SourceItem := [
  { source := .iasp, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩  -- strong against: "experience" ≠ process
      | .emotionalState    => ⟨1, 2⟩  -- weak for: "emotional" but misses sensory
      | .stateOfMind       => ⟨3, 0⟩  -- strong for: "psychological state"
      | .split             => ⟨2, 0⟩, -- moderate for: captures both aspects
    note := "IASP 2020: 'unpleasant sensory and emotional experience'" },
  { source := .stanfordSEP, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩  -- strong against: "pain as quale/mental state"
      | .emotionalState    => ⟨0, 0⟩  -- no direct opinion
      | .stateOfMind       => ⟨3, 0⟩  -- strong for: "mental state" analysis
      | .split             => ⟨2, 0⟩, -- moderate for: philosophically clean
    note := "Stanford Encyclopedia of Philosophy: pain as mental state" },
  { source := .snomedCT, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩  -- strong against: classifies as Finding
      | .emotionalState    => ⟨1, 1⟩  -- mixed: some emotional codes
      | .stateOfMind       => ⟨2, 0⟩  -- moderate for: broader coverage
      | .split             => ⟨0, 2⟩, -- moderate against: over-engineers
    note := "SNOMED Clinical Terms: Pain as Finding, not Process" },
  { source := .sumoAxiom, kind := .empirical,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩  -- strong against: contraryAttribute needs Attribute
      | .emotionalState    => ⟨3, 0⟩  -- strong for: matches Pleasure's class
      | .stateOfMind       => ⟨3, 0⟩  -- strong for: type-checks (subclass Attribute)
      | .split             => ⟨0, 0⟩, -- no direct opinion
    note := "SUMO axiom: (contraryAttribute Pleasure Pain) demands Attribute" },
  { source := .sumoProcess, kind := .empirical,
    support := fun
      | .pathologicProcess => ⟨2, 0⟩  -- moderate for: 5 process-like axiom usages
      | .emotionalState    => ⟨0, 0⟩  -- no opinion
      | .stateOfMind       => ⟨0, 1⟩  -- weak against: process axioms don't fit
      | .split             => ⟨2, 0⟩, -- moderate for: preserves process axioms
    note := "5 SUMO axioms use Pain in process-like contexts" },
  { source := .enacheGF, kind := .expertElicited,
    support := fun
      | .pathologicProcess => ⟨0, 2⟩  -- moderate against: Enache moved it away
      | .emotionalState    => ⟨3, 0⟩  -- strong for: GF grammar has this
      | .stateOfMind       => ⟨0, 0⟩  -- no opinion
      | .split             => ⟨0, 2⟩, -- moderate against: not what Enache did
    note := "Enache 2010 GF grammar: Pain under EmotionalState (silent repair)" },
  { source := .wikipedia, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 2⟩  -- moderate against: "distressing feeling"
      | .emotionalState    => ⟨2, 0⟩  -- moderate for: "feeling" → emotion
      | .stateOfMind       => ⟨1, 0⟩  -- weak for: compatible but vague
      | .split             => ⟨0, 0⟩, -- no opinion
    note := "Wikipedia: 'distressing feeling associated with tissue damage'" }
]

/-! ## 3. Aggregation: fold support vectors by candidate

Council quorum (Goertzel/Carneiro/Hutter): This IS hplus — independent sources
contribute additively. The `support c` projection is the categorical-to-binary
derivation GPT-5.4 Pro recommended. The fold is the explicit, auditable policy. -/

def aggregate (items : List SourceItem) (c : PainCandidate) : BinEvNat :=
  (items.map (fun item => item.support c)).foldl (· + ·) 0

def strength (e : BinEvNat) : Nat × Nat := (e.pos, e.pos + e.neg)

/-! ## 4. Kernel-checked evidence computation

Council quorum (Knuth/Buzzard): The totals are the contract. If the fold produces
the same values as the previous hand-written version, the refactor is correct. -/

theorem pathologic_total :
    aggregate painEvidence .pathologicProcess = ⟨2, 16⟩ := by decide
theorem emotional_total :
    aggregate painEvidence .emotionalState = ⟨10, 3⟩ := by decide
theorem stateofmind_total :
    aggregate painEvidence .stateOfMind = ⟨12, 1⟩ := by decide
theorem split_total :
    aggregate painEvidence .split = ⟨6, 4⟩ := by decide

/-! ## 5. Ranking from evidence algebra

Council quorum (Tao): Cross-multiplication avoids division. The ranking emerges:
StateOfMind > EmotionalState > Split >> PathologicProcess. -/

theorem pathologic_refuted :
    (aggregate painEvidence .pathologicProcess).neg >
    (aggregate painEvidence .pathologicProcess).pos := by decide

theorem stateofmind_beats_emotional :
    let sm := aggregate painEvidence .stateOfMind
    let em := aggregate painEvidence .emotionalState
    sm.pos * (em.pos + em.neg) > em.pos * (sm.pos + sm.neg) := by decide

theorem emotional_beats_split :
    let em := aggregate painEvidence .emotionalState
    let sp := aggregate painEvidence .split
    em.pos * (sp.pos + sp.neg) > sp.pos * (em.pos + em.neg) := by decide

/-! ## 6. Generic source forgetting

Council quorum (Kwiatkowska/Dragan): "What if we lose this source?" is a list
filter. No hand-written per-source defs — one generic function. -/

def forget (s : PainSource) (items : List SourceItem) : List SourceItem :=
  items.filter (fun item => !decide (item.source = s))

/-! ## 7. Sensitivity: Wikipedia removal preserves ranking

Wikipedia contributes weak/moderate evidence. Removing it does not change
the ranking — it was corroborative, not decisive. -/

theorem ranking_preserved_noWiki :
    let l := forget .wikipedia painEvidence
    let pp := aggregate l .pathologicProcess
    let sm := aggregate l .stateOfMind
    let em := aggregate l .emotionalState
    let sp := aggregate l .split
    pp.neg > pp.pos ∧
    sm.pos * (em.pos + em.neg) > em.pos * (sm.pos + sm.neg) ∧
    em.pos * (sp.pos + sp.neg) > sp.pos * (em.pos + em.neg) := by decide

/-! ## 8. Sensitivity: IASP removal breaks the tie

IASP is the critical discriminator. Without it, StateOfMind and EmotionalState
become tied — the evidence no longer distinguishes them. -/

theorem iasp_is_critical_discriminator :
    let l := forget .iasp painEvidence
    aggregate l .stateOfMind = aggregate l .emotionalState := by decide

/-! ## 9. Provenance tracking with Which semiring

The Which semiring tracks which sources contributed to each candidate's aggregate.
With the vector model, every source potentially contributes to every candidate
(with ⟨0,0⟩ for "no opinion"). The `forget` filter is the real sensitivity tool;
Which provides the compositional provenance label. -/

abbrev W := Which PainSource

def sourcesFor (items : List SourceItem) (c : PainCandidate) : W :=
  items.foldl (fun acc item =>
    if (item.support c).pos + (item.support c).neg > 0
    then acc + Which.wset {item.source}
    else acc) 0

/-! ## 10. Policy vs evidence separation

The evidence says StateOfMind (12,1). We shipped EmotionalState (10,3).

These are different questions:
- "What does the evidence support?" → StateOfMind (computed above, kernel-checked)
- "What did we ship?" → EmotionalState (operational choice)

The gap is operational, not epistemic:
1. Phase 1 fixes type errors only; broader reclassification deferred to Phase 2
2. EmotionalState matches Enache's prior repair (conservative consistency)
3. StateOfMind reclassification would require Adam Pease's approval for official SUMO
4. Margin between StateOfMind (12,1) and EmotionalState (10,3) is narrow enough to defer

Per GPT-5.4 Pro (line 606): "If your conservative choice is about safe deployment
rather than truth, it belongs in the action policy, not in the evidence counts."
The evidence counts above are clean — they reflect what the sources say, not what
we chose to ship. -/

/-! ## 11. End-to-end summary -/

theorem end_to_end :
    aggregate painEvidence .pathologicProcess = ⟨2, 16⟩ ∧
    aggregate painEvidence .emotionalState = ⟨10, 3⟩ ∧
    aggregate painEvidence .stateOfMind = ⟨12, 1⟩ ∧
    aggregate painEvidence .split = ⟨6, 4⟩ ∧
    (aggregate painEvidence .pathologicProcess).neg >
      (aggregate painEvidence .pathologicProcess).pos ∧
    (let l := forget .wikipedia painEvidence
     let sm := aggregate l .stateOfMind
     let em := aggregate l .emotionalState
     sm.pos * (em.pos + em.neg) > em.pos * (sm.pos + sm.neg)) ∧
    (let l := forget .iasp painEvidence
     aggregate l .stateOfMind = aggregate l .emotionalState) := by decide

/-! ## 12. AdditiveWorldModel instance

Council quorum (Goertzel/Buzzard/de Paiva): Without this, it's a spreadsheet.
WITH this, it's a WM-PLN evidence analysis.

The state is `PainCandidate → BinEvNat` — a function from queries to evidence.
This is exactly `KRelation` in the derivation tracking demo. Pi types get
`AddCommMonoid` for free, so `extract_add` is `rfl`. -/

section WorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

instance : EvidenceType BinEvNat := {}
instance : EvidenceType (PainCandidate → BinEvNat) := {}

abbrev EvidenceState := PainCandidate → BinEvNat

noncomputable instance : AdditiveWorldModel EvidenceState PainCandidate BinEvNat where
  extract state c := state c
  extract_add _ _ _ := rfl

/-- The embedding from evidence ledger to world-model state. -/
def toState (items : List SourceItem) : EvidenceState :=
  fun c => aggregate items c

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
theorem toState_append (l₁ l₂ : List SourceItem) :
    toState (l₁ ++ l₂) = fun c => toState l₁ c + toState l₂ c := by
  funext c; simp only [toState, aggregate, List.map_append, List.foldl_append]
  exact foldl_add_acc _ _

/-- The abstract `extract` IS the concrete `aggregate`. -/
theorem extract_eq_aggregate (c : PainCandidate) :
    (toState painEvidence) c = aggregate painEvidence c := rfl

end WorldModel

/-! ## 13. Bridge to formal BinaryEvidence (ℝ≥0∞)

Council quorum (Skilling/Carneiro): The Nat computation is the SAME evidence
as the ℝ≥0∞ theory. The bridge makes that explicit. -/

noncomputable def BinEvNat.toBinaryEvidence (e : BinEvNat) :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence :=
  ⟨↑e.pos, ↑e.neg⟩

end Mettapedia.Languages.GF.SUMO.PainEvidenceWM
