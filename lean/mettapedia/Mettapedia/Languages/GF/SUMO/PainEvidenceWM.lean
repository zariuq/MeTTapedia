import Mettapedia.Logic.EvidentialLedger
import Mettapedia.Languages.GF.SUMO.EvidenceModel
import Provenance.Semirings.Which

/-!
# WM-PLN Evidence Analysis: Pain Reclassification

Evidence-driven ontology repair using the generic `EvidentialLedger` framework.
This file instantiates the framework with concrete SUMO Pain data and
kernel-checks the ranking, sensitivity, and compositionality properties.

The generic framework (`EvidentialLedger.lean`) provides:
- `SourceItem` parameterized by source/candidate type
- `aggregate` fold, `forget` filter, `toState` embedding
- `toState_append` compositionality theorem
- `AdditiveWorldModel` instance

This file provides:
- 7 concrete source items (IASP, Stanford SEP, SNOMED, SUMO axiom, etc.)
- Kernel-checked totals, ranking, and sensitivity analysis
- Policy-vs-evidence separation (epistemic winner ≠ shipped choice)

## References

- SumoNTT.lean: Decision 1 informal evidence analysis
- RepairLog.lean: RepairDecision record for Pain
- O'Hagan 2019, Morita et al. 2008 (evidence methodology)
-/

namespace Mettapedia.Languages.GF.SUMO.PainEvidenceWM

open Mettapedia.Logic
open Mettapedia.Logic.EvidentialLedger

/-! ## 1. Sources and candidates -/

inductive PainSource
  | iasp | stanfordSEP | snomedCT | sumoAxiom | sumoProcess | enacheGF | wikipedia
  deriving DecidableEq, BEq, Repr

inductive PainCandidate
  | pathologicProcess | emotionalState | stateOfMind | split
  deriving DecidableEq, BEq, Repr

/-! ## 2. Evidence ledger: 7 source items

Each source contributes a `PainCandidate → BinEvNat` support vector.
Pseudo-counts encode strength and direction:
  strong-for = ⟨3,0⟩, moderate-against = ⟨0,2⟩, mixed = ⟨1,2⟩, no opinion = ⟨0,0⟩. -/

def painEvidence : List (SourceItem PainSource PainCandidate) := [
  { source := .iasp, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩
      | .emotionalState    => ⟨1, 2⟩
      | .stateOfMind       => ⟨3, 0⟩
      | .split             => ⟨2, 0⟩,
    note := "IASP 2020: 'unpleasant sensory and emotional experience'" },
  { source := .stanfordSEP, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩
      | .emotionalState    => ⟨0, 0⟩
      | .stateOfMind       => ⟨3, 0⟩
      | .split             => ⟨2, 0⟩,
    note := "Stanford Encyclopedia of Philosophy: pain as mental state" },
  { source := .snomedCT, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩
      | .emotionalState    => ⟨1, 1⟩
      | .stateOfMind       => ⟨2, 0⟩
      | .split             => ⟨0, 2⟩,
    note := "SNOMED Clinical Terms: Pain as Finding, not Process" },
  { source := .sumoAxiom, kind := .empirical,
    support := fun
      | .pathologicProcess => ⟨0, 3⟩
      | .emotionalState    => ⟨3, 0⟩
      | .stateOfMind       => ⟨3, 0⟩
      | .split             => ⟨0, 0⟩,
    note := "SUMO axiom: (contraryAttribute Pleasure Pain) demands Attribute" },
  { source := .sumoProcess, kind := .empirical,
    support := fun
      | .pathologicProcess => ⟨2, 0⟩
      | .emotionalState    => ⟨0, 0⟩
      | .stateOfMind       => ⟨0, 1⟩
      | .split             => ⟨2, 0⟩,
    note := "5 SUMO axioms use Pain in process-like contexts" },
  { source := .enacheGF, kind := .expertElicited,
    support := fun
      | .pathologicProcess => ⟨0, 2⟩
      | .emotionalState    => ⟨3, 0⟩
      | .stateOfMind       => ⟨0, 0⟩
      | .split             => ⟨0, 2⟩,
    note := "Enache 2010 GF grammar: Pain under EmotionalState (silent repair)" },
  { source := .wikipedia, kind := .textInterpreted,
    support := fun
      | .pathologicProcess => ⟨0, 2⟩
      | .emotionalState    => ⟨2, 0⟩
      | .stateOfMind       => ⟨1, 0⟩
      | .split             => ⟨0, 0⟩,
    note := "Wikipedia: 'distressing feeling associated with tissue damage'" }
]

/-! ## 3. Kernel-checked evidence computation -/

theorem pathologic_total :
    aggregate painEvidence .pathologicProcess = ⟨2, 16⟩ := by decide
theorem emotional_total :
    aggregate painEvidence .emotionalState = ⟨10, 3⟩ := by decide
theorem stateofmind_total :
    aggregate painEvidence .stateOfMind = ⟨12, 1⟩ := by decide
theorem split_total :
    aggregate painEvidence .split = ⟨6, 4⟩ := by decide

/-! ## 4. Ranking -/

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

/-! ## 5. Sensitivity: Wikipedia removal preserves ranking -/

theorem ranking_preserved_noWiki :
    let l := forget .wikipedia painEvidence
    let pp := aggregate l .pathologicProcess
    let sm := aggregate l .stateOfMind
    let em := aggregate l .emotionalState
    let sp := aggregate l .split
    pp.neg > pp.pos ∧
    sm.pos * (em.pos + em.neg) > em.pos * (sm.pos + sm.neg) ∧
    em.pos * (sp.pos + sp.neg) > sp.pos * (em.pos + em.neg) := by decide

/-! ## 6. Sensitivity: IASP removal breaks the tie -/

theorem iasp_is_critical_discriminator :
    let l := forget .iasp painEvidence
    aggregate l .stateOfMind = aggregate l .emotionalState := by decide

/-! ## 7. Provenance tracking with Which semiring -/

abbrev W := Which PainSource

def sourcesFor (items : List (SourceItem PainSource PainCandidate))
    (c : PainCandidate) : W :=
  items.foldl (fun acc item =>
    if (item.support c).pos + (item.support c).neg > 0
    then acc + Which.wset {item.source}
    else acc) 0

/-! ## 8. Policy vs evidence separation

The evidence says StateOfMind (12,1). We shipped EmotionalState (10,3).

These are different questions:
- "What does the evidence support?" → StateOfMind (computed above, kernel-checked)
- "What did we ship?" → EmotionalState (operational choice)

The gap is operational, not epistemic:
1. Phase 1 fixes type errors only; broader reclassification deferred to Phase 2
2. EmotionalState matches Enache's prior repair (conservative consistency)
3. StateOfMind reclassification would require Adam Pease's approval for official SUMO
4. Margin between StateOfMind (12,1) and EmotionalState (10,3) is narrow enough to defer

Per GPT-5.4 Pro: "If your conservative choice is about safe deployment
rather than truth, it belongs in the action policy, not in the evidence counts." -/

/-! ## 9. End-to-end summary -/

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

end Mettapedia.Languages.GF.SUMO.PainEvidenceWM
