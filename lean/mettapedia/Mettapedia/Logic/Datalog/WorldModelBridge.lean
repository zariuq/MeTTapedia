import Mettapedia.Logic.Datalog.PathMapBridge
import Mettapedia.OSLF.PathMap.WorldModelBridge
import Mettapedia.OSLF.PathMap.PLNBridge

/-!
# Datalog ↔ WorldModel Bridge

This module connects the Datalog least Herbrand model to the `WorldModel` / `multisetPathEvidence`
infrastructure from `OSLF/PathMap/WorldModelBridge.lean`.

## Core idea

The least Herbrand model `leastModelFin kb : Finset (GroundAtom τ)` is a finite relational
store.  Via the embedding `Finset.val : Finset α → Multiset α`, it plugs directly into
`multisetPathWorldModel` to give a `WorldModel (Multiset (GroundAtom τ)) (Finset (GroundAtom τ))`.

Evidence for a conjunctive query `q : Finset (GroundAtom τ)` against the least model is:

    ⟨|leastModelFin kb ∩ q|, |leastModelFin kb \ q|⟩

## Key theorems

- `datalogLeastModelEvidence` — `multisetPathEvidence` on `leastModelFin`
  agrees with `finsetPathEvidence` (specialization of `finset_multiset_evidence_agree`)
- `datalogEvidence_monotone` — larger knowledge base ⇒ more positive evidence
- `datalogEDB_posEvidence` — a non-empty EDB fact set with matching query yields pos > 0
-/

namespace Mettapedia.Logic.Datalog

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.PathMap.WorldModelBridge
open Mettapedia.OSLF.PathMap.PLNBridge

/-! ## Section 1: Datalog model as a WorldModel store -/

/-- The multiset evidence for a query against the least Herbrand model.

    This is the primary bridge: the finite Datalog model, viewed as a `Multiset`
    store, provides evidence via the `multisetPathWorldModel` instance. -/
noncomputable def datalogModelEvidence {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) (q : Finset (GroundAtom τ)) : Evidence :=
  multisetPathEvidence (leastModelFin kb).val q

/-! ## Section 2: Agreement with finsetPathEvidence -/

/-- The multiset evidence of `leastModelFin` equals the finset-based evidence.

    Corollary of `finset_multiset_evidence_agree` with `W = leastModelFin kb`. -/
theorem datalogLeastModelEvidence {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) (q : Finset (GroundAtom τ)) :
    datalogModelEvidence kb q = finsetPathEvidence (leastModelFin kb) q :=
  finset_multiset_evidence_agree (leastModelFin kb) q

/-! ## Section 3: Monotonicity of evidence -/

/-- A larger knowledge base yields a larger (or equal) leastModel, hence more positive evidence.

    Monotonicity chain:
    1. `leastModel_monotone_in_rules` → `leastModelFin kb₁ ⊆ leastModelFin kb₂`
    2. `Finset.inter_subset_inter_right` → `leastModelFin kb₁ ∩ q ⊆ leastModelFin kb₂ ∩ q`
    3. `Finset.card_le_card` → pos₁ ≤ pos₂ -/
theorem datalogEvidence_monotone {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb₁ kb₂ : KnowledgeBase τ)
    (h_db : kb₁.db ⊆ kb₂.db)
    (h_prog : ∀ r ∈ kb₁.prog, r ∈ kb₂.prog)
    (q : Finset (GroundAtom τ)) :
    (datalogModelEvidence kb₁ q).pos ≤ (datalogModelEvidence kb₂ q).pos := by
  simp only [datalogModelEvidence, multisetPathEvidence]
  -- goal: ↑card₁ ≤ ↑card₂ in ENNReal; reduce to ℕ inequality
  norm_cast
  apply Multiset.card_le_card
  apply Multiset.filter_le_filter
  -- goal: (leastModelFin kb₁).val ≤ (leastModelFin kb₂).val as multisets
  rw [Finset.val_le_iff_val_subset]
  intro a ha
  simp only [Finset.mem_val] at ha ⊢
  rw [mem_leastModelFin_iff] at ha ⊢
  exact leastModel_monotone_in_rules kb₁ kb₂ h_db h_prog ha

/-! ## Section 4: Non-zero evidence from EDB facts -/

/-- If an EDB fact `a` is in the query `q`, then the leastModel has positive evidence for `q`.

    Proof: `a ∈ leastModel kb` (by `leastModel_db`) → `a ∈ leastModelFin kb ∩ q` → card ≥ 1. -/
theorem datalogEDB_posEvidence {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) (a : GroundAtom τ) (ha_db : a ∈ kb.db)
    (q : Finset (GroundAtom τ)) (ha_q : a ∈ q) :
    0 < (datalogModelEvidence kb q).pos := by
  simp only [datalogModelEvidence, multisetPathEvidence]
  -- goal: (0 : ENNReal) < ↑(filter (· ∈ q) (leastModelFin kb).val).card
  norm_cast
  rw [Multiset.card_pos_iff_exists_mem]
  exact ⟨a, by simp only [Multiset.mem_filter, Finset.mem_val];
               exact ⟨(mem_leastModelFin_iff kb a).mpr (leastModel_db kb a ha_db), ha_q⟩⟩

end Mettapedia.Logic.Datalog
