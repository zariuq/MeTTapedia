import Mettapedia.Logic.LP.PathMapBridge
import Mettapedia.OSLF.PathMap.WorldModelBridge
import Mettapedia.OSLF.PathMap.PLNBridge

/-!
# LP ↔ WorldModel Bridge

Port of `Mettapedia.Logic.Datalog.WorldModelBridge` onto LP types.

Connects the LP least Herbrand model to the `WorldModel` / `multisetPathEvidence`
infrastructure from `OSLF/PathMap/WorldModelBridge.lean`.

Evidence for a conjunctive query `q : Finset (GroundAtom σ)` against the least model is:

    ⟨|leastHerbrandModelFin kb ∩ q|, |leastHerbrandModelFin kb \ q|⟩

## Key theorems

- `lpLeastModelEvidence` — `multisetPathEvidence` on `leastHerbrandModelFin`
  agrees with `finsetPathEvidence`
- `lpEvidence_monotone` — larger knowledge base ⇒ more positive evidence
- `lpEDB_posEvidence` — a non-empty EDB fact in the query yields pos > 0
-/

namespace Mettapedia.Logic.LP

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.OSLF.PathMap.WorldModelBridge
open Mettapedia.OSLF.PathMap.PLNBridge

variable {σ : LPSignature} [IsEmpty σ.functionSymbols]

/-! ## Section 1: LP model as a WorldModel store -/

/-- The multiset evidence for a query against the least Herbrand model. -/
noncomputable def lpModelEvidence
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (q : Finset (GroundAtom σ)) : Evidence :=
  multisetPathEvidence (leastHerbrandModelFin kb).val q

/-! ## Section 2: Agreement with finsetPathEvidence -/

/-- The multiset evidence of `leastHerbrandModelFin` equals the finset-based evidence. -/
theorem lpLeastModelEvidence
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (q : Finset (GroundAtom σ)) :
    lpModelEvidence kb q = finsetPathEvidence (leastHerbrandModelFin kb) q :=
  finset_multiset_evidence_agree (leastHerbrandModelFin kb) q

/-! ## Section 3: Monotonicity of evidence -/

/-- A larger knowledge base yields more positive evidence. -/
theorem lpEvidence_monotone
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb₁ kb₂ : KnowledgeBase σ)
    (h_db : kb₁.db ⊆ kb₂.db)
    (h_prog : ∀ r ∈ kb₁.prog, r ∈ kb₂.prog)
    (q : Finset (GroundAtom σ)) :
    (lpModelEvidence kb₁ q).pos ≤ (lpModelEvidence kb₂ q).pos := by
  simp only [lpModelEvidence, multisetPathEvidence]
  norm_cast
  apply Multiset.card_le_card
  apply Multiset.filter_le_filter
  rw [Finset.val_le_iff_val_subset]
  intro a ha
  simp only [Finset.mem_val] at ha ⊢
  rw [mem_leastHerbrandModelFin_iff] at ha ⊢
  exact leastHerbrandModel_monotone_in_rules kb₁ kb₂ h_db h_prog ha

/-! ## Section 4: Non-zero evidence from EDB facts -/

/-- If an EDB fact `a` is in the query `q`, then the leastHerbrandModel has
    positive evidence for `q`. -/
theorem lpEDB_posEvidence
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (a : GroundAtom σ) (ha_db : a ∈ kb.db)
    (q : Finset (GroundAtom σ)) (ha_q : a ∈ q) :
    0 < (lpModelEvidence kb q).pos := by
  simp only [lpModelEvidence, multisetPathEvidence]
  norm_cast
  rw [Multiset.card_pos_iff_exists_mem]
  exact ⟨a, by simp only [Multiset.mem_filter, Finset.mem_val];
               exact ⟨(mem_leastHerbrandModelFin_iff kb a).mpr
                       (leastHerbrandModel_db kb a ha_db), ha_q⟩⟩

end Mettapedia.Logic.LP
