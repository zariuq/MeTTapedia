import Mettapedia.Logic.MarkovDeFinettiCarrierTransport
import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

/-! LLM primer:
- Adjacent carrier transport = queue transposition for a single state.
- We use this + existing Level 2→3 chain to get per-row perm invariance.
- Namespace qualification: `CarrierSuffHyp` lives in `CarrierTransportBridge`,
  `MarkovExchangeablePrefixMeasure` in `MarkovExchangeabilityBridge`,
  `cylinder` in `MarkovDeFinettiRecurrence`.

# Per-Row Exchangeability from Carrier Transport
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovExchangeability
open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open MarkovDeFinettiCarrierTransport
open CarrierTransportBridge
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open MeasureTheory
open Finset

variable {k : ℕ}

namespace PerRowPE

/-! ## Section 1: Out-visit counting -/

def outVisitCount {N : ℕ} (xs : Fin (N + 1) → Fin k) (i : Fin k) : ℕ :=
  ((univ : Finset (Fin N)).filter (fun t => xs (Fin.castSucc t) = i)).card

lemma sum_outVisitCount_eq {N : ℕ} (xs : Fin (N + 1) → Fin k) :
    ∑ i : Fin k, outVisitCount xs i = N := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset (Fin N)) (univ : Finset (Fin k))
    (fun t => xs (Fin.castSucc t))
  simp only [Finset.mem_univ, forall_const, Finset.filter_True] at h
  simpa [Finset.card_univ, Fintype.card_fin] using h

/-! ## Section 2: 1D start-restricted perm invariance from carrier transport -/

/-- 1D start-restricted perm invariance instantiated from carrier transport. -/
theorem startRestricted_rowSucc_permInvariant
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder xs))
    (hSuff : ∀ (i b : Fin k) (N : ℕ), Mettapedia.Logic.CarrierTransportBridge.CarrierSuffHyp i b N)
    (i a b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (hbi : b ≠ i) :
    P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i (σ n) b) =
    P ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) i n b) := by
  apply startRestrictedRowSuccessorPermInvariant_offDiagonal_of_extension_transport
    (k := k) μ hμ P hExt
  · intro i' b' n' n'' N' hbi'
    exact Mettapedia.Logic.CarrierTransportBridge.carrierTransportEquivGeneral i' b' hbi' n' n'' (hSuff i' b' N')
  · exact hbi

/-! ## Section 3: Unrestricted 1D perm invariance -/

/-- Unrestricted 1D: sum over start states removes the start restriction. -/
theorem rowSucc_permInvariant
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (MarkovDeFinettiRecurrence.cylinder xs))
    (hSuff : ∀ (i b : Fin k) (N : ℕ), Mettapedia.Logic.CarrierTransportBridge.CarrierSuffHyp i b N)
    (i b : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (hbi : b ≠ i) :
    P (rowSuccessorValueEvent (k := k) i (σ n) b) =
    P (rowSuccessorValueEvent (k := k) i n b) := by
  have hleft := sum_start_inter_eq_measure (k := k) P
    (rowSuccessorValueEvent (k := k) i (σ n) b)
  have hright := sum_start_inter_eq_measure (k := k) P
    (rowSuccessorValueEvent (k := k) i n b)
  rw [← hleft, ← hright]
  congr 1; funext a
  exact startRestricted_rowSucc_permInvariant μ hμ P hExt hSuff i a b σ n hbi

end PerRowPE

end Mettapedia.Logic
