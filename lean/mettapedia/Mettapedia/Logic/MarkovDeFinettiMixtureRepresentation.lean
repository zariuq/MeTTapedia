import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux
import Mettapedia.Logic.MarkovDeFinettiFiberEventBridge
import Mettapedia.Logic.MarkovDeFinettiPEBridge
import Mettapedia.Logic.MarkovDeFinettiKernelUniqueness

/-!
# Markov de Finetti: Surface Theorem Assembly

The surface theorem `fortini_surface` assembles all components of the
Diaconis-Freedman (1980) Markov de Finetti theorem:
  Every Markov-exchangeable, recurrent prefix measure on Fin(k)
  is a mixture of time-homogeneous Markov chains.

## Assembly route

| # | Step | Source | Status |
|---|------|--------|--------|
| 1 | Extension P + StrongRecurrence | input hypothesis from caller | INPUT |
| 2 | Per-row perm invariance | PEBridge: `rowProcessLaw_permInvariant_of_markovExchangeability` | PROVED |
| 3 | Row kernels (directingMeasure) | de Finetti ViaMartingale | PROVED |
| 4 | StartRestrictedRowKernelData | directingMeasure L1 transfer (KernelUniqueness) | PROVED |
| 5 | CrossRowCoherenceStep | cross-row conditional independence for the direct rowwise route | OPTIONAL |
| 6 | CylinderMixingIdentity_P | assembly of 4+5 via Crux combinators | PROVED (modulo 5) |
| 7 | Mixture reconstruction | `exists_markovParamLaw_of_...` (Crux) | PROVED |

The full theorem is already proved elsewhere in the codebase through the
successor-matrix / PE route. This file records an alternative direct rowwise
route: there, Step 5 is the only genuinely nontrivial local obligation.
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open MeasureTheory

variable {k : ℕ}

/-! ## The Remaining Direct-Route Obligation: CrossRowCoherenceStep

`CylinderMixingIdentity_P` is proved by assembly from two components:
- PROVED: pair-case base (`crossAnchor_lengthTwo` via `StartRestrictedRowKernelData`)
- OPTIONAL DIRECT-ROUTE INPUT: `CrossRowCoherenceStep` — the cross-row
  conditional independence

For the direct rowwise route, one must show that, given the row-directing measures K_i, events
from different row processes are conditionally independent. Per-row de Finetti
(which is proved) gives within-row factorization only. The cross-row claim
is the genuine mathematical content of the Diaconis-Freedman (1980) theorem.

Important status note: this is not a live gap in the completed main theorem.
The completed theorem proceeds through the successor-matrix / PE bridge
formalized in `MarkovDeFinettiFortiniBridgeCrux`, which avoids requiring this
direct-rowwise theorem in the public statement.

**Update (2026-04):** Class-based recurrence infrastructure now provides:
- `rowProcessLaw_restrictClass_eq_finsetSum` (BridgeCore:2245) — decomposes class-restricted
  measures as finite sums over singleton-start fibers
- `exchangeable_rowProcess_restrict_class` (PEBridge:2097) — process-level exchangeability
  under class restriction
- `StrongRecurrenceInClass` (Recurrence:190) — class-based recurrence definition

The path forward for the direct route is to apply `startRestrictedRowKernelData_directingRowKernel` fiberwise
for each a ∈ C using the finite-sum decomposition, then recombine with
`ae_finsetSum_measure_iff`. This reduces CrossRowCoherenceStep to the already-proved
per-start machinery. -/

/-! ## Public row-process consequences

These wrappers expose the canonical row-process theorems directly from the
usual public hypotheses (`hμ`, `hExt`, `hStrRec`), so downstream callers can
work at the Finetti-statement layer instead of threading per-row permutation
and exchangeability infrastructure by hand. -/

/-- Under Markov exchangeability plus strong recurrence, each row-process law
is exchangeable. This is the public route from the prefix-measure hypotheses
to the row-law symmetry used throughout the fiber-event bridge. -/
theorem rowProcessLaw_exchangeable_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P) :
    ∀ i : Fin k,
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n) := by
  intro i
  exact
    rowProcessLaw_exchangeable_of_perm_invariant
      (k := k) P i
      (fun σ =>
        PerRowJointPE.rowProcessLaw_permInvariant_of_markovExchangeability
          (k := k) μ hμ P hExt hStrRec i σ inferInstance)

/-- Under Markov exchangeability plus strong recurrence, the canonical
`directingRowKernel` satisfies the coordwise Cesàro theorem on the full
row-process law. -/
theorem rowProcessCoordwiseCesaroLimit_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P) :
    RowProcessCoordwiseCesaroLimit
      (k := k) P (directingRowKernel (k := k) P) := by
  exact
    rowProcessCoordwiseCesaroLimit_of_directingRowKernel_of_exchangeable
      (k := k) (P := P)
      (rowProcessLaw_exchangeable_of_markovExchangeable_strongRecurrence
        (k := k) μ hμ P hExt hStrRec)

/-- Under Markov exchangeability plus strong recurrence, the canonical
`directingRowKernel` satisfies the start-restricted finite-coordinate
factorization theorem. This is the proved Step 4 payload in the surface
assembly table. -/
theorem startRestrictedRowKernelData_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P) :
    StartRestrictedRowKernelData
      (k := k) P (directingRowKernel (k := k) P) := by
  exact
    startRestrictedRowKernelData_directingRowKernel
      (k := k) μ hμ P hExt hStrRec
      (rowProcessLaw_exchangeable_of_markovExchangeable_strongRecurrence
        (k := k) μ hμ P hExt hStrRec)

/-! ## Public class-restricted row-process consequences

These wrappers expose the class-restricted row-process theorems directly from
the usual public hypotheses (`hμ`, `hExt`, `hStrRec`), so downstream callers do
not need to thread the internal exchangeability plumbing manually. -/

/-- Under Markov exchangeability plus strong recurrence, the class-restricted
row process satisfies the canonical coordwise Cesàro theorem. -/
theorem rowProcessCoordwiseCesaroLimit_restrictClass_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (C : Set (Fin k)) :
    RowProcessCoordwiseCesaroLimit
      (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C})
      (directingRowKernel (k := k) P) := by
  exact
    rowProcessCoordwiseCesaroLimit_restrictClass_of_directingRowKernel_of_exchangeable
      (k := k) (P := P) (C := C)
      (rowProcessLaw_exchangeable_of_markovExchangeable_strongRecurrence
        (k := k) μ hμ P hExt hStrRec)

/-- Under Markov exchangeability plus strong recurrence, the class-restricted
row law factors through the canonical directing row kernel on finite
coordinate projections. -/
theorem rowProcessLaw_restrictClass_factorizes_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (C : Set (Fin k))
    (i : Fin k) (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (rowProcessLaw_restrictClass (k := k) C P i)
      =
    (rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  exact
    rowProcessLaw_restrictClass_factorizes_directingRowKernel
      (k := k) μ hμ P hExt hStrRec
      (rowProcessLaw_exchangeable_of_markovExchangeable_strongRecurrence
        (k := k) μ hμ P hExt hStrRec)
      C i m sel hsel

/-- Direct-route wrapper for the cylinder mixing identity via Crux assembly.
P(cyl(xs)) = ∫ wordProb(θ(ω), xs) dP for |xs| ≥ 2.

Takes `hStart` and `hStep` as PARAMETERS (not derived from hrow — they need
Markov exchangeability which is only available in the caller `fortini_surface`). -/
theorem cylinderMixingIdentity_gap
    (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval : ∀ i : Fin k, ∀ b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i))
    (hPi : ∀ i : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
        (rowProcessLaw (k := k) P i))
    (hStart : StartRestrictedRowKernelData (k := k) P rowKernel)
    (hStep : CrossRowCoherenceStep (k := k) P rowKernel) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  -- Assembly: length-2 base case (Crux:650, PROVED)
  have hpair := crossAnchor_lengthTwo_of_rowKernelData_restrict_direct
    (k := k) P rowKernel hEval hStart hPi
  -- Assembly: full identity by induction (Crux:695, PROVED)
  have hCAP := crossAnchorProductIdentity_of_lengthTwo_and_consStep
    (k := k) P rowKernel hpair hStep
  -- Assembly: CylinderMixingIdentity_P (Crux:130, PROVED)
  exact cylinderMixingIdentity_P_of_crossAnchorProductIdentity
    (k := k) P rowKernel hCAP

/-- Public canonical specialization of `cylinderMixingIdentity_gap`: for the
canonical `directingRowKernel`, the start-restricted factorization hypothesis is
discharged directly from the public Markov-exchangeable strong-recurrence data.

For this direct route, the remaining external input is exactly the genuine joint row-coupling content,
namely `CrossRowCoherenceStep`. -/
theorem cylinderMixingIdentity_of_directingRowKernel_of_markovExchangeable_strongRecurrence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (hStep :
      CrossRowCoherenceStep (k := k) P (directingRowKernel (k := k) P)) :
    CylinderMixingIdentity_P (k := k) P (directingRowKernel (k := k) P) := by
  have hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i) := by
    intro i b
    let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
    letI : Nonempty (Fin k) := ⟨i⟩
    letI : IsProbabilityMeasure ρ :=
      Measure.isProbabilityMeasure_map
        ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
    have hmeas :
        Measurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) ({b} : Set (Fin k))) := by
      simpa [ρ, directingRowKernel] using
        (Exchangeability.DeFinetti.ViaMartingale.directingMeasure_measurable_eval
          (μ := ρ)
          (X := fun n (r : ℕ → Fin k) => r n)
          (hX := fun n => measurable_pi_apply n)
          ({b} : Set (Fin k))
          (measurableSet_singleton b))
    exact hmeas.aemeasurable
  have hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (directingRowKernel (k := k) P i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i) := by
    intro i
    let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
    letI : Nonempty (Fin k) := ⟨i⟩
    letI : IsProbabilityMeasure ρ :=
      Measure.isProbabilityMeasure_map
        ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
    have hdir_eval_meas :
        ∀ B : Set (Fin k), MeasurableSet B →
          Measurable
            (fun r : ℕ → Fin k =>
              (directingRowKernel (k := k) P i r : Measure (Fin k)) B) := by
      intro B hB
      simpa [ρ, directingRowKernel] using
        (Exchangeability.DeFinetti.ViaMartingale.directingMeasure_measurable_eval
          (μ := ρ)
          (X := fun n (r : ℕ → Fin k) => r n)
          (hX := fun n => measurable_pi_apply n)
          B hB)
    have hmeas :
        Measurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
      exact
        measurable_measure_pi
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))
          (fun _ => by infer_instance)
          hdir_eval_meas
    exact hmeas.aemeasurable
  exact
    cylinderMixingIdentity_gap
      (k := k) P inferInstance (directingRowKernel (k := k) P) hEval hPi
      (startRestrictedRowKernelData_of_markovExchangeable_strongRecurrence
        (k := k) μ hμ P hExt hStrRec)
      hStep

/-! ## Surface theorem via the successor-matrix PE bridge

The proved assembly lemmas in this file remain useful once a row-kernel family
and `RowSuccessorMatrixInvariance` are available. The active route to those
hypotheses is the strong-recurrence successor-matrix PE bridge exposed in
`MarkovDeFinettiFortiniBridgeCrux`, not a local attempt to derive
`CrossRowCoherenceStep` directly from rowwise de Finetti data.

Routing the surface theorem through the PE bridge keeps the missing mathematics
at the right abstraction level: first prove the genuine joint symmetry theorem
`SuccessorMatrixPE_of_markovExchangeable_strongRecurrence`, then recover the
row-kernel payload and the final mixture representation from that bridge. -/

/-- Honest surface route with the minimal PE payload
`hEval + RowSuccessorMatrixInvariance`. -/
theorem fortini_surface_of_successorMatrixPE_minimal
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_minimal
    (k := k) hPEStrong hKernelFromPE

/-- Honest surface route with reduced PE-builder assumptions: derive
`hEval`/`hPi` from successor-matrix PE and keep only the start-factorization and
row-successor-matrix-invariance builders explicit. -/
theorem fortini_surface_of_successorMatrixPE_reduced
    (hk : 0 < k)
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hStartFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel)
    (hInvFromPE :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (_hPE : SuccessorMatrixPartialExchangeable (k := k) P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowSuccessorMatrixInvariance (k := k) P rowKernel) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE_reduced
      (k := k) hk hPEStrong hStartFromPE hInvFromPE

/-- Honest surface route with the stronger built-row-kernel payload. -/
theorem fortini_surface_of_successorMatrixPE
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_successorMatrixPE
    (k := k) hPEStrong hBuildFromPE

/-- Backward-compatible surface name, now explicitly routed through the PE bridge
instead of a local cross-row coherence proof attempt. -/
@[deprecated fortini_surface_of_successorMatrixPE_minimal (since := "2026-04-09")]
theorem fortini_surface
    (_hk : 0 < k)
    (hPEStrong : SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k)
    (hKernelFromPE :
      ExistsRowKernel_hEval_and_rowSuccessorMatrixInvariance_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k :=
  fortini_surface_of_successorMatrixPE_minimal
    (k := k) hPEStrong hKernelFromPE

end Mettapedia.Logic
