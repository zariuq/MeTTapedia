import Mettapedia.Logic.GenericWorldModelForgetting

/-!
# WM Evidence-Conservation Pack

Named theorem pack for scoped forgetting/revision conservation behavior:

- Noether-style outside-scope conservation under exact inverse forgetting,
- anti-hallucination outside forgotten scope,
- leakage-budget family on observation counts,
- exact-inverse impossibility when outside-scope evidence is nonzero.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [GenericWorldModel State Query Ev]

/-- Outside-scope leakage budget for one scoped revision `Δ`. -/
def OutsideLeakageBudget
    (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (Δ : State) (B : ℝ≥0∞) : Prop :=
  ∀ q, ¬ F.inScope S q →
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) Δ q ≤ B

/-- Anti-hallucination outside forgotten scope under exact inverse forgetting. -/
theorem antiHallucination_outsideScope_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    ∀ q, ¬ F.inScope S q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
  ForgettingLayer.exactInverse_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero hinv

/-- Noether-style conservation statement: under exact inverse forgetting, a
revision preserves outside-scope evidence of every base state. -/
theorem outsideScopeEvidence_conserved_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W)
    (W : State) (q : Query) (hout : ¬ F.inScope S q) :
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
    GenericWorldModel.evidence
      (State := State) (Query := Query) (Ev := Ev) W q := by
  have hΔ0 :
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
    antiHallucination_outsideScope_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv q hout
  calc
    GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (W + Δ) q
      =
    GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) W q +
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q := by
          simpa using GenericWorldModel.evidence_add' (State := State) (Query := Query) (Ev := Ev) W Δ q
    _ =
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) W q + 0 := by
          simp [hΔ0]
    _ =
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) W q := by simp

/-- Outside-scope leakage count is exactly zero under exact inverse forgetting. -/
theorem outsideLeakageCount_zero_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    ∀ q, ¬ F.inScope S q →
      GenericWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  have hΔ0 :
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
    antiHallucination_outsideScope_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv q hout
  unfold GenericWorldModel.queryObservationCount
  simpa [hΔ0] using (ConjugateEvidence.observationCount_zero (Ev := Ev))

/-- Zero-budget leakage theorem. -/
theorem outsideLeakageBudget_zero_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ 0 := by
  intro q hout
  simp [outsideLeakageCount_zero_of_exactInverse
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero hinv q hout]

/-- Monotonicity of leakage budgets. -/
theorem outsideLeakageBudget_mono
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {Δ : State} {B₁ B₂ : ℝ≥0∞}
    (hBudget : OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ B₁)
    (hB : B₁ ≤ B₂) :
    OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ B₂ := by
  intro q hout
  exact (hBudget q hout).trans hB

/-- General leakage-budget family induced by exact inverse forgetting. -/
theorem outsideLeakageBudget_of_exactInverse
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    (B : ℝ≥0∞)
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ B := by
  exact outsideLeakageBudget_mono
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F (outsideLeakageBudget_zero_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv) (by exact bot_le)

/-- Named theorem pack for evidence conservation under one forgetting layer. -/
structure EvidenceConservationPack
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev)) :
    Prop where
  noether_outsideScope_conservation :
    ∀ {S : Scope} {Δ : State}
      (_hinv : ∀ W : State, F.forget S (W + Δ) = W)
      (W : State) (q : Query),
      ¬ F.inScope S q →
        GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
        GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) W q
  anti_hallucination_outsideScope :
    ∀ {S : Scope} {Δ : State}
      (_hinv : ∀ W : State, F.forget S (W + Δ) = W)
      (q : Query),
      ¬ F.inScope S q →
        GenericWorldModel.evidence
          (State := State) (Query := Query) (Ev := Ev) Δ q = 0
  leakage_budget_zero :
    ∀ {S : Scope} {Δ : State}
      (_hinv : ∀ W : State, F.forget S (W + Δ) = W),
      OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
        F S Δ 0
  no_exact_inverse_if_nonzero_outside :
    ∀ {S : Scope} {Δ : State} {q : Query},
      ¬ F.inScope S q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0 →
      ¬ ∀ W : State, F.forget S (W + Δ) = W

/-- Canonical constructor: every forgetting layer with zero-preserving WM
induces the full conservation pack. -/
theorem evidenceConservationPack_of_forgetting
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev)) :
    EvidenceConservationPack (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S Δ hinv W q hout
    exact outsideScopeEvidence_conserved_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv W q hout
  · intro S Δ hinv q hout
    exact antiHallucination_outsideScope_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv q hout
  · intro S Δ hinv
    exact outsideLeakageBudget_zero_of_exactInverse
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hinv
  · intro S Δ q hout hne
    exact ForgettingLayer.no_exactInverse_revision_of_nonzero_outside_scope
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hout hne

end Mettapedia.Logic
