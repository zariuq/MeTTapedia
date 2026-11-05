import Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

/-!
# WM BinaryEvidence-Conservation Pack

Named theorem pack for scoped forgetting/revision conservation behavior, for a
revision `Δ` that forgetting the scope erases (`F.forget S Δ = 0`):

- Noether-style outside-scope conservation: adding `Δ` changes no query outside
  the scope;
- anti-hallucination outside the forgotten scope;
- leakage-budget family on observation counts;
- a revision with nonzero outside-scope evidence cannot be erased.

Erasure is the inverse law asked of the empty base.  The same law asked of
every base is degenerate
(`GenericWorldModelForgetting.ForgettingLayer.exactInverse_everywhere_degenerate`);
with supports, every revision supported in the footprint is erased
(`PLNWorldModelSupportForgetting.SupportTrackedForgettingLayer`).
-/

namespace Mettapedia.PLN.WorldModel.WorldModelConservationPack

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]

/-- Outside-scope leakage budget for one scoped revision `Δ`. -/
def OutsideLeakageBudget
    (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (Δ : State) (B : ℝ≥0∞) : Prop :=
  ∀ q, ¬ F.inScope S q →
    AdditiveWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) Δ q ≤ B

/-- Anti-hallucination outside the forgotten scope for an erased revision. -/
theorem antiHallucination_outsideScope_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    ∀ q, ¬ F.inScope S q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
  ForgettingLayer.erased_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero herase

/-- Noether-style conservation statement: an erased revision preserves the
outside-scope evidence of every base state. -/
theorem outsideScopeEvidence_conserved_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0)
    (W : State) (q : Query) (hout : ¬ F.inScope S q) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) W q := by
  have hΔ0 :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
    antiHallucination_outsideScope_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase q hout
  calc
    AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (W + Δ) q
      =
    AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q +
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q := by
          simpa using AdditiveWorldModel.extract_add' (State := State) (Query := Query) (Ev := Ev) W Δ q
    _ =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q + 0 := by
          simp [hΔ0]
    _ =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q := by simp

/-- Outside-scope leakage count of an erased revision is exactly zero. -/
theorem outsideLeakageCount_zero_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    ∀ q, ¬ F.inScope S q →
      AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  have hΔ0 :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
    antiHallucination_outsideScope_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase q hout
  unfold AdditiveWorldModel.queryObservationCount
  simpa [hΔ0] using (ConjugateEvidence.observationCount_zero (Ev := Ev))

/-- Zero-budget leakage theorem. -/
theorem outsideLeakageBudget_zero_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ 0 := by
  intro q hout
  simp [outsideLeakageCount_zero_of_erases
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero herase q hout]

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

/-- General leakage-budget family of an erased revision. -/
theorem outsideLeakageBudget_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    (B : ℝ≥0∞)
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F S Δ B := by
  exact outsideLeakageBudget_mono
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F (outsideLeakageBudget_zero_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase) (by exact bot_le)

/-- Named theorem pack for evidence conservation under one forgetting layer. -/
structure EvidenceConservationPack
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev)) :
    Prop where
  noether_outsideScope_conservation :
    ∀ {S : Scope} {Δ : State}
      (_herase : F.forget S Δ = 0)
      (W : State) (q : Query),
      ¬ F.inScope S q →
        AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
        AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) W q
  anti_hallucination_outsideScope :
    ∀ {S : Scope} {Δ : State}
      (_herase : F.forget S Δ = 0)
      (q : Query),
      ¬ F.inScope S q →
        AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) Δ q = 0
  leakage_budget_zero :
    ∀ {S : Scope} {Δ : State}
      (_herase : F.forget S Δ = 0),
      OutsideLeakageBudget (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
        F S Δ 0
  not_erased_if_nonzero_outside :
    ∀ {S : Scope} {Δ : State} {q : Query},
      ¬ F.inScope S q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0 →
      F.forget S Δ ≠ 0

/-- Canonical constructor: every forgetting layer with zero-preserving WM
induces the full conservation pack. -/
theorem evidenceConservationPack_of_forgetting
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev)) :
    EvidenceConservationPack (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S Δ herase W q hout
    exact outsideScopeEvidence_conserved_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase W q hout
  · intro S Δ herase q hout
    exact antiHallucination_outsideScope_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase q hout
  · intro S Δ herase
    exact outsideLeakageBudget_zero_of_erases
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero herase
  · intro S Δ q hout hne
    exact ForgettingLayer.not_erased_of_nonzero_outside_scope
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F hzero hout hne

/-! ## Profile-Level Conservation

The four conservation theorems unify into one profile-level statement: for an
erased revision, the revision's evidence profile vanishes outside the scope AND
the revised profile equals the base profile there. -/

/-- **Profile-level conservation** for a revision that forgetting erases:
    (1) the revision's profile vanishes outside the scope, and
    (2) the revised state's profile agrees with the base state's profile
    outside the scope.

    This is the single profile theorem from which all four per-query
    conservation lemmas follow by projection. -/
theorem profile_conservation_of_erases
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0)
    (q : Query) (hout : ¬ F.inScope S q) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) Δ q = 0 ∧
    ∀ W : State,
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q :=
  ⟨antiHallucination_outsideScope_of_erases F hzero herase q hout,
   fun W => outsideScopeEvidence_conserved_of_erases F hzero herase W q hout⟩

end Mettapedia.PLN.WorldModel.WorldModelConservationPack
