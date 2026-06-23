import Mathlib.Data.Real.Basic
import Mettapedia.Logic.PLNIndefiniteTruth
import KnuthSkilling.Probability.BooleanRepresentation

/-!
# PLN Indefinite Truth Bridge

This file bridges finite families of event-level K&S Boolean representations
into the live PLN indefinite-truth-value surface.

The bridge is conceptually PLN-facing: it packages lower/upper probability
bounds as a `PLNIndefiniteTruth.ITV` with an explicit external credibility.
-/

namespace Mettapedia.Logic.PLNIndefiniteTruthBridge

open KnuthSkilling.Probability.BooleanRepresentation

/-- Generic constructor from lower/upper bounds and an external credibility.

This is the proof-agnostic bridge point for interval-valued semantics that
already proved their own `[0,1]` and order bounds. -/
noncomputable def ofBoundsAndCredibility
    (lower upper credibility : ℝ)
    (h_valid : lower ≤ upper)
    (h_lower : 0 ≤ lower)
    (h_upper : upper ≤ 1)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV where
  lower := lower
  upper := upper
  credibility := credibility
  lower_le_upper := h_valid
  lower_in_unit := ⟨h_lower, h_valid.trans h_upper⟩
  upper_in_unit := ⟨h_lower.trans h_valid, h_upper⟩
  credibility_in_unit := hcred

/-- A finite-family credal set built from event-level K&S Boolean representations. -/
structure CredalSet (α : Type*) [BooleanAlgebra α] where
  representations : Set (KSBooleanRepresentation α)
  nonempty : representations.Nonempty

namespace CredalSet

variable {α : Type*} [BooleanAlgebra α] (C : CredalSet α)

/-- Lower probability: infimum over represented precise probabilities. -/
noncomputable def lowerProb (a : α) : ℝ :=
  sInf { R.probability a | R ∈ C.representations }

/-- Upper probability: supremum over represented precise probabilities. -/
noncomputable def upperProb (a : α) : ℝ :=
  sSup { R.probability a | R ∈ C.representations }

/-- Interval-valued probability associated to an event. -/
noncomputable def probInterval (a : α) : Set ℝ :=
  Set.Icc (C.lowerProb a) (C.upperProb a)

/-- Package a credal interval as the live PLN indefinite truth-value type. -/
noncomputable def toPLNITV (a : α)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (h_lower : 0 ≤ C.lowerProb a)
    (h_upper : C.upperProb a ≤ 1)
    (h_valid : C.lowerProb a ≤ C.upperProb a) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  ofBoundsAndCredibility (C.lowerProb a) (C.upperProb a) credibility
    h_valid h_lower h_upper hcred

end CredalSet

end Mettapedia.Logic.PLNIndefiniteTruthBridge
