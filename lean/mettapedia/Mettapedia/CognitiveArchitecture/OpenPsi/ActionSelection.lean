/-
# OpenPsi Action Selection

Formalization of OpenPsi's action selection rule: select the demand with
lowest satisfaction (most critical need).

## Core Rule

In OpenPsi, action selection is driven by unsatisfied demands:
1. Compute fuzzy satisfaction for all demands
2. Select the demand with the lowest satisfaction
3. Choose an action that addresses that demand

This is simpler than utility-based selection - the most critical need
always takes priority.

## References

- https://wiki.opencog.org/w/OpenPsi_(2010)
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (2011)
-/

import Mettapedia.CognitiveArchitecture.OpenPsi.Basic

namespace Mettapedia.CognitiveArchitecture.OpenPsi

/-! ## Critical Demand Selection

The core OpenPsi action selection rule: select the demand with lowest
satisfaction (most critical/urgent).

We use a simple explicit comparison approach for clarity.
-/

/-- Compare two demands and return the one with lower satisfaction -/
def minDemand (sats : DemandType → UnitValue) (d1 d2 : DemandType) : DemandType :=
  if (sats d1).val ≤ (sats d2).val then d1 else d2

/-- minDemand returns a demand with satisfaction ≤ both inputs -/
theorem minDemand_le_left (sats : DemandType → UnitValue) (d1 d2 : DemandType) :
    (sats (minDemand sats d1 d2)).val ≤ (sats d1).val := by
  simp only [minDemand]
  split_ifs with h
  · exact le_refl _
  · exact le_of_lt (lt_of_not_ge h)

theorem minDemand_le_right (sats : DemandType → UnitValue) (d1 d2 : DemandType) :
    (sats (minDemand sats d1 d2)).val ≤ (sats d2).val := by
  simp only [minDemand]
  split_ifs with h
  · exact h
  · exact le_refl _

/-- Select the demand with lowest satisfaction among all 6 demands.
    This is the core OpenPsi action selection rule. -/
def selectCriticalDemand (sats : DemandType → UnitValue) : DemandType :=
  let m1 := minDemand sats .energy .water
  let m2 := minDemand sats m1 .integrity
  let m3 := minDemand sats m2 .affiliation
  let m4 := minDemand sats m3 .certainty
  minDemand sats m4 .competence

/-- Helper: transitivity of minDemand across 3 elements -/
theorem minDemand_chain_le (sats : DemandType → UnitValue) (d1 d2 d3 : DemandType) :
    (sats (minDemand sats (minDemand sats d1 d2) d3)).val ≤ (sats d1).val := by
  calc (sats (minDemand sats (minDemand sats d1 d2) d3)).val
      ≤ (sats (minDemand sats d1 d2)).val := minDemand_le_left sats _ d3
    _ ≤ (sats d1).val := minDemand_le_left sats d1 d2

/-- The selected demand has minimal satisfaction among all demands -/
theorem selectCriticalDemand_minimal (sats : DemandType → UnitValue) (d : DemandType) :
    (sats (selectCriticalDemand sats)).val ≤ (sats d).val := by
  unfold selectCriticalDemand
  cases d with
  | energy =>
    calc (sats (minDemand sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty) .competence)).val
        ≤ (sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty)).val :=
          minDemand_le_left sats _ .competence
      _ ≤ (sats (minDemand sats (minDemand sats (minDemand sats .energy .water) .integrity) .affiliation)).val :=
          minDemand_le_left sats _ .certainty
      _ ≤ (sats (minDemand sats (minDemand sats .energy .water) .integrity)).val :=
          minDemand_le_left sats _ .affiliation
      _ ≤ (sats (minDemand sats .energy .water)).val :=
          minDemand_le_left sats _ .integrity
      _ ≤ (sats .energy).val := minDemand_le_left sats .energy .water
  | water =>
    calc (sats (minDemand sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty) .competence)).val
        ≤ (sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty)).val :=
          minDemand_le_left sats _ .competence
      _ ≤ (sats (minDemand sats (minDemand sats (minDemand sats .energy .water) .integrity) .affiliation)).val :=
          minDemand_le_left sats _ .certainty
      _ ≤ (sats (minDemand sats (minDemand sats .energy .water) .integrity)).val :=
          minDemand_le_left sats _ .affiliation
      _ ≤ (sats (minDemand sats .energy .water)).val :=
          minDemand_le_left sats _ .integrity
      _ ≤ (sats .water).val := minDemand_le_right sats .energy .water
  | integrity =>
    calc (sats (minDemand sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty) .competence)).val
        ≤ (sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty)).val :=
          minDemand_le_left sats _ .competence
      _ ≤ (sats (minDemand sats (minDemand sats (minDemand sats .energy .water) .integrity) .affiliation)).val :=
          minDemand_le_left sats _ .certainty
      _ ≤ (sats (minDemand sats (minDemand sats .energy .water) .integrity)).val :=
          minDemand_le_left sats _ .affiliation
      _ ≤ (sats .integrity).val := minDemand_le_right sats _ .integrity
  | affiliation =>
    calc (sats (minDemand sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty) .competence)).val
        ≤ (sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty)).val :=
          minDemand_le_left sats _ .competence
      _ ≤ (sats (minDemand sats (minDemand sats (minDemand sats .energy .water) .integrity) .affiliation)).val :=
          minDemand_le_left sats _ .certainty
      _ ≤ (sats .affiliation).val := minDemand_le_right sats _ .affiliation
  | certainty =>
    calc (sats (minDemand sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty) .competence)).val
        ≤ (sats (minDemand sats (minDemand sats (minDemand sats
            (minDemand sats .energy .water) .integrity) .affiliation) .certainty)).val :=
          minDemand_le_left sats _ .competence
      _ ≤ (sats .certainty).val := minDemand_le_right sats _ .certainty
  | competence =>
    exact minDemand_le_right sats _ .competence

/-- Alternative form: selected demand satisfies ≤ any other demand -/
theorem selectCriticalDemand_is_critical (sats : DemandType → UnitValue) :
    ∀ d : DemandType, sats (selectCriticalDemand sats) ≤ sats d := by
  intro d
  show (sats (selectCriticalDemand sats)).val ≤ (sats d).val
  exact selectCriticalDemand_minimal sats d

/-! ## Action Selection from State

Combining critical demand selection with the full OpenPsi state.
-/

/-- Select the most critical demand from an OpenPsi state -/
noncomputable def OpenPsiState.criticalDemand (state : OpenPsiState) : DemandType :=
  selectCriticalDemand state.demands.allSatisfactions

/-- The selected demand has minimal satisfaction in the state.
    This follows directly from selectCriticalDemand_minimal. -/
theorem OpenPsiState.criticalDemand_minimal
    (state : OpenPsiState) (d : DemandType) :
    (state.demands.allSatisfactions (state.criticalDemand)).val ≤
    (state.demands.allSatisfactions d).val :=
  selectCriticalDemand_minimal state.demands.allSatisfactions d

/-! ## Interpretation

The action selection rule captures Dörner's "lowest satisfaction wins" principle:

1. **Urgency**: The demand with lowest satisfaction is most urgent
2. **Focus**: Agent focuses on one critical need at a time
3. **Switching**: As satisfactions change, focus can switch to different demands

This is different from utility-based selection which considers:
- Action costs
- Expected gains
- Multiple demands simultaneously

OpenPsi's simpler rule is more biologically plausible and computationally efficient.
-/

end Mettapedia.CognitiveArchitecture.OpenPsi
