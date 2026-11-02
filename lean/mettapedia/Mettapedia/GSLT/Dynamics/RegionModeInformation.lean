import Mettapedia.GSLT.Dynamics.RegionObservations
import Mettapedia.Machines.FiniteModeInformation

/-!
# Mode is an exact instance of the future-observation quotient

The independent smallest-label mode function observes a count vector after
arbitrary future additions in a fixed finite label universe. The existing
constructive separator proves that signed count differences plus occupancy
are exactly the information required. The generic quotient now supplies its
universal property on the reachable summary image.

The count vectors are unbounded. Finitely many labels do not imply a finite
summary alphabet or constant bit space. Extending the labels, observing mass,
or allowing deletion changes the interface and invalidates this quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionObservations.Mode

open Mettapedia.Machines.ModeAggregation.FiniteInformation

def futures (n : Nat) : Family (Counts n) where
  Question := Counts n
  Answer _ := Option (Label n)
  read added counts := mode (counts + added)

theorem compact_exact (n : Nat) : (futures n).Exact (@compact n) :=
  compact_eq_iff_future

theorem compact_sufficient (n : Nat) : (futures n).Sufficient (@compact n) :=
  fun left right => (compact_exact n left right).mp

noncomputable def minimalSummaryEquiv (n : Nat) :
    Set.range (@compact n) ≃ (futures n).Classes :=
  (futures n).exactEquiv compact (compact_exact n)

/-- A supposedly smaller summary must determine the compact code on every
reachable input. A distinguishing suffix refutes any collision that does not. -/
theorem every_sufficient_summary_determines_compact {n : Nat} {Code : Type}
    (summary : Counts n → Code) (sufficient : (futures n).Sufficient summary) :
    Core.NonFactorization.Factors (Set.rangeFactorization summary) (@compact n) := by
  apply (Core.NonFactorization.factors_iff_constantOnFibers
    Set.rangeFactorization_surjective (@compact n)).mpr
  intro left right same
  apply (compact_eq_iff_future left right).mpr
  exact sufficient left right (congrArg Subtype.val same)

theorem winner_is_not_sufficient : ¬ (futures 2).Sufficient (@mode 2) := by
  intro sufficient
  obtain ⟨sameWinner, differentLater⟩ := Controls.winner_alone_loses_information
  exact differentLater (sufficient _ _ sameWinner ![0, 0, 2])

theorem total_mass_does_not_descend :
    ¬ Core.NonFactorization.Factors (@compact 2) (@mass 2) := by
  intro factors
  have same := (compact_eq_iff_future Controls.first Controls.shifted).mpr
    Controls.common_offset_same_future
  have impossible := factors.constantOnFibers Controls.first Controls.shifted same
  have masses := Controls.total_count_is_not_retained
  rw [masses.1, masses.2] at impossible
  contradiction

#print axioms minimalSummaryEquiv
#print axioms every_sufficient_summary_determines_compact
#print axioms winner_is_not_sufficient
#print axioms total_mass_does_not_descend

end Mettapedia.GSLT.Dynamics.RegionObservations.Mode
