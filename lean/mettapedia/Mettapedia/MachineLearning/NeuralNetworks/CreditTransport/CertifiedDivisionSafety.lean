import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedRoundingErrorComposition

/-!
# Executable denominator-safety certificates

This file reconstructs the division-safety boundary from Becker et al.,
*A Verified Certificate Checker for Finite-Precision Error Bounds in Coq and
HOL4* (2018), Sections IV.C and V.A--V.B.

FloVer checks both the ideal real denominator range and the finite-precision
range.  Checking only the ideal range is unsound: a sufficiently large
rounding error can move a nonzero ideal denominator to zero.  The authors
report that this distinction exposed a bug in their certificate producer.

`DivisionSafetyCertificate` is a finite rational record.  Its executable
checker verifies a proper ideal interval, a nonnegative absolute-error radius,
exclusion of zero from the ideal interval, and exclusion of zero from the
error-expanded machine interval.  The kernel theorem casts these rational
checks to real arithmetic and proves both the ideal and computed denominators
nonzero.

This is a local safety certificate, not a complete floating-point semantics.
An authenticated replay must still bind the exact and computed values and
justify the declared error radius.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedDivisionSafety

noncomputable section

open CertifiedIntervalEvaluation
open CertifiedRoundingErrorComposition

/-- Rational certificate fields needed to protect one division denominator. -/
structure DivisionSafetyCertificate where
  idealLower : ℚ
  idealUpper : ℚ
  absoluteError : ℚ
  deriving Repr

namespace DivisionSafetyCertificate

/-- The ideal interval interpreted over the reals. -/
def idealInterval
    (certificate : DivisionSafetyCertificate) : ClosedInterval :=
  ⟨certificate.idealLower, certificate.idealUpper⟩

/-- The range of every computed denominator within the declared absolute
error of a value in the ideal interval. -/
def machineInterval
    (certificate : DivisionSafetyCertificate) : ClosedInterval :=
  ⟨certificate.idealLower - certificate.absoluteError,
    certificate.idealUpper + certificate.absoluteError⟩

/-- Propositional meaning of a valid finite certificate. -/
def Valid (certificate : DivisionSafetyCertificate) : Prop :=
  certificate.idealLower ≤ certificate.idealUpper ∧
    0 ≤ certificate.absoluteError ∧
    (certificate.idealUpper < 0 ∨ 0 < certificate.idealLower) ∧
    (certificate.idealUpper + certificate.absoluteError < 0 ∨
      0 < certificate.idealLower - certificate.absoluteError)

instance instDecidableValid
    (certificate : DivisionSafetyCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

/-- Executable checker for the finite rational certificate. -/
def check (certificate : DivisionSafetyCertificate) : Bool :=
  decide certificate.Valid

theorem check_eq_true_iff_valid
    (certificate : DivisionSafetyCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- The ideal interval excludes zero after a successful check. -/
theorem ideal_nonzero_of_check
    (certificate : DivisionSafetyCertificate)
    {ideal : Real}
    (checked : certificate.check = true)
    (idealMembership : certificate.idealInterval.Contains ideal) :
    ideal ≠ 0 := by
  have valid := (certificate.check_eq_true_iff_valid).mp checked
  rcases valid.2.2.1 with upperNegative | lowerPositive
  · have upperNegativeReal :
        (certificate.idealUpper : Real) < 0 := by
      exact_mod_cast upperNegative
    have idealNegative : ideal < 0 :=
      idealMembership.2.trans_lt upperNegativeReal
    exact ne_of_lt idealNegative
  · have lowerPositiveReal :
        0 < (certificate.idealLower : Real) := by
      exact_mod_cast lowerPositive
    have idealPositive : 0 < ideal :=
      lowerPositiveReal.trans_le idealMembership.1
    exact ne_of_gt idealPositive

/-- An absolute error bound transports ideal-interval membership to the
error-expanded machine interval. -/
theorem machine_membership_of_absolute_error
    (certificate : DivisionSafetyCertificate)
    {ideal computed : Real}
    (idealMembership : certificate.idealInterval.Contains ideal)
    (errorBound :
      |computed - ideal| ≤ (certificate.absoluteError : Real)) :
    certificate.machineInterval.Contains computed := by
  change
    (certificate.idealLower : Real) ≤ ideal ∧
      ideal ≤ (certificate.idealUpper : Real) at idealMembership
  have errorBounds :
      -(certificate.absoluteError : Real) ≤ computed - ideal ∧
        computed - ideal ≤ (certificate.absoluteError : Real) :=
    (abs_le).mp errorBound
  constructor
  · change
      (certificate.idealLower : Real) -
          (certificate.absoluteError : Real) ≤ computed
    linarith [idealMembership.1, errorBounds.1]
  · change
      computed ≤ (certificate.idealUpper : Real) +
        (certificate.absoluteError : Real)
    linarith [idealMembership.2, errorBounds.2]

/-- A successful certificate excludes zero from the computed denominator. -/
theorem computed_nonzero_of_check
    (certificate : DivisionSafetyCertificate)
    {ideal computed : Real}
    (checked : certificate.check = true)
    (idealMembership : certificate.idealInterval.Contains ideal)
    (errorBound :
      |computed - ideal| ≤ (certificate.absoluteError : Real)) :
    computed ≠ 0 := by
  have valid := (certificate.check_eq_true_iff_valid).mp checked
  have machineMembership :=
    certificate.machine_membership_of_absolute_error
      idealMembership errorBound
  change
    (certificate.idealLower : Real) -
          (certificate.absoluteError : Real) ≤ computed ∧
      computed ≤
        (certificate.idealUpper : Real) +
          (certificate.absoluteError : Real) at machineMembership
  rcases valid.2.2.2 with upperNegative | lowerPositive
  · have upperNegativeReal :
        (certificate.idealUpper : Real) +
            (certificate.absoluteError : Real) < 0 := by
      exact_mod_cast upperNegative
    have computedNegative : computed < 0 :=
      machineMembership.2.trans_lt upperNegativeReal
    exact ne_of_lt computedNegative
  · have lowerPositiveReal :
        0 <
          (certificate.idealLower : Real) -
            (certificate.absoluteError : Real) := by
      exact_mod_cast lowerPositive
    have computedPositive : 0 < computed :=
      lowerPositiveReal.trans_le machineMembership.1
    exact ne_of_gt computedPositive

/-- Overall local FloVer-style division-safety theorem. -/
theorem check_sound
    (certificate : DivisionSafetyCertificate)
    {ideal computed : Real}
    (checked : certificate.check = true)
    (idealMembership : certificate.idealInterval.Contains ideal)
    (errorBound :
      |computed - ideal| ≤ (certificate.absoluteError : Real)) :
    ideal ≠ 0 ∧ computed ≠ 0 :=
  ⟨certificate.ideal_nonzero_of_check checked idealMembership,
    certificate.computed_nonzero_of_check
      checked idealMembership errorBound⟩

/-- Bridge from the asymmetric absolute-error predicate to the executable
division-safety certificate. -/
theorem check_sound_of_symmetric_error_enclosure
    (certificate : DivisionSafetyCertificate)
    {ideal computed : Real}
    (checked : certificate.check = true)
    (idealMembership : certificate.idealInterval.Contains ideal)
    (errorEnclosure :
      AbsoluteErrorEnclosure computed ideal
        ⟨-(certificate.absoluteError : Real),
          certificate.absoluteError⟩) :
    ideal ≠ 0 ∧ computed ≠ 0 := by
  have errorBound :
      |computed - ideal| ≤ (certificate.absoluteError : Real) := by
    exact (abs_le).2 errorEnclosure
  exact certificate.check_sound checked idealMembership errorBound

end DivisionSafetyCertificate

/-! ## Positive and negative fixtures -/

private def positiveCertificate : DivisionSafetyCertificate :=
  ⟨1, 2, 1 / 4⟩

/-- A denominator in `[1,2]` with error at most `1/4` is accepted. -/
theorem positive_certificate_accepted :
    positiveCertificate.check = true := by
  norm_num [DivisionSafetyCertificate.check,
    DivisionSafetyCertificate.Valid, positiveCertificate]

/-- The accepted certificate proves concrete ideal and computed denominators
nonzero. -/
theorem positive_certificate_concrete_sound :
    (3 / 2 : Real) ≠ 0 ∧ (7 / 5 : Real) ≠ 0 := by
  apply positiveCertificate.check_sound positive_certificate_accepted
  · norm_num [positiveCertificate,
      DivisionSafetyCertificate.idealInterval, ClosedInterval.Contains]
  · norm_num [positiveCertificate]

private def negativeCertificate : DivisionSafetyCertificate :=
  ⟨-2, -1, 1 / 4⟩

/-- The checker handles negative denominator ranges symmetrically. -/
theorem negative_certificate_accepted :
    negativeCertificate.check = true := by
  norm_num [DivisionSafetyCertificate.check,
    DivisionSafetyCertificate.Valid, negativeCertificate]

/-- Checking only the ideal range is unsound: the ideal denominator `1`
excludes zero, yet an allowed absolute error of `1` reaches the computed
denominator `0`. -/
theorem ideal_range_only_does_not_protect_computed_denominator :
    let ideal : Real := 1
    let computed : Real := 0
    let error : Real := 1
    ideal ≠ 0 ∧ |computed - ideal| ≤ error ∧ computed = 0 := by
  norm_num

private def equalityAtMarginCertificate : DivisionSafetyCertificate :=
  ⟨1, 1, 1⟩

/-- The executable checker rejects equality at the zero-separation margin,
which is exactly the preceding failure case. -/
theorem equality_at_margin_is_rejected :
    equalityAtMarginCertificate.check = false := by
  norm_num [DivisionSafetyCertificate.check,
    DivisionSafetyCertificate.Valid, equalityAtMarginCertificate]

/-- Merely checking that the ideal interval excludes zero would accept the
same record despite its zero machine-margin. -/
theorem equality_at_margin_ideal_range_excludes_zero :
    equalityAtMarginCertificate.idealUpper < 0 ∨
      0 < equalityAtMarginCertificate.idealLower := by
  norm_num [equalityAtMarginCertificate]

private def improperCertificate : DivisionSafetyCertificate :=
  ⟨2, 1, 0⟩

/-- An improper interval cannot obtain a vacuous safety certificate. -/
theorem improper_interval_is_rejected :
    improperCertificate.check = false := by
  norm_num [DivisionSafetyCertificate.check,
    DivisionSafetyCertificate.Valid, improperCertificate]

#print axioms DivisionSafetyCertificate.check_sound
#print axioms
  DivisionSafetyCertificate.check_sound_of_symmetric_error_enclosure
#print axioms positive_certificate_concrete_sound
#print axioms ideal_range_only_does_not_protect_computed_denominator
#print axioms equality_at_margin_is_rejected

end

end CertifiedDivisionSafety

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
