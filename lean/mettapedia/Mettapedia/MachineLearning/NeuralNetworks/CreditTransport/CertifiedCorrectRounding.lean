import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedDivisionSafety

/-!
# Certified correctly rounded result intervals

This file reconstructs the correctness core of Lim and Nagarakatte,
*RLIBM-32: High Performance Correctly Rounded Math Libraries for 32-bit
Floating Point Representations* (2021), Section 3 and Algorithms 1--3.

The source generates an interval of higher-precision values that all round to
one oracle result in the target representation.  An approximation need not be
closest to the exact real value: it is sufficient for its evaluated value to
remain in that rounding interval.  Polynomial synthesis may use samples, but
the candidate is accepted only after checking every target input.

`MonotoneRoundingSpec` makes the interval argument explicit.  For a monotone
rounding map, equal rounded endpoint values certify every interior value.  An
executable endpoint checker is proved sound, and an oracle-target equality
turns interval membership into correct rounding.  A nonmonotone fixture proves
that endpoint equality alone is insufficient.  A separate finite-domain
checker records the source's counterexample-guided boundary: passing a sample
does not replace exhaustive candidate validation.

The abstraction does not claim that an arbitrary backend conversion is an
IEEE-754 rounding map.  Such use requires a separately authenticated
monotonicity theorem, endpoint words, oracle target, and runtime value.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedCorrectRounding

/-- A rounding map together with the order property needed to certify a whole
rounding interval from its endpoints. -/
structure MonotoneRoundingSpec
    (High Target : Type*)
    [Preorder High] [PartialOrder Target] where
  round : High → Target
  monotone_round : Monotone round

/-- A proposed interval in the higher-precision domain whose values should all
round to `target`. -/
structure RoundingIntervalCertificate (High Target : Type*) where
  lower : High
  upper : High
  target : Target
  deriving Repr

namespace RoundingIntervalCertificate

variable {High Target : Type*}
variable [LinearOrder High] [PartialOrder Target]

/-- Membership in the proposed higher-precision interval. -/
def Contains
    (certificate : RoundingIntervalCertificate High Target)
    (value : High) : Prop :=
  certificate.lower ≤ value ∧ value ≤ certificate.upper

/-- The finite endpoint obligations for a monotone rounding map. -/
def Valid
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target) : Prop :=
  certificate.lower ≤ certificate.upper ∧
    specification.round certificate.lower = certificate.target ∧
    specification.round certificate.upper = certificate.target

instance instDecidableValid
    [DecidableLE High] [DecidableEq Target]
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target) :
    Decidable (certificate.Valid specification) := by
  unfold Valid
  infer_instance

/-- Executable endpoint checker. -/
def check
    [DecidableLE High] [DecidableEq Target]
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target) : Bool :=
  decide (certificate.Valid specification)

theorem check_eq_true_iff_valid
    [DecidableLE High] [DecidableEq Target]
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target) :
    certificate.check specification = true ↔
      certificate.Valid specification := by
  simp [check]

/-- Equal rounded endpoint values and monotonicity force the same rounded
value throughout the interval. -/
theorem round_eq_target_of_valid
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target)
    {value : High}
    (valid : certificate.Valid specification)
    (membership : certificate.Contains value) :
    specification.round value = certificate.target := by
  have lowerBound :
      specification.round certificate.lower ≤
        specification.round value :=
    specification.monotone_round membership.1
  have upperBound :
      specification.round value ≤
        specification.round certificate.upper :=
    specification.monotone_round membership.2
  apply le_antisymm
  · simpa [valid.2.2] using upperBound
  · simpa [valid.2.1] using lowerBound

/-- Soundness of the executable interval checker. -/
theorem check_sound
    [DecidableLE High] [DecidableEq Target]
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target)
    {value : High}
    (checked : certificate.check specification = true)
    (membership : certificate.Contains value) :
    specification.round value = certificate.target :=
  certificate.round_eq_target_of_valid specification
    ((certificate.check_eq_true_iff_valid specification).mp checked)
    membership

/-- Binding the checked target to an oracle result yields correct rounding for
the original input. -/
theorem correctly_rounded_of_check
    [DecidableLE High] [DecidableEq Target]
    {Input : Type*}
    (specification : MonotoneRoundingSpec High Target)
    (certificate : RoundingIntervalCertificate High Target)
    (oracleTarget : Input → Target)
    {input : Input} {value : High}
    (checked : certificate.check specification = true)
    (membership : certificate.Contains value)
    (targetBinding : certificate.target = oracleTarget input) :
    specification.round value = oracleTarget input := by
  rw [← targetBinding]
  exact certificate.check_sound specification checked membership

/-- Two independently checked constraints can be consumed at one common
higher-precision value. -/
theorem common_value_satisfies_both
    [DecidableLE High] [DecidableEq Target]
    (firstSpec secondSpec : MonotoneRoundingSpec High Target)
    (first second : RoundingIntervalCertificate High Target)
    {value : High}
    (firstChecked : first.check firstSpec = true)
    (secondChecked : second.check secondSpec = true)
    (firstMembership : first.Contains value)
    (secondMembership : second.Contains value) :
    firstSpec.round value = first.target ∧
      secondSpec.round value = second.target :=
  ⟨first.check_sound firstSpec firstChecked firstMembership,
    second.check_sound secondSpec secondChecked secondMembership⟩

/-- If one rounding map is required to produce two distinct targets, the two
checked intervals cannot have a common value. -/
theorem no_common_value_of_distinct_targets
    [DecidableLE High] [DecidableEq Target]
    (specification : MonotoneRoundingSpec High Target)
    (first second : RoundingIntervalCertificate High Target)
    (firstChecked : first.check specification = true)
    (secondChecked : second.check specification = true)
    (targetsDiffer : first.target ≠ second.target) :
    ¬ ∃ value, first.Contains value ∧ second.Contains value := by
  rintro ⟨value, firstMembership, secondMembership⟩
  have firstResult :=
    first.check_sound specification firstChecked firstMembership
  have secondResult :=
    second.check_sound specification secondChecked secondMembership
  exact targetsDiffer (firstResult.symm.trans secondResult)

end RoundingIntervalCertificate

/-! ## A nontrivial monotone fixture -/

/-- A simple saturating higher-to-target map. -/
def clippedRationalRound (value : ℚ) : ℚ :=
  min 1 (max (-1) value)

/-- Monotonicity of the saturating fixture is part of the rounding
specification, not inferred from endpoint tests. -/
def clippedRationalSpecification : MonotoneRoundingSpec ℚ ℚ where
  round := clippedRationalRound
  monotone_round :=
    monotone_const.min (monotone_const.max monotone_id)

private def positiveSaturationCertificate :
    RoundingIntervalCertificate ℚ ℚ :=
  ⟨1, 2, 1⟩

/-- The endpoint checker accepts the positive saturation cell. -/
theorem positive_saturation_certificate_accepted :
    positiveSaturationCertificate.check
      clippedRationalSpecification = true := by
  norm_num [RoundingIntervalCertificate.check,
    RoundingIntervalCertificate.Valid,
    positiveSaturationCertificate, clippedRationalSpecification,
    clippedRationalRound]

/-- A non-endpoint interior value obtains the certified target. -/
theorem positive_saturation_interior_rounds_correctly :
    clippedRationalRound (3 / 2) = 1 := by
  apply positiveSaturationCertificate.check_sound
    clippedRationalSpecification
    positive_saturation_certificate_accepted
  norm_num [positiveSaturationCertificate,
    RoundingIntervalCertificate.Contains]

/-! ## Monotonicity boundary -/

/-- Endpoint-only obligations, intentionally omitting monotonicity. -/
def EndpointOnlyValid
    {High Target : Type*} [LinearOrder High]
    (round : High → Target)
    (certificate : RoundingIntervalCertificate High Target) : Prop :=
  certificate.lower ≤ certificate.upper ∧
    round certificate.lower = certificate.target ∧
    round certificate.upper = certificate.target

/-- A map whose two endpoints agree but whose interior changes target. -/
def nonmonotoneRationalRound (value : ℚ) : ℚ :=
  if value = 0 then 1 else 0

private def nonmonotoneEndpointCertificate :
    RoundingIntervalCertificate ℚ ℚ :=
  ⟨-1, 1, 0⟩

/-- Endpoint equality alone accepts the nonmonotone fixture. -/
theorem nonmonotone_endpoints_match :
    EndpointOnlyValid nonmonotoneRationalRound
      nonmonotoneEndpointCertificate := by
  norm_num [EndpointOnlyValid, nonmonotoneRationalRound,
    nonmonotoneEndpointCertificate]

/-- The interior nevertheless rounds to a different target. -/
theorem nonmonotone_interior_violates_target :
    nonmonotoneEndpointCertificate.Contains (0 : ℚ) ∧
      nonmonotoneRationalRound 0 ≠
        nonmonotoneEndpointCertificate.target := by
  norm_num [RoundingIntervalCertificate.Contains,
    nonmonotoneEndpointCertificate, nonmonotoneRationalRound]

/-- The preceding failure is exactly a failure of monotonicity. -/
theorem nonmonotone_fixture_is_not_monotone :
    ¬ Monotone nonmonotoneRationalRound := by
  intro monotoneRound
  have contradiction := monotoneRound (show (0 : ℚ) ≤ 1 by norm_num)
  norm_num [nonmonotoneRationalRound] at contradiction

/-! ## Complete candidate validation -/

/-- Check a candidate on an explicit finite list of inputs. -/
def candidatePasses
    {Input : Type*}
    (inputs : List Input)
    (accepts : Input → Bool) : Bool :=
  inputs.all accepts

/-- A successful list check certifies each recorded input. -/
theorem candidate_passes_sound_on_list
    {Input : Type*}
    (inputs : List Input)
    (accepts : Input → Bool)
    (checked : candidatePasses inputs accepts = true) :
    ∀ input ∈ inputs, accepts input = true :=
  (List.all_eq_true.mp checked)

/-- If the explicit list covers the entire intended domain, a successful
candidate check is exhaustive over that domain. -/
theorem complete_candidate_check_sound
    {Input : Type*}
    (inputs : List Input)
    (accepts : Input → Bool)
    (coverage : ∀ input, input ∈ inputs)
    (checked : candidatePasses inputs accepts = true) :
    ∀ input, accepts input = true := by
  intro input
  exact candidate_passes_sound_on_list inputs accepts checked
    input (coverage input)

private def onePointAccepts (input : Bool) : Bool :=
  !input

/-- Passing a proper sample does not imply passing the full finite domain. -/
theorem sample_success_does_not_imply_exhaustive_success :
    candidatePasses [false] onePointAccepts = true ∧
      candidatePasses [false, true] onePointAccepts = false := by
  decide

#print axioms
  RoundingIntervalCertificate.correctly_rounded_of_check
#print axioms RoundingIntervalCertificate.no_common_value_of_distinct_targets
#print axioms positive_saturation_interior_rounds_correctly
#print axioms nonmonotone_interior_violates_target
#print axioms sample_success_does_not_imply_exhaustive_success

end CertifiedCorrectRounding

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
