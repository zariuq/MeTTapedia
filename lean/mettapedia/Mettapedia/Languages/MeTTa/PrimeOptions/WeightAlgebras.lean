import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.GSLT.Logic.GradedSupport
import Mettapedia.GSLT.Core.WriterGSLT
import Mettapedia.GSLT.LanguageDef.GradedLanguageDef
import Mettapedia.Algebra.TropicalAffineSummary
import Mettapedia.Algorithms.CertifiedRealCircuit
import Mettapedia.Algorithms.OrdinalPriority
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOrdinalAdvice
import Mettapedia.GSLT.Core.WeightOrderedSelection
import Mettapedia.Algebra.FiniteCoordinateBuffer
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls
import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mettapedia.Algebra.RationalComplexAmplitude
import Mettapedia.GSLT.Scope.WeightedReadout
import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra
import Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency
import Mettapedia.GSLT.Distinction.FrontierWitnesses.Weights

/-!
# What a weight means, placed in the option graph

One question with eight options: Boolean weights, natural and nonnegative rational numbers,
min-plus costs with an actual infinity, ordinal priorities, vectors and square matrices,
complex amplitudes read by the Born rule, PLN evidence, and an algebra given by a program's
descriptor. Each option's facts are the theorems the closed gate of algebra and interpretation
binds to its family; the modules are imported, not edited.

* **Cancellation.** Opposite amplitudes add to zero while both occurrences remain; Boolean,
  natural and nonnegative rational weights cannot cancel.
* **A pruning law that does not fit.** Adding nonnegative costs is a superior combination, which
  licenses stopping early; rational multiplication is not, and a fixture declaring the
  nonnegative-sum law for a multiplicative algebra is refused.
* **Descriptor syntax supplies no laws.** Min-plus has its laws proved; for a descriptor, two
  liftings of one aggregate disagree, and an operation named addition need not be superior.
* **Zero divisors.** PLN evidence and vectors have nonzero weights whose product is zero; natural
  numbers and amplitudes do not.
* **Idempotence, size, well-foundedness and a greatest value.** OR and AND are idempotent, adding
  counts and sequencing costs are not; the OR/AND algebra has two values and checked ordinal
  priorities infinitely many; nonnegative rationals descend forever and ordinal priorities do
  not; min-plus has infinity above every cost and no checked priority is greatest.

Two readouts are arrows: support, from natural and rational weights to Boolean ones, which is
exactly reachability for algebras that cannot cancel; and the Born readout, from amplitudes to
nonnegative rationals, which forgets future interference and is not additive.

`graph` is the local graph of this module, checked by `graph_wellFormed`, `contracts_cited`,
`quotients_honest`, `contracts_consistent` and `lossy_counterexampled`; `targets_kernelChecked`
says the witnesses proved for frontier targets rest on theorems only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.WeightAlgebras

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph
open Mettapedia.GSLT.Distinction.FrontierWitnesses

/-- The report of the closed gate of algebra and interpretation. -/
def report : Document where
  key := "g1-algebra-report-20261005"
  title := "G1 algebra and interpretation — closed: report"
  date := "2026-10-05"

/-- The native library of weight algebra descriptors. -/
def descriptorLibrary : Document where
  key := "native-weight-algebras-library"
  title := "Native weight algebra descriptors"
  date := "2026-10-05"

/-- The Born readout as a function, the map of its arrow. -/
def bornReadout : Mettapedia.Algebra.RationalComplexAmplitude.Amplitude → ℚ :=
  fun amplitude => Mettapedia.Algebra.RationalComplexAmplitude.born amplitude

def question : Question where
  id := "weight-meaning"
  title := "What a weight means"
  summary := "Which algebra a coefficient on an alternative is read in, with which laws, and \
    which readout turns it into an answer."
  facts := [.argument report.key "A weight can count evidence, order a search or carry an \
    amplitude." "Counting evidence, ordering a search and carrying an amplitude have different \
    laws."]

def nodes : List Node := [
  { id := "weight-boolean", question := question.id, title := "Boolean"
    summary := "OR for alternatives, AND for sequencing; the neutral grading leaves base \
      execution unchanged."
    facts := [cites [``Mettapedia.GSLT.GradedSupport.OrBool.instCommSemiring,
      ``Mettapedia.GSLT.GradedSupport.OrBool.noCancellation,
      ``Mettapedia.GSLT.GradedSupport.Control.orBool_keeps_sink,
      ``Mettapedia.GSLT.GradedSupport.Control.xor_deficit,
      ``Mettapedia.GSLT.WriterGSLT.constGrading_unit_step_iff,
      ``Mettapedia.GSLT.WriterGSLT.constGrading_unit_multiStep_iff,
      ``Mettapedia.GSLT.LanguageDef.GradedLanguageDef.toFreeGSLT_step_of_no_weights]] },
  { id := "weight-natural-rational", question := question.id, title := "Natural and rational numbers"
    summary := "Natural counts and nonnegative rational multiplicative weights; interpreted real \
      circuits compared soundly where an enclosure decides."
    facts := [cites [``Mettapedia.GSLT.GradedSupport.nat_noCancellation,
      ``Mettapedia.GSLT.GradedSupport.nonnegative_rat_noCancellation,
      ``Mettapedia.GSLT.GradedSupport.Control.end_normalisation_is_not_the_jump_chain,
      ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.coefficient_is_not_occurrence_count,
      ``Mettapedia.Algorithms.CertifiedRealCircuit.Circuit.enclosure_sound,
      ``Mettapedia.Algorithms.CertifiedRealCircuit.Circuit.comparison_lt_sound,
      ``Mettapedia.Algorithms.CertifiedRealCircuit.Circuit.comparison_eq_sound,
      ``Mettapedia.Algorithms.CertifiedRealCircuit.Circuit.identical_log_two_is_unresolved]] },
  { id := "weight-min-plus", question := question.id, title := "Min-plus costs"
    summary := "Tropical costs with an actual infinity: the minimum for alternatives, addition \
      for sequencing."
    facts := [cites [``Mettapedia.Algebra.TropicalCoefficient.alternative_associative,
      ``Mettapedia.Algebra.TropicalCoefficient.sequential_associative,
      ``Mettapedia.Algebra.TropicalCoefficient.sequential_distributes_left,
      ``Mettapedia.Algebra.TropicalCoefficient.finite_sentinel_not_identity,
      ``Mettapedia.Algebra.TropicalCoefficient.finite_costs_do_not_multiply]] },
  { id := "weight-ordinal", question := question.id, title := "Ordinal priority"
    summary := "Checked finite Cantor normal forms below ω^ω, compared and selected least first; \
      a well-order alone does not make selection fair."
    facts := [cites [``Mettapedia.Algorithms.OrdinalPriority.comparison_semantics,
      ``Mettapedia.Algorithms.OrdinalPriority.scan_comparison_semantics,
      ``Mettapedia.Algorithms.OrdinalPriority.checked_priority_below_omega_pow_omega,
      ``Mettapedia.Algorithms.OrdinalPriority.infinitely_many_priorities_below_omega,
      ``Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOrdinalAdvice.pending_score_has_no_proposal,
      ``Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOrdinalAdvice.compared_atoms_sound,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.least_first_selects,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.ReturningZero.goal_starves,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.ZeroChain.target_starves,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.Descending.age_lane_selects_goal]] },
  { id := "weight-vectors-matrices", question := question.id, title := "Vectors and square matrices"
    summary := "Componentwise vectors with the Pareto order, and shape-checked matrix contraction \
      in which the order of factors matters."
    facts := [cites [``Mettapedia.Algebra.FiniteCoordinateBuffer.zipWith?_ofFn,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.zipWith?_shape_refusal,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.contract_rowMajor,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.Dense.multiply_associative,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.Dense.multiply_shape_refusal,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.matrix_order_control,
      ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.pareto_incomparable,
      ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.vector_zero_divisors,
      ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.reordering_matrix_coefficients_changes_answer]] },
  { id := "weight-complex-born", question := question.id
    title := "Complex amplitude with a Born readout"
    summary := "Exact rational complex amplitudes, aggregated by answer before a separately \
      declared Born readout."
    readings := [(.distinctions, ``Mettapedia.GSLT.Scope.WeightedReadout.interferenceAfter)]
    facts := [cites [``Mettapedia.Algebra.RationalComplexAmplitude.pair_multiply_agrees,
      ``Mettapedia.Algebra.RationalComplexAmplitude.intoComplex_injective,
      ``Mettapedia.Algebra.RationalComplexAmplitude.born_agrees_complex,
      ``Mettapedia.Algebra.RationalComplexAmplitude.born_not_additive,
      ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_preserves_labels,
      ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_preserves_occurrences,
      ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_nonnegative,
      ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_sum_one,
      ``Mettapedia.Algebra.RationalComplexAmplitude.cancelled_readout_refused,
      ``Mettapedia.GSLT.Scope.WeightedReadout.cancellation_retains_occurrences,
      ``Mettapedia.GSLT.Scope.WeightedReadout.future_interference_not_factors_born]] },
  { id := "weight-pln-evidence", question := question.id, title := "PLN evidence"
    summary := "Pairs of positive and negative evidence counts: count addition, tensor and a \
      calibrated projection, each with its own laws; revision needs independent sources."
    facts := [cites [``Mettapedia.PLN.Evidence.instCommSemiringBinEvNat,
      ``Mettapedia.PLN.Evidence.exact_evidence_zero_divisors,
      ``Mettapedia.PLN.Evidence.count_addition_not_idempotent,
      ``Mettapedia.PLN.Evidence.exact_evidence_tensor_control,
      ``Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra.countSemiringHom,
      ``Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra.revision_not_idempotent,
      ``Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra.propensity_not_additive,
      ``Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency.no_propensity_only_revision,
      ``Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency.evidence_revision_factorsThrough]] },
  { id := "weight-program-descriptor", question := question.id
    title := "Program-defined descriptor"
    summary := "An algebra given by a program's descriptor of operations; the operations run, and \
      no law is inferred from the descriptor."
    facts := [cites [``Mettapedia.GSLT.Dynamics.WeightedResumption.sequence_assoc,
      ``Mettapedia.GSLT.Dynamics.WeightedResumption.interpret_bind,
      ``Mettapedia.GSLT.Dynamics.WeightedResumption.interpret_mapCoefficients,
      ``Mettapedia.GSLT.Dynamics.WeightedResumption.total_sequence,
      ``Mettapedia.GSLT.Scope.WeightedReadout.aggregate_liftings_disagree,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.Realized.stepBound,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.rat_mul_not_superior,
      ``Mettapedia.GSLT.Core.WeightOrderedSelection.intAdd_not_superior],
      .argument descriptorLibrary.key
        "An algebra descriptor supplies operations; it is not evidence of their laws."
        "A descriptor names the operations of an algebra; it supplies none of their laws."] }
]

/-! ## Readouts -/

def arrows : List Arrow := [
  { id := "support-readout", source := "weight-natural-rational", target := "weight-boolean"
    kind := .observationalQuotient
    grades := [.ungraded]
    summary := "A natural or nonnegative rational coefficient read by whether it is nonzero: for \
      an algebra that cannot cancel, the support of the graded denotation is exactly what is \
      reached."
    evidence := [cites [``Mettapedia.GSLT.GradedSupport.denote_ne_zero_iff_reachIn,
      ``Mettapedia.GSLT.GradedSupport.nat_noCancellation,
      ``Mettapedia.GSLT.GradedSupport.nonnegative_rat_noCancellation]]
    contract := {
      entries := [
        .keeps .verdicts [``Mettapedia.GSLT.GradedSupport.denote_ne_zero_iff_reachIn,
          ``Mettapedia.GSLT.GradedSupport.normal_support_iff]
          "which states are reached within a budget, and which normal forms",
        .unknownAt .distinctions "the counts and multiplicities the support forgets"]
      hypotheses := [``Mettapedia.GSLT.GradedSupport.NoCancellation] } },
  { id := "born-readout", source := "weight-complex-born", target := "weight-natural-rational"
    kind := .observationalQuotient
    map := some ``bornReadout
    grades := [.lossy]
    summary := "An amplitude read by its Born intensity, a nonnegative rational; normalization \
      keeps labels and occurrences and refuses a zero total."
    evidence := [cites [``Mettapedia.Algebra.RationalComplexAmplitude.born_agrees_complex,
      ``Mettapedia.GSLT.Scope.WeightedReadout.future_interference_not_factors_born,
      ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_preserves_occurrences]]
    contract := {
      entries := [
        .keeps (.evidence .occurrences)
          [``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_preserves_occurrences,
          ``Mettapedia.Algebra.RationalComplexAmplitude.normalizeBorn_preserves_labels]
          "labels and occurrences survive Born normalization",
        .loses .distinctions
          [``Mettapedia.GSLT.Scope.WeightedReadout.future_interference_not_factors_born,
          ``Mettapedia.GSLT.Scope.WeightedReadout.same_intensity_different_future_interference]
          "future interference: 1 and -1 have one intensity and interfere differently with 1",
        .loses .laws [``Mettapedia.Algebra.RationalComplexAmplitude.born_not_additive]
          "addition: the intensity of 1 + -1 is not the sum of the intensities"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "weight-cancellation", title := "Cancellation"
    reads := "Whether two nonzero coefficients of the algebra can add to zero."
    kind := .«theorem» },
  { id := "weight-zero-divisors", title := "Zero divisors"
    reads := "Whether two nonzero coefficients of the algebra can multiply to zero."
    kind := .«theorem» },
  { id := "weight-pruning-law", title := "A pruning law that fits"
    reads := "Whether the law that licenses stopping a weighted search early, a superior \
      combination such as the sum of nonnegative costs, fits the algebra's sequencing."
    kind := .«theorem» },
  { id := "weight-proved-laws", title := "Laws by proof"
    reads := "Whether the algebra's laws hold by proof for every value, rather than being read \
      off its descriptor."
    kind := .«theorem» },
  { id := "weight-commutative-sequencing", title := "Commutative sequencing"
    reads := "Whether sequencing two coefficients gives the same result in either order."
    kind := .«theorem» },
  { id := "weight-idempotent-alternatives", title := "Idempotent alternatives"
    reads := "Whether combining a coefficient with itself as an alternative returns it."
    kind := .«theorem» },
  { id := "weight-total-comparison", title := "Total comparison"
    reads := "Whether any two coefficients are comparable."
    kind := .«theorem» },
  { id := "weight-idempotent-sequencing", title := "Idempotent sequencing"
    reads := "Whether sequencing a coefficient with itself returns it."
    kind := .«theorem» },
  { id := "weight-finitely-many-values", title := "Finitely many values"
    reads := "Whether the algebra has only finitely many coefficients."
    kind := .«theorem» },
  { id := "weight-well-founded", title := "Well-founded order"
    reads := "Whether every strictly descending chain of coefficients is finite."
    kind := .«theorem» },
  { id := "weight-greatest-value", title := "A greatest value"
    reads := "Whether one coefficient lies above every other in the algebra's order."
    kind := .«theorem» }
]

/-- The verdict that a descriptor supplies no laws. -/
def descriptorVerdict : Verdict where
  reading := "Not supplied: two liftings of one aggregate disagree, and an operation named \
    addition need not be superior."
  evidence := [cites [``Mettapedia.GSLT.Scope.WeightedReadout.aggregate_liftings_disagree,
    ``Mettapedia.GSLT.Core.WeightOrderedSelection.intAdd_not_superior]]

/-- A witness that a descriptor supplies no laws while the other option's laws are proved. -/
def lawsWitness (id other reading : String) (evidence : List Name) : Witness where
  id := id
  observer := "weight-proved-laws"
  left := "weight-program-descriptor"
  right := other
  case := "The laws of the algebra's operations."
  leftVerdict := descriptorVerdict
  rightVerdict := { reading := reading, evidence := [cites evidence] }

/-- Witnesses found when the frontier was surveyed. -/
def surveyWitnesses : List Witness := [
  { id := "boolean-vector-zero-divisors", observer := "weight-zero-divisors"
    left := "weight-boolean", right := "weight-vectors-matrices"
    case := "A product of two nonzero coefficients."
    leftVerdict := {
      reading := "Never zero: the OR/AND algebra has no zero divisors."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.OrBool.noCancellation]] }
    rightVerdict := {
      reading := "Zero: two nonzero objective vectors multiply componentwise to zero."
      evidence := [cites [``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.vector_zero_divisors]] } },
  { id := "boolean-evidence-zero-divisors", observer := "weight-zero-divisors"
    left := "weight-boolean", right := "weight-pln-evidence"
    case := "A product of two nonzero coefficients."
    leftVerdict := {
      reading := "Never zero: the OR/AND algebra has no zero divisors."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.OrBool.noCancellation]] }
    rightVerdict := {
      reading := "Zero: purely positive and purely negative evidence tensor to zero."
      evidence := [cites [``Mettapedia.PLN.Evidence.exact_evidence_zero_divisors]] } },
  { id := "matrices-do-not-commute", observer := "weight-commutative-sequencing"
    left := "weight-min-plus", right := "weight-vectors-matrices"
    case := "Two coefficients sequenced in both orders."
    leftVerdict := {
      reading := "Same result: adding costs is commutative."
      evidence := [cites [``Mettapedia.Algebra.TropicalCoefficient.sequential_commutative]] }
    rightVerdict := {
      reading := "Different results: two 2×2 matrices multiplied in the two orders differ, and \
        reordering matrix coefficients changes the answer."
      evidence := [cites [``Mettapedia.Algebra.FiniteCoordinateBuffer.matrix_order_control,
        ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.reordering_matrix_coefficients_changes_answer]] } },
  { id := "evidence-tensor-commutes", observer := "weight-commutative-sequencing"
    left := "weight-pln-evidence", right := "weight-vectors-matrices"
    case := "Two coefficients sequenced in both orders."
    leftVerdict := {
      reading := "Same result: evidence with count addition and tensor is a commutative semiring."
      evidence := [cites [``Mettapedia.PLN.Evidence.instCommSemiringBinEvNat]] }
    rightVerdict := {
      reading := "Different results: two 2×2 matrices multiplied in the two orders differ."
      evidence := [cites [``Mettapedia.Algebra.FiniteCoordinateBuffer.matrix_order_control]] } },
  { id := "evidence-addition-not-idempotent", observer := "weight-idempotent-alternatives"
    left := "weight-min-plus", right := "weight-pln-evidence"
    case := "A coefficient combined with itself as an alternative."
    leftVerdict := {
      reading := "Returned: the minimum of a cost with itself is the cost."
      evidence := [cites [``Mettapedia.Algebra.TropicalCoefficient.alternative_idempotent]] }
    rightVerdict := {
      reading := "Not returned: adding the evidence (2, 3) to itself gives (4, 6)."
      evidence := [cites [``Mettapedia.PLN.Evidence.count_addition_not_idempotent,
        ``Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra.revision_not_idempotent]] } },
  { id := "pareto-incomparable", observer := "weight-total-comparison"
    left := "weight-ordinal", right := "weight-vectors-matrices"
    case := "Two coefficients, compared."
    leftVerdict := {
      reading := "Comparable: the comparison of two checked priorities is the comparison of \
        their ordinals."
      evidence := [cites [``Mettapedia.Algorithms.OrdinalPriority.comparison_semantics,
        ``Mettapedia.Algorithms.OrdinalPriority.scan_comparison_semantics]] }
    rightVerdict := {
      reading := "Incomparable: two objective vectors neither of which is below the other."
      evidence := [cites [``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.pareto_incomparable]] } },
  lawsWitness "descriptor-against-boolean" "weight-boolean"
    "Proved: the OR/AND algebra is a commutative semiring that cannot cancel."
    [``Mettapedia.GSLT.GradedSupport.OrBool.instCommSemiring,
      ``Mettapedia.GSLT.GradedSupport.OrBool.noCancellation],
  lawsWitness "descriptor-against-numbers" "weight-natural-rational"
    "Proved: natural numbers and nonnegative rationals cannot cancel, have no zero divisors, and \
      have 1 ≠ 0."
    [``Mettapedia.GSLT.GradedSupport.nat_noCancellation,
      ``Mettapedia.GSLT.GradedSupport.nonnegative_rat_noCancellation],
  lawsWitness "descriptor-against-ordinal" "weight-ordinal"
    "Proved: the comparison of checked priorities is the comparison of their ordinals."
    [``Mettapedia.Algorithms.OrdinalPriority.comparison_semantics,
      ``Mettapedia.Algorithms.OrdinalPriority.scan_comparison_semantics],
  lawsWitness "descriptor-against-matrices" "weight-vectors-matrices"
    "Proved: dense matrix multiplication is associative, and componentwise operations agree \
      with the coordinate functions."
    [``Mettapedia.Algebra.FiniteCoordinateBuffer.Dense.multiply_associative,
      ``Mettapedia.Algebra.FiniteCoordinateBuffer.zipWith?_ofFn],
  lawsWitness "descriptor-against-amplitudes" "weight-complex-born"
    "Proved: multiplication of coordinate pairs is the algebra's multiplication, and the algebra \
      embeds injectively in the complex numbers."
    [``Mettapedia.Algebra.RationalComplexAmplitude.pair_multiply_agrees,
      ``Mettapedia.Algebra.RationalComplexAmplitude.intoComplex_injective],
  lawsWitness "descriptor-against-evidence" "weight-pln-evidence"
    "Proved: evidence with count addition and tensor is a commutative semiring."
    [``Mettapedia.PLN.Evidence.instCommSemiringBinEvNat]
]

/-- The cancellation verdict of amplitudes. -/
def amplitudesCancel : Verdict where
  reading := "Cancellation: 1 and -1 add to zero while both occurrences remain."
  evidence := [cites [``Mettapedia.GSLT.Scope.WeightedReadout.cancellation_retains_occurrences]]

/-- Witnesses proved for targets of the frontier map. -/
def targetWitnesses : List Witness := [
  { id := "boolean-alternatives-idempotent", observer := "weight-idempotent-alternatives"
    left := "weight-boolean", right := "weight-natural-rational"
    case := "A coefficient combined with itself as an alternative."
    leftVerdict := {
      reading := "Returned: OR of a Boolean weight with itself is the weight."
      evidence := [cites [``Weights.orBool_add_self]] }
    rightVerdict := {
      reading := "Not returned: the count 1 with itself is 2, and the nonnegative rational 1 \
        with itself is not 1."
      evidence := [cites [``Weights.nat_add_not_idempotent,
        ``Weights.nonnegativeRat_add_not_idempotent]] } },
  { id := "boolean-sequencing-idempotent", observer := "weight-idempotent-sequencing"
    left := "weight-boolean", right := "weight-min-plus"
    case := "A coefficient sequenced with itself."
    leftVerdict := {
      reading := "Returned: AND of a Boolean weight with itself is the weight."
      evidence := [cites [``Weights.orBool_mul_self]] }
    rightVerdict := {
      reading := "Not returned: the cost 1 sequenced with itself is the cost 2."
      evidence := [cites [``Weights.minPlus_sequential_not_idempotent]] } },
  { id := "priorities-infinitely-many", observer := "weight-finitely-many-values"
    left := "weight-boolean", right := "weight-ordinal"
    case := "The coefficients of the algebra, counted."
    leftVerdict := {
      reading := "Two: every weight of the OR/AND algebra is 0 or 1."
      evidence := [cites [``Weights.orBool_two_values]] }
    rightVerdict := {
      reading := "Infinitely many: there is a checked priority, and every checked priority has \
        a strictly larger one."
      evidence := [cites [``Weights.checked_priorities_infinite]] } },
  { id := "rational-weights-descend", observer := "weight-well-founded"
    left := "weight-natural-rational", right := "weight-ordinal"
    case := "A strictly descending chain of coefficients."
    leftVerdict := {
      reading := "Exists: the nonnegative rational weights 1/(n+1) descend forever. The natural \
        counts alone admit no such chain."
      evidence := [cites [``Weights.nonnegativeRat_descends]] }
    rightVerdict := {
      reading := "None: ordinal notations, and so checked priorities, admit no infinite strictly \
        descending chain."
      evidence := [cites [``Weights.priorities_no_infinite_descent]] } },
  { id := "min-plus-greatest-cost", observer := "weight-greatest-value"
    left := "weight-min-plus", right := "weight-ordinal"
    case := "A coefficient above every other in the algebra's order."
    leftVerdict := {
      reading := "Exists: infinity; the minimum of any cost with infinity is that cost."
      evidence := [cites [``Weights.minPlus_infinity_greatest]] }
    rightVerdict := {
      reading := "None: every checked priority has a strictly larger checked priority."
      evidence := [cites [``Weights.checked_priority_not_greatest]] } },
  { id := "min-plus-does-not-cancel", observer := "weight-cancellation"
    left := "weight-min-plus", right := "weight-complex-born"
    case := "Two contributions to one answer."
    leftVerdict := {
      reading := "No cancellation: the alternative of two costs is infinity, the identity of \
        alternatives, only when both are."
      evidence := [cites [``Weights.minPlus_alternative_eq_infinity_iff]] }
    rightVerdict := amplitudesCancel },
  { id := "amplitudes-no-zero-divisors", observer := "weight-zero-divisors"
    left := "weight-vectors-matrices", right := "weight-complex-born"
    case := "A product of two nonzero coefficients."
    leftVerdict := {
      reading := "Zero: two nonzero objective vectors multiply componentwise to zero."
      evidence := [cites [
        ``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.vector_zero_divisors]] }
    rightVerdict := {
      reading := "Never zero: a product of amplitudes is zero only when a factor is, since \
        amplitudes embed in the complex numbers."
      evidence := [cites [``Weights.amplitude_mul_eq_zero]] } },
  { id := "evidence-does-not-cancel", observer := "weight-cancellation"
    left := "weight-complex-born", right := "weight-pln-evidence"
    case := "Two contributions to one answer."
    leftVerdict := amplitudesCancel
    rightVerdict := {
      reading := "No cancellation: a sum of evidence counts is zero only when each summand is."
      evidence := [cites [``Weights.evidence_add_eq_zero]] } }
]

def witnesses : List Witness := [
  { id := "amplitudes-cancel", observer := "weight-cancellation"
    left := "weight-natural-rational", right := "weight-complex-born"
    case := "Two contributions to one answer, with coefficients 1 and its opposite where one exists."
    leftVerdict := {
      reading := "No cancellation: a sum of natural or nonnegative rational coefficients is zero \
        only when each is."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.nat_noCancellation,
        ``Mettapedia.GSLT.GradedSupport.nonnegative_rat_noCancellation]] }
    rightVerdict := {
      reading := "Cancellation: 1 and -1 add to zero while both occurrences remain, and the Born \
        readout of the total is refused."
      evidence := [cites [``Mettapedia.GSLT.Scope.WeightedReadout.cancellation_retains_occurrences,
        ``Mettapedia.Algebra.RationalComplexAmplitude.cancelled_readout_refused,
        ``Mettapedia.Algebra.RationalComplexAmplitude.born_not_additive]] } },
  { id := "booleans-do-not-cancel", observer := "weight-cancellation"
    left := "weight-boolean", right := "weight-complex-born"
    case := "Two histories reaching one state, with coefficients true and true, against 1 and -1."
    leftVerdict := {
      reading := "No cancellation: OR keeps the state reached; the xor ring, which would cancel, \
        is not this semiring."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.OrBool.noCancellation,
        ``Mettapedia.GSLT.GradedSupport.Control.orBool_keeps_sink,
        ``Mettapedia.GSLT.GradedSupport.Control.xor_deficit]] }
    rightVerdict := {
      reading := "Cancellation: the two contributions total zero, and both occurrences remain."
      evidence := [cites [``Mettapedia.GSLT.Scope.WeightedReadout.cancellation_retains_occurrences]] } },
  { id := "evidence-zero-divisors", observer := "weight-zero-divisors"
    left := "weight-natural-rational", right := "weight-pln-evidence"
    case := "A product of two nonzero coefficients."
    leftVerdict := {
      reading := "Never zero: natural numbers have no zero divisors."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.nat_noCancellation]] }
    rightVerdict := {
      reading := "Zero: purely positive and purely negative evidence tensor to zero."
      evidence := [cites [``Mettapedia.PLN.Evidence.exact_evidence_zero_divisors]] } },
  { id := "vector-zero-divisors", observer := "weight-zero-divisors"
    left := "weight-natural-rational", right := "weight-vectors-matrices"
    case := "A product of two nonzero coefficients."
    leftVerdict := {
      reading := "Never zero: natural numbers have no zero divisors."
      evidence := [cites [``Mettapedia.GSLT.GradedSupport.nat_noCancellation]] }
    rightVerdict := {
      reading := "Zero: two nonzero objective vectors multiply componentwise to zero."
      evidence := [cites [``Mettapedia.GSLT.Dynamics.WeightedResumptionControls.vector_zero_divisors]] } },
  { id := "law-does-not-fit", observer := "weight-pruning-law"
    left := "weight-natural-rational", right := "weight-min-plus"
    case := "The nonnegative-sum law, which licenses stopping once no pending alternative can do \
      better, declared for the algebra's sequencing."
    leftVerdict := {
      reading := "Does not fit: sequencing multiplies, and no superior combination is rational \
        multiplication; a search declaring the law for the multiplicative algebra is refused, \
        and the true best is still found."
      evidence := [cites [``Mettapedia.GSLT.Core.WeightOrderedSelection.rat_mul_not_superior],
        .fixture "weights-tree" "tests/prime/weights/law_breaking.metta" []] }
    rightVerdict := {
      reading := "Fits for nonnegative costs: adding them is a superior combination, and under a \
        superior law best-first selection finds the best."
      evidence := [cites [``Mettapedia.GSLT.Core.WeightOrderedSelection.natAdd,
        ``Mettapedia.GSLT.Core.WeightOrderedSelection.best_first_best_under_law]] } },
  { id := "descriptor-supplies-no-laws", observer := "weight-proved-laws"
    left := "weight-program-descriptor", right := "weight-min-plus"
    case := "The laws of the algebra's alternative and sequencing operations."
    leftVerdict := {
      reading := "Not supplied: two liftings of one aggregate disagree, and an operation named \
        addition need not be superior."
      evidence := [cites [``Mettapedia.GSLT.Scope.WeightedReadout.aggregate_liftings_disagree,
        ``Mettapedia.GSLT.Core.WeightOrderedSelection.intAdd_not_superior]] }
    rightVerdict := {
      reading := "Proved: both operations are associative and sequencing distributes over \
        alternatives."
      evidence := [cites [``Mettapedia.Algebra.TropicalCoefficient.alternative_associative,
        ``Mettapedia.Algebra.TropicalCoefficient.sequential_associative,
        ``Mettapedia.Algebra.TropicalCoefficient.sequential_distributes_left]] } }
]

/-- The local graph of this module. -/
def graph : Graph where
  documents := [report, descriptorLibrary]
  questions := [question]
  nodes := nodes
  arrows := arrows
  observers := observers
  witnesses := witnesses ++ surveyWitnesses ++ targetWitnesses

theorem graph_wellFormed : graph.wellFormed = true := by
  decide +kernel

theorem contracts_cited : graph.contractsCited = true := by
  decide +kernel

theorem quotients_honest : graph.quotientsHonest = true := by
  decide +kernel

theorem contracts_consistent : graph.contractsConsistent = true := by
  decide +kernel

/-- Every arrow claiming to forget a distinction records a counterexample. -/
theorem lossy_counterexampled : graph.lossyCounterexampled = true := by
  decide +kernel

/-- The witnesses proved for frontier targets rest on theorems only. -/
theorem targets_kernelChecked : targetWitnesses.all Witness.kernelChecked = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.WeightAlgebras
