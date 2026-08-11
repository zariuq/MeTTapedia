import Mettapedia.MachineLearning.ContinualLearning.QuadraticTwoTask

/-!
# Additive evidence ledgers and double counting

Gaussian precision and natural parameters are additive evidence coordinates.
This file proves that a correctly sequenced ledger is exactly additive and
that reusing one causal contribution leaves precisely one extra copy in both
coordinates.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

/-- Gaussian evidence in precision/natural-parameter coordinates. -/
structure GaussianEvidence (Index : Type*) where
  precision : Matrix Index Index ℝ
  naturalParameter : Index → ℝ

@[ext] theorem GaussianEvidence.extensionality {Index : Type*}
    {left right : GaussianEvidence Index}
    (hprecision : left.precision = right.precision)
    (hnatural : left.naturalParameter = right.naturalParameter) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Coordinatewise sum of independent evidence contributions. -/
noncomputable def GaussianEvidence.add {Index : Type*}
    (left right : GaussianEvidence Index) : GaussianEvidence Index where
  precision := left.precision + right.precision
  naturalParameter := left.naturalParameter + right.naturalParameter

/-- Append one evidence contribution to a ledger. -/
noncomputable def GaussianEvidence.update {Index : Type*}
    (ledger contribution : GaussianEvidence Index) : GaussianEvidence Index :=
  ledger.add contribution

theorem GaussianEvidence.add_assoc {Index : Type*}
    (first second third : GaussianEvidence Index) :
    (first.add second).add third = first.add (second.add third) := by
  apply GaussianEvidence.extensionality
  · ext i j
    change first.precision i j + second.precision i j + third.precision i j =
      first.precision i j + (second.precision i j + third.precision i j)
    exact _root_.add_assoc _ _ _
  · funext i
    change first.naturalParameter i + second.naturalParameter i +
      third.naturalParameter i = first.naturalParameter i +
        (second.naturalParameter i + third.naturalParameter i)
    exact _root_.add_assoc _ _ _

theorem GaussianEvidence.add_comm {Index : Type*}
    (first second : GaussianEvidence Index) :
    first.add second = second.add first := by
  apply GaussianEvidence.extensionality
  · ext i j
    change first.precision i j + second.precision i j =
      second.precision i j + first.precision i j
    exact _root_.add_comm _ _
  · funext i
    change first.naturalParameter i + second.naturalParameter i =
      second.naturalParameter i + first.naturalParameter i
    exact _root_.add_comm _ _

/-- Correct sequential bookkeeping is exactly the additive joint ledger. -/
theorem GaussianEvidence.sequential_update_eq_additive {Index : Type*}
    (prior first second : GaussianEvidence Index) :
    (prior.update first).update second = prior.add (first.add second) := by
  exact prior.add_assoc first second

/-- If the first contribution is reused, the resulting ledger is the correct
once-each ledger plus exactly one extra copy of that contribution. -/
theorem GaussianEvidence.reused_contribution_exact_excess {Index : Type*}
    (prior first second : GaussianEvidence Index) :
    ((prior.update first).update first).update second =
      (prior.update first).update (second.add first) := by
  cases prior
  cases first
  cases second
  simp [GaussianEvidence.update, GaussianEvidence.add]
  constructor <;> module

/-- Precision-coordinate form of the exact double-counting excess. -/
theorem GaussianEvidence.reused_precision_exact {Index : Type*}
    (prior first second : GaussianEvidence Index) :
    (((prior.update first).update first).update second).precision =
      ((prior.update first).update second).precision + first.precision := by
  simp [GaussianEvidence.update, GaussianEvidence.add]
  module

/-- Natural-parameter form of the exact double-counting excess. -/
theorem GaussianEvidence.reused_naturalParameter_exact {Index : Type*}
    (prior first second : GaussianEvidence Index) :
    (((prior.update first).update first).update second).naturalParameter =
      ((prior.update first).update second).naturalParameter +
        first.naturalParameter := by
  simp [GaussianEvidence.update, GaussianEvidence.add]
  module

/-! ## Distinct-event Gaussian aggregation

The additive coordinates above become an evidence valuation only after the
atomic event identity has been fixed.  A `Finset Event` makes deduplication at
that identity explicit; inclusion--exclusion then gives the exact correction
when two batches share events.
-/

/-- Aggregate one Gaussian contribution per distinct atomic event. -/
noncomputable def aggregateDistinctGaussian {Event Index : Type*}
    (events : Finset Event) (contribution : Event → GaussianEvidence Index) :
    GaussianEvidence Index where
  precision i j := ∑ event ∈ events, (contribution event).precision i j
  naturalParameter i := ∑ event ∈ events, (contribution event).naturalParameter i

/-- Gaussian evidence obeys inclusion--exclusion at the declared event
identity.  This is the additive analogue of overlap correction for counts. -/
theorem aggregateDistinctGaussian_inclusion_exclusion
    {Event Index : Type*} [DecidableEq Event]
    (left right : Finset Event) (contribution : Event → GaussianEvidence Index) :
    (aggregateDistinctGaussian (left ∪ right) contribution).add
        (aggregateDistinctGaussian (left ∩ right) contribution) =
      (aggregateDistinctGaussian left contribution).add
        (aggregateDistinctGaussian right contribution) := by
  apply GaussianEvidence.extensionality
  · ext i j
    simpa [aggregateDistinctGaussian, GaussianEvidence.add] using
      (Finset.sum_union_inter
        (s₁ := left) (s₂ := right)
        (f := fun event ↦ (contribution event).precision i j))
  · funext i
    simpa [aggregateDistinctGaussian, GaussianEvidence.add] using
      (Finset.sum_union_inter
        (s₁ := left) (s₂ := right)
        (f := fun event ↦ (contribution event).naturalParameter i))

/-- Disjoint event batches may be added without an overlap correction. -/
theorem aggregateDistinctGaussian_union_of_disjoint
    {Event Index : Type*} [DecidableEq Event]
    (left right : Finset Event) (contribution : Event → GaussianEvidence Index)
    (hdisjoint : Disjoint left right) :
    aggregateDistinctGaussian (left ∪ right) contribution =
      (aggregateDistinctGaussian left contribution).add
        (aggregateDistinctGaussian right contribution) := by
  apply GaussianEvidence.extensionality
  · ext i j
    simpa [aggregateDistinctGaussian, GaussianEvidence.add] using
      (Finset.sum_union hdisjoint
        (f := fun event ↦ (contribution event).precision i j))
  · funext i
    simpa [aggregateDistinctGaussian, GaussianEvidence.add] using
      (Finset.sum_union hdisjoint
        (f := fun event ↦ (contribution event).naturalParameter i))

noncomputable def zeroScalarEvidence : GaussianEvidence (Fin 1) where
  precision := 0
  naturalParameter := 0

noncomputable def unitScalarEvidence : GaussianEvidence (Fin 1) where
  precision := fun _ _ => 1
  naturalParameter := fun _ => 1

/-- Positive fixture: reusing unit scalar evidence adds one unit of precision
and one unit of natural parameter beyond once-each accounting. -/
theorem scalarEvidence_reuse_doubleCounting :
    (((zeroScalarEvidence.update unitScalarEvidence).update unitScalarEvidence).update
        zeroScalarEvidence).precision 0 0 = 2 ∧
      (((zeroScalarEvidence.update unitScalarEvidence).update unitScalarEvidence).update
        zeroScalarEvidence).naturalParameter = fun _ => 2 := by
  constructor
  ·
    norm_num [GaussianEvidence.update, GaussianEvidence.add,
      zeroScalarEvidence, unitScalarEvidence, Matrix.one_apply]
  · funext i
    fin_cases i
    norm_num [GaussianEvidence.update, GaussianEvidence.add,
      zeroScalarEvidence, unitScalarEvidence]

/-- Negative fixture: a zero contribution creates no accounting excess. -/
theorem zeroEvidence_reuse_has_no_excess :
    ((zeroScalarEvidence.update zeroScalarEvidence).update zeroScalarEvidence) =
      zeroScalarEvidence := by
  apply GaussianEvidence.extensionality
  · ext i j
    simp [GaussianEvidence.update, GaussianEvidence.add, zeroScalarEvidence]
  · funext i
    simp [GaussianEvidence.update, GaussianEvidence.add, zeroScalarEvidence]

/-- Status tags distinguish proved linear instances from the broader proposed
causal-coding correspondence. -/
inductive CausalCodingClaimStatus where
  | provedLinearTwoTask
  | conjecturalBeyondLinearRequiresInterventionalClamp
  deriving DecidableEq

/-- The general coupling-dilemma/causal-coding correspondence is retained as
a conjecture, and causal use requires an interventional clamp that removes the
intervened node's own residual mechanism.  Only the linear two-task statements
in this directory are claimed as theorems. -/
def generalCausalCodingCorrespondenceStatus : CausalCodingClaimStatus :=
  .conjecturalBeyondLinearRequiresInterventionalClamp

theorem generalCausalCodingCorrespondence_requires_interventionalClamp :
    generalCausalCodingCorrespondenceStatus =
      .conjecturalBeyondLinearRequiresInterventionalClamp := rfl

/-- Causal bridge crown: linear order interference, same-cause sequential
non-additivity, and exact ledger double counting are proved simultaneously,
without promoting the general correspondence beyond conjecture status. -/
theorem linearCausalCodingBridge :
    curvatureCommutator obliqueFirstTask obliqueSecondTask ≠ 0 ∧
      curvatureCommutator scalarUnitTask scalarUnitTask = 0 ∧
      sequentialTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter ≠
        additiveTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter ∧
      (((zeroScalarEvidence.update unitScalarEvidence).update unitScalarEvidence).update
        zeroScalarEvidence).precision 0 0 = 2 ∧
      generalCausalCodingCorrespondenceStatus =
        .conjecturalBeyondLinearRequiresInterventionalClamp :=
  ⟨linearTwoTask_causalCoding_separation.1,
    linearTwoTask_causalCoding_separation.2.2.1,
    linearTwoTask_causalCoding_separation.2.2.2,
    scalarEvidence_reuse_doubleCounting.1,
    generalCausalCodingCorrespondence_requires_interventionalClamp⟩

end Mettapedia.MachineLearning.ContinualLearning
