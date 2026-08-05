import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EncoderEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.GridRelationSymmetry

/-!
# Exact symmetry boundary for relation-masked softmax

A finite relation can be used as the source-dependent mask of a uniform-score
softmax read.  A coordinate permutation commutes with every such read exactly
when it preserves and reflects the relation.  The converse is witnessed by a
coordinate basis vector: a related target receives strictly positive softmax
mass, whereas an unrelated target receives exactly zero mass.

This provides a nonlinear counterpart to the zero-one linear relation-kernel
classification.  It is reusable infrastructure for structured weight-space
attention, but it does not by itself formalize the complete slice-attention
equations of a Neural Functional Transformer.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

section RelationSoftmax

variable {Coordinate : Type*}

/-- The Boolean mask selecting the targets related to one source. -/
def relationRowActive
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (source target : Coordinate) : Bool :=
  decide (relation source target)

/-- A uniform-score softmax average over the targets related to `source`.
An empty relation row evaluates to zero under the ambient field convention. -/
noncomputable def relationSoftmaxAverage
    [Fintype Coordinate]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (values : Coordinate → ℝ) (source : Coordinate) : ℝ :=
  attentionRead
    (relationRowActive relation source)
    (fun _ _ => 0)
    (fun _ _ => 1)
    values
    source

/-- Equivariance of every scalar relation-softmax read under one coordinate
permutation. -/
def RelationSoftmaxEquivariant
    [Fintype Coordinate]
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation] : Prop :=
  ∀ values source,
    relationSoftmaxAverage relation
        (transportRows permutation values) (permutation source) =
      relationSoftmaxAverage relation values source

theorem relationRowActive_transport
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (preserves : EquivPreservesRelation permutation relation)
    (source target : Coordinate) :
    relationRowActive relation (permutation source) (permutation target) =
      relationRowActive relation source target := by
  simp only [relationRowActive, decide_eq_decide]
  exact preserves source target

/-- A preserved relation makes every relation-masked softmax average commute
with coordinate transport. -/
theorem preservesRelation_implies_relationSoftmaxEquivariant
    [Fintype Coordinate]
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (preserves : EquivPreservesRelation permutation relation) :
    RelationSoftmaxEquivariant permutation relation := by
  intro values source
  have activeEq :
      relationRowActive relation (permutation source) =
        transportRows permutation (relationRowActive relation source) := by
    funext transportedTarget
    obtain ⟨target, rfl⟩ := permutation.surjective transportedTarget
    simp [transportRows,
      relationRowActive_transport permutation relation preserves source target]
  unfold relationSoftmaxAverage
  rw [activeEq]
  have scoreEq :
      transportPairs permutation (fun _ _ => (0 : ℝ)) =
        (fun _ _ => (0 : ℝ)) := by
    funext source' target'
    rfl
  have multiplierEq :
      transportPairs permutation (fun _ _ => (1 : ℝ)) =
        (fun _ _ => (1 : ℝ)) := by
    funext source' target'
    rfl
  simpa only [scoreEq, multiplierEq] using
    (attentionRead_transport permutation
      (relationRowActive relation source)
      (fun _ _ => (0 : ℝ))
      (fun _ _ => (1 : ℝ))
      values source)

theorem relationSoftmaxAverage_basis
    [Fintype Coordinate] [DecidableEq Coordinate]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (source target : Coordinate) :
    relationSoftmaxAverage relation
        (basisVector (R := ℝ) target) source =
      maskedSoftmaxWeight
        (relationRowActive relation source)
        (fun _ _ => 0)
        source target := by
  simp [relationSoftmaxAverage, attentionRead, basisVector]

/-- A related target receives strictly positive mass. -/
theorem relationSoftmaxWeight_pos
    [Fintype Coordinate]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (source target : Coordinate)
    (related : relation source target) :
    0 <
      maskedSoftmaxWeight
        (relationRowActive relation source)
        (fun _ _ => 0)
        source target := by
  have targetActive :
      relationRowActive relation source target = true := by
    simp [relationRowActive, related]
  have nonempty :
      ∃ candidate, relationRowActive relation source candidate = true :=
    ⟨target, targetActive⟩
  unfold maskedSoftmaxWeight
  apply div_pos
  · simp [maskedExpKernel, targetActive]
  · exact
      maskedNormalizer_positive
        (relationRowActive relation source)
        (fun _ _ => 0)
        source nonempty

/-- An unrelated target receives exactly zero mass. -/
theorem relationSoftmaxWeight_eq_zero
    [Fintype Coordinate]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (source target : Coordinate)
    (unrelated : ¬ relation source target) :
    maskedSoftmaxWeight
        (relationRowActive relation source)
        (fun _ _ => 0)
        source target = 0 := by
  apply maskedSoftmaxWeight_inactive
  simp [relationRowActive, unrelated]

theorem transportRows_basisVector
    [DecidableEq Coordinate]
    (permutation : Equiv.Perm Coordinate)
    (target : Coordinate) :
    transportRows permutation (basisVector (R := ℝ) target) =
      basisVector (R := ℝ) (permutation target) := by
  funext candidate
  simp [transportRows, basisVector, Equiv.symm_apply_eq]

/-- If every relation-softmax average commutes with a permutation, then the
permutation must preserve and reflect the masking relation. -/
theorem relationSoftmaxEquivariant_implies_preservesRelation
    [Fintype Coordinate] [DecidableEq Coordinate]
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (equivariant : RelationSoftmaxEquivariant permutation relation) :
    EquivPreservesRelation permutation relation := by
  intro source target
  have equality :=
    equivariant (basisVector (R := ℝ) target) source
  rw [transportRows_basisVector permutation target] at equality
  rw [relationSoftmaxAverage_basis, relationSoftmaxAverage_basis] at equality
  constructor
  · intro transportedRelated
    by_contra originalRelated
    have transportedPositive :=
      relationSoftmaxWeight_pos relation
        (permutation source) (permutation target) transportedRelated
    have originalZero :=
      relationSoftmaxWeight_eq_zero relation source target originalRelated
    rw [originalZero] at equality
    linarith
  · intro originalRelated
    by_contra transportedRelated
    have originalPositive :=
      relationSoftmaxWeight_pos relation source target originalRelated
    have transportedZero :=
      relationSoftmaxWeight_eq_zero relation
        (permutation source) (permutation target) transportedRelated
    rw [transportedZero] at equality
    linarith

/-- Exact nonlinear symmetry boundary for a relation-masked softmax read. -/
theorem relationSoftmaxEquivariant_iff_preservesRelation
    [Fintype Coordinate] [DecidableEq Coordinate]
    (permutation : Equiv.Perm Coordinate)
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation] :
    RelationSoftmaxEquivariant permutation relation ↔
      EquivPreservesRelation permutation relation :=
  ⟨relationSoftmaxEquivariant_implies_preservesRelation
      permutation relation,
    preservesRelation_implies_relationSoftmaxEquivariant
      permutation relation⟩

end RelationSoftmax

namespace RelationSoftmaxFixtures

open GridRelationFixtures

/-- A genuine row/column product permutation preserves the nonlinear
same-row softmax read. -/
theorem productSwap_softmax_equivariant :
    RelationSoftmaxEquivariant productSwap
      (SameFirst (Row := Fin 2) (Column := Fin 2)) :=
  preservesRelation_implies_relationSoftmaxEquivariant
    productSwap SameFirst productSwap_preserves_grid.1

/-- A column-dependent row exchange fails the same nonlinear equivariance
test. -/
theorem partialRowSwap_not_softmax_equivariant :
    ¬ RelationSoftmaxEquivariant partialRowSwap
      (SameFirst (Row := Fin 2) (Column := Fin 2)) := by
  intro equivariant
  exact partialRowSwap_does_not_preserve_rows
    ((relationSoftmaxEquivariant_iff_preservesRelation
      partialRowSwap SameFirst).1 equivariant)

end RelationSoftmaxFixtures

#print axioms relationSoftmaxEquivariant_iff_preservesRelation
#print axioms RelationSoftmaxFixtures.productSwap_softmax_equivariant
#print axioms RelationSoftmaxFixtures.partialRowSwap_not_softmax_equivariant

end

end Mettapedia.MachineLearning.NeuralNetworks
