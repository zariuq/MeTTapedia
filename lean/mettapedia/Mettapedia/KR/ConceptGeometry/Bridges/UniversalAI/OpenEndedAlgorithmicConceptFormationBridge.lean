import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConceptFormationBridge

/-!
# Open-ended algorithmic concept formation

An open-ended learner does not receive a once-for-all domain of worlds.  It
observes a monotone family of source sets.  At each stage, strict executable
features induce a formal concept relative to the observations available at
that stage.

The transport laws are deliberately one-sided:

* observed feature instances persist as the source set grows;
* provisional feature implications can disappear when a new counterexample is
  observed; and
* a global strict implication restricts to every stage, but no finite-stage
  implication is promoted back to a global one without a separate proof.

This is the open-world boundary.  The stage index supplies a forward diagram
of evidence, while concept intents vary contravariantly with added sources.
-/

namespace Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.OpenEndedAlgorithmicConceptFormation

open scoped Classical

open KolmogorovComplexity
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureInheritance
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureConceptFormation
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.FeatureContainment

universe uStage

/-- A monotone family of observed source sets for one conditional algorithm. -/
structure StagewiseFeatureContext (Stage : Type uStage) [Preorder Stage] where
  algorithm : ConditionalAlgorithm
  observed : Stage → Set BinString
  observed_mono : Monotone observed

namespace StagewiseFeatureContext

variable {Stage : Type uStage} [Preorder Stage]

/-- Stage-local incidence: the source has been observed and exhibits the
feature strictly. -/
def relation (C : StagewiseFeatureContext Stage)
    (stage : Stage) (source feature : BinString) : Prop :=
  source ∈ C.observed stage ∧ StrictFeatureOf C.algorithm feature source

/-- Implication relative to the sources observed at one stage. -/
def ImplicationAt (C : StagewiseFeatureContext Stage)
    (stage : Stage) (premise consequent : BinString) : Prop :=
  ∀ ⦃source⦄, C.relation stage source premise →
    C.relation stage source consequent

theorem implicationAt_refl
    (C : StagewiseFeatureContext Stage) (stage : Stage) (feature : BinString) :
    C.ImplicationAt stage feature feature := by
  intro source featureOfSource
  exact featureOfSource

theorem implicationAt_trans
    (C : StagewiseFeatureContext Stage) (stage : Stage)
    {first second third : BinString}
    (h₁₂ : C.ImplicationAt stage first second)
    (h₂₃ : C.ImplicationAt stage second third) :
    C.ImplicationAt stage first third := by
  intro source featureOfSource
  exact h₂₃ (h₁₂ featureOfSource)

/-- The stage-relative feature concept: observed instances paired with their
current common strict-feature theory. -/
def conceptAt (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature : BinString) : DualConcept BinString BinString where
  extent := {source | C.relation stage source feature}
  intent := {consequent | C.ImplicationAt stage feature consequent}

@[simp]
theorem mem_conceptAt_extent_iff
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature source : BinString) :
    source ∈ (C.conceptAt stage feature).extent ↔
      C.relation stage source feature :=
  Iff.rfl

@[simp]
theorem mem_conceptAt_intent_iff
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature consequent : BinString) :
    consequent ∈ (C.conceptAt stage feature).intent ↔
      C.ImplicationAt stage feature consequent :=
  Iff.rfl

theorem upperPolar_conceptAt_extent
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature : BinString) :
    _root_.upperPolar (C.relation stage) (C.conceptAt stage feature).extent =
      (C.conceptAt stage feature).intent := by
  ext consequent
  rfl

theorem lowerPolar_conceptAt_intent
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature : BinString) :
    _root_.lowerPolar (C.relation stage) (C.conceptAt stage feature).intent =
      (C.conceptAt stage feature).extent := by
  ext source
  constructor
  · intro satisfiesTheory
    exact satisfiesTheory (C.implicationAt_refl stage feature)
  · intro featureOfSource consequent implication
    exact implication featureOfSource

/-- Every stage-relative feature concept is a genuine formal concept. -/
theorem conceptAt_isClosed
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature : BinString) :
    DualConcept.IsClosed (C.relation stage) (C.conceptAt stage feature) :=
  ⟨C.upperPolar_conceptAt_extent stage feature,
    C.lowerPolar_conceptAt_intent stage feature⟩

/-- Formal-concept realization of one provisional stage-relative concept. -/
def formalConceptAt
    (C : StagewiseFeatureContext Stage)
    (stage : Stage) (feature : BinString) :
    _root_.Concept BinString BinString (C.relation stage) :=
  DualConcept.toConcept (C.conceptAt stage feature)
    (C.conceptAt_isClosed stage feature)

/-- Observed feature instances persist along the forward stage order. -/
theorem relation_mono
    (C : StagewiseFeatureContext Stage) {earlier later : Stage}
    (hstage : earlier ≤ later) {source feature : BinString}
    (h : C.relation earlier source feature) :
    C.relation later source feature :=
  ⟨C.observed_mono hstage h.1, h.2⟩

/-- Extents grow monotonically with observations. -/
theorem conceptAt_extent_mono
    (C : StagewiseFeatureContext Stage) {earlier later : Stage}
    (hstage : earlier ≤ later) (feature : BinString) :
    (C.conceptAt earlier feature).extent ⊆
      (C.conceptAt later feature).extent :=
  fun _ h => C.relation_mono hstage h

/-- A consequence surviving a later, larger source set was already valid at
every earlier stage. -/
theorem implicationAt_anti
    (C : StagewiseFeatureContext Stage) {earlier later : Stage}
    (hstage : earlier ≤ later) {premise consequent : BinString}
    (h : C.ImplicationAt later premise consequent) :
    C.ImplicationAt earlier premise consequent := by
  intro source featureOfSource
  have laterPremise := C.relation_mono hstage featureOfSource
  exact ⟨featureOfSource.1, (h laterPremise).2⟩

/-- Intents shrink contravariantly as new sources are observed. -/
theorem conceptAt_intent_anti
    (C : StagewiseFeatureContext Stage) {earlier later : Stage}
    (hstage : earlier ≤ later) (feature : BinString) :
    (C.conceptAt later feature).intent ⊆
      (C.conceptAt earlier feature).intent :=
  fun _ h => C.implicationAt_anti hstage h

/-- A globally proved strict implication is valid in every observed stage. -/
theorem implicationAt_of_strictFeatureImplication
    (C : StagewiseFeatureContext Stage) (stage : Stage)
    {premise consequent : BinString}
    (h : StrictFeatureImplication C.algorithm premise consequent) :
    C.ImplicationAt stage premise consequent := by
  intro source featureOfPremise
  obtain ⟨observed, certificate, realizesPremise⟩ := featureOfPremise
  exact ⟨observed, h certificate source realizesPremise⟩

end StagewiseFeatureContext

/-! ## Strict-growth canary -/

/-- The canonical context indexed directly by observed source sets. -/
def sourceSetFeatureContext (U : ConditionalAlgorithm) :
    StagewiseFeatureContext (Set BinString) where
  algorithm := U
  observed := id
  observed_mono := monotone_id

theorem shortGenerator_not_strictFeatureOf_empty :
    ¬ StrictFeatureOf imageCompressionAlgorithm [false] [] := by
  rintro ⟨certificate, _extracts, reconstructs, _compresses⟩
  by_cases residualEmpty : certificate.residual = []
  · simp [imageCompressionAlgorithm, residualEmpty, fourTrue] at reconstructs
  · simp [imageCompressionAlgorithm, residualEmpty, fourTrue] at reconstructs

def earlySourceSet : Set BinString := {[]}

def laterSourceSet : Set BinString := {[], fourTrue}

theorem earlySourceSet_subset_laterSourceSet :
    earlySourceSet ⊆ laterSourceSet := by
  intro source hsource
  simp [earlySourceSet] at hsource
  subst source
  simp [laterSourceSet]

/-- Before a premise instance has appeared, a relative implication may hold
without establishing any global semantic relation. -/
theorem early_short_implies_long :
    (sourceSetFeatureContext imageCompressionAlgorithm).ImplicationAt
      earlySourceSet [false] fourTrue := by
  intro source featureOfPremise
  have sourceEmpty : source = [] := by
    simpa [sourceSetFeatureContext, earlySourceSet,
      StagewiseFeatureContext.relation] using featureOfPremise.1
  subst source
  exact (shortGenerator_not_strictFeatureOf_empty featureOfPremise.2).elim

/-- Adding the witnessed counterexample retracts the provisional implication. -/
theorem later_not_short_implies_long :
    ¬ (sourceSetFeatureContext imageCompressionAlgorithm).ImplicationAt
      laterSourceSet [false] fourTrue := by
  intro implication
  have premiseAtFourTrue :
      (sourceSetFeatureContext imageCompressionAlgorithm).relation
        laterSourceSet fourTrue [false] := by
    exact ⟨by simp [sourceSetFeatureContext, laterSourceSet],
      shortGenerator_strictFeature⟩
  exact longGenerator_not_strictFeature (implication premiseAtFourTrue).2

/-- Concrete open-world boundary: source growth preserves instances but can
invalidate a provisional intent member. -/
theorem strict_source_growth_revises_intension :
    earlySourceSet ⊆ laterSourceSet ∧
      (sourceSetFeatureContext imageCompressionAlgorithm).ImplicationAt
        earlySourceSet [false] fourTrue ∧
      ¬ (sourceSetFeatureContext imageCompressionAlgorithm).ImplicationAt
        laterSourceSet [false] fourTrue :=
  ⟨earlySourceSet_subset_laterSourceSet,
    early_short_implies_long,
    later_not_short_implies_long⟩

/-- Consequently, stage-local implication has no uniform promotion to global
strict implication, even when the source stage is nonempty. -/
theorem no_uniform_implicationAt_to_strictFeatureImplication :
    ¬ (∀ (U : ConditionalAlgorithm) (sources : Set BinString)
        (premise consequent : BinString),
      sources.Nonempty →
      (sourceSetFeatureContext U).ImplicationAt sources premise consequent →
      StrictFeatureImplication U premise consequent) := by
  intro promote
  have promoted := promote imageCompressionAlgorithm earlySourceSet
    [false] fourTrue (by exact ⟨[], by simp [earlySourceSet]⟩)
    early_short_implies_long
  exact imageInclusion_does_not_imply_strictFeatureImplication.2.2 promoted

#print axioms StagewiseFeatureContext.conceptAt_isClosed
#print axioms StagewiseFeatureContext.conceptAt_extent_mono
#print axioms StagewiseFeatureContext.conceptAt_intent_anti
#print axioms StagewiseFeatureContext.implicationAt_of_strictFeatureImplication
#print axioms shortGenerator_not_strictFeatureOf_empty
#print axioms strict_source_growth_revises_intension
#print axioms no_uniform_implicationAt_to_strictFeatureImplication

end Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.OpenEndedAlgorithmicConceptFormation
