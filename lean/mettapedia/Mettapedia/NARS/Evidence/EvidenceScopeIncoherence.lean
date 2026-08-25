import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mettapedia.Evidence.SourceScoped
import Mettapedia.NARS.TruthFunctions

/-!
# Evidence-scope incoherence in NARS

Pei Wang, *Formalization of Evidence: A Comparative Study*, Journal of
Artificial General Intelligence 1 (2009), pp. 46--47, argues that NARS does
not maintain one coherent probability distribution over its statement space.
Each belief is evaluated from the evidence supplied along its inference path,
so the same statement may temporarily carry different truth values.  When the
underlying evidence bodies are distinct, revision combines them; when they
overlap, the choice rule selects one rather than double-counting their common
evidence.

This file isolates that claim without treating incoherence as arbitrary data:

* an `EvidencePath` retains both rule occurrences and source identifiers;
* a concrete direct path and a concrete deductive path reach the same statement
  with different NARS truth values;
* no semantics assigning one probability event to that statement can realize
  both frequencies simultaneously;
* `reconcile` revises exactly on disjoint scopes and otherwise chooses the
  more confident belief.

The last clause is an executable safeguard, not a claim that confidence choice
is the only possible overlap policy.  Wang describes higher-confidence choice
as the usual NARS policy; alternative policies can be studied above the same
scope distinction.
-/

namespace Mettapedia.NARS.Evidence.EvidenceScopeIncoherence

open MeasureTheory
open Mettapedia.NARS.TruthFunctions

universe uStatement uEvidence uSample

/-- Rule occurrences retained by an evidence path.  The statements stored in
the deduction occurrence are its two premises; the enclosing belief stores the
conclusion. -/
inductive InferenceStep (Statement : Type uStatement) where
  | observation (statement : Statement)
  | deduction (left right : Statement)
  | revision (statement : Statement)
  | choice (statement : Statement)
  deriving DecidableEq, Repr

/-- An inference history together with the finite set of evidence sources it
consulted.  Source identity, rather than merely source count, is what makes an
overlap check possible. -/
structure EvidencePath (Statement : Type uStatement) (EvidenceId : Type uEvidence)
    [DecidableEq EvidenceId] where
  steps : List (InferenceStep Statement)
  sources : Finset EvidenceId

/-- A NARS truth value attached to a statement through a retained evidence
path.  The evidence scope is derived from the path rather than duplicated in a
second field. -/
structure PathScopedBelief (Statement : Type uStatement) (EvidenceId : Type uEvidence)
    [DecidableEq EvidenceId] where
  statement : Statement
  truth : TV
  path : EvidencePath Statement EvidenceId

namespace PathScopedBelief

variable {Statement : Type uStatement} {EvidenceId : Type uEvidence}
  [DecidableEq EvidenceId]

/-- The finite evidence scope retained by a belief. -/
def scope (belief : PathScopedBelief Statement EvidenceId) : Finset EvidenceId :=
  belief.path.sources

/-- A path-scoped NARS belief exposes its retained evidence identifiers through
the system-independent source-scope interface. -/
instance instSourceScoped :
    Mettapedia.Evidence.SourceScoped
      (PathScopedBelief Statement EvidenceId) EvidenceId where
  sourceScope := scope

@[simp] theorem sourceScope_eq_scope
    (belief : PathScopedBelief Statement EvidenceId) :
    Mettapedia.Evidence.sourceScope belief = belief.scope := rfl

end PathScopedBelief

/-- A probability semantics that assigns one measurable event to each
statement.  This is deliberately a narrow target: the obstruction below says
that path-scoped NARS frequencies cannot all be read as one unique event
probability.  It does not say that an individual NARS truth value lacks a
probabilistic or evidence-count interpretation. -/
structure StatementProbabilityModel (Sample : Type uSample) (Statement : Type uStatement)
    [MeasurableSpace Sample] where
  probability : ProbabilityMeasure Sample
  event : Statement → Set Sample
  measurable_event : ∀ statement, MeasurableSet (event statement)

namespace StatementProbabilityModel

variable {Sample : Type uSample} {Statement : Type uStatement}
  {EvidenceId : Type uEvidence} [MeasurableSpace Sample] [DecidableEq EvidenceId]

/-- A model realizes a belief's frequency when the unique event assigned to
its statement has that probability. -/
def RealizesFrequency
    (model : StatementProbabilityModel Sample Statement)
    (belief : PathScopedBelief Statement EvidenceId) : Prop :=
  (((model.probability : Measure Sample) (model.event belief.statement)).toReal =
    belief.truth.f)

end StatementProbabilityModel

/-! ## A concrete two-path witness -/

namespace PathWitness

/-- Three atoms suffice for a direct `a → c` observation and a two-premise
deduction through `b`. -/
inductive Atom where
  | a | b | c
  deriving DecidableEq, Repr

abbrev Statement := Atom × Atom

def leftPremise : Statement := (.a, .b)
def rightPremise : Statement := (.b, .c)
def conclusion : Statement := (.a, .c)

/-- Both premises use the same simple probabilistically valid truth value. -/
noncomputable def premiseTruth : TV := ⟨1 / 2, 1 / 2⟩

/-- Direct evidence for the conclusion. -/
noncomputable def directTruth : TV := ⟨3 / 4, 1 / 2⟩

/-- The actual NARS deduction formula applied to the two premises. -/
noncomputable def deductiveTruth : TV := truthDeduction premiseTruth premiseTruth

def directPath : EvidencePath Statement (Fin 3) where
  steps := [.observation conclusion]
  sources := {0}

def deductivePath : EvidencePath Statement (Fin 3) where
  steps := [.observation leftPremise, .observation rightPremise,
    .deduction leftPremise rightPremise]
  sources := {1, 2}

def overlappingDeductivePath : EvidencePath Statement (Fin 3) where
  steps := [.observation leftPremise, .observation rightPremise,
    .deduction leftPremise rightPremise]
  sources := {0, 2}

noncomputable def directBelief : PathScopedBelief Statement (Fin 3) where
  statement := conclusion
  truth := directTruth
  path := directPath

noncomputable def deductiveBelief : PathScopedBelief Statement (Fin 3) where
  statement := conclusion
  truth := deductiveTruth
  path := deductivePath

noncomputable def overlappingDeductiveBelief : PathScopedBelief Statement (Fin 3) where
  statement := conclusion
  truth := deductiveTruth
  path := overlappingDeductivePath

theorem same_statement :
    directBelief.statement = deductiveBelief.statement := rfl

theorem distinct_paths :
    directBelief.path.steps ≠ deductiveBelief.path.steps := by
  decide

theorem disjoint_scopes :
    Disjoint directBelief.scope deductiveBelief.scope := by
  decide

theorem overlapping_scopes :
    ¬ Disjoint directBelief.scope overlappingDeductiveBelief.scope := by
  decide

theorem direct_frequency_ne_deductive_frequency :
    directBelief.truth.f ≠ deductiveBelief.truth.f := by
  norm_num [directBelief, directTruth, deductiveBelief, deductiveTruth,
    premiseTruth, truthDeduction]

theorem direct_truth_ne_deductive_truth :
    directBelief.truth ≠ deductiveBelief.truth := by
  intro equality
  exact direct_frequency_ne_deductive_frequency (congrArg TV.f equality)

/-- Wang's path-dependent witness obstructs every reading that assigns a
single probability event to the conclusion and identifies its probability
with both path frequencies. -/
theorem no_single_event_probability_realizes_both
    {Sample : Type uSample} [MeasurableSpace Sample]
    (model : StatementProbabilityModel Sample Statement) :
    ¬ (model.RealizesFrequency directBelief ∧
      model.RealizesFrequency deductiveBelief) := by
  rintro ⟨hdirect, hdeductive⟩
  unfold StatementProbabilityModel.RealizesFrequency at hdirect hdeductive
  rw [← same_statement] at hdeductive
  apply direct_frequency_ne_deductive_frequency
  exact hdirect.symm.trans hdeductive

end PathWitness

/-! ## Revision versus choice -/

namespace Resolution

variable {Statement : Type uStatement} {EvidenceId : Type uEvidence}
  [DecidableEq EvidenceId]

open Mettapedia.Evidence

/-- Two path-scoped beliefs about the same statement. -/
structure CompetingBeliefs where
  left : PathScopedBelief Statement EvidenceId
  right : PathScopedBelief Statement EvidenceId
  same_statement : left.statement = right.statement

/-- The two evidence bodies may be added exactly when their retained source
sets are disjoint. -/
def CompetingBeliefs.RevisionLicensed
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId)) : Prop :=
  SourceScoped.Independent beliefs.left beliefs.right

/-- Resolution remembers whether the operation was additive revision or
non-additive choice. -/
inductive EvidenceResolution where
  | revised (belief : PathScopedBelief Statement EvidenceId)
  | chosen (belief : PathScopedBelief Statement EvidenceId)

/-- Add two distinct evidence bodies using the unclamped evidence-additive
revision core.  The caller supplies the source-disjointness receipt. -/
noncomputable def revise
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId))
    (_licensed : beliefs.RevisionLicensed) : PathScopedBelief Statement EvidenceId where
  statement := beliefs.left.statement
  truth := truthRevisionCore beliefs.left.truth beliefs.right.truth
  path :=
    { steps := beliefs.left.path.steps ++ beliefs.right.path.steps ++
        [.revision beliefs.left.statement]
      sources := SourceScope.merge beliefs.left.scope beliefs.right.scope }

/-- The usual NARS overlap policy: retain the belief with greater confidence.
Ties retain the left occurrence, making the operation deterministic while
preserving one original evidence body rather than manufacturing a sum. -/
noncomputable def chooseMoreConfident
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId)) :
    PathScopedBelief Statement EvidenceId :=
  if beliefs.left.truth.c < beliefs.right.truth.c then beliefs.right else beliefs.left

/-- Reconcile two beliefs without double-counting: revise disjoint evidence
bodies and use choice when their scopes overlap. -/
noncomputable def reconcile
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId)) :
    EvidenceResolution (Statement := Statement) (EvidenceId := EvidenceId) :=
  @dite (EvidenceResolution (Statement := Statement) (EvidenceId := EvidenceId))
    beliefs.RevisionLicensed (Classical.propDecidable _)
    (fun licensed => .revised (revise beliefs licensed))
    (fun _overlap => .chosen (chooseMoreConfident beliefs))

theorem reconcile_eq_revised_of_disjoint
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId))
    (licensed : beliefs.RevisionLicensed) :
    reconcile beliefs = .revised (revise beliefs licensed) := by
  simp [reconcile, licensed]

theorem reconcile_eq_chosen_of_overlap
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId))
    (overlap : ¬ beliefs.RevisionLicensed) :
    reconcile beliefs = .chosen (chooseMoreConfident beliefs) := by
  simp [reconcile, overlap]

@[simp] theorem revise_scope
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId))
    (licensed : beliefs.RevisionLicensed) :
    (revise beliefs licensed).scope =
      SourceScope.merge beliefs.left.scope beliefs.right.scope := rfl

@[simp] theorem revise_truth
    (beliefs : CompetingBeliefs (Statement := Statement) (EvidenceId := EvidenceId))
    (licensed : beliefs.RevisionLicensed) :
    (revise beliefs licensed).truth =
      truthRevisionCore beliefs.left.truth beliefs.right.truth := rfl

end Resolution

namespace PathWitness

open Resolution

noncomputable def independentCompetition :
    CompetingBeliefs (Statement := PathWitness.Statement) (EvidenceId := Fin 3) where
  left := directBelief
  right := deductiveBelief
  same_statement := rfl

noncomputable def overlappingCompetition :
    CompetingBeliefs (Statement := PathWitness.Statement) (EvidenceId := Fin 3) where
  left := directBelief
  right := overlappingDeductiveBelief
  same_statement := rfl

theorem independent_competition_revises :
    ∃ licensed : independentCompetition.RevisionLicensed,
      reconcile independentCompetition =
        .revised (revise independentCompetition licensed) := by
  have licensed : independentCompetition.RevisionLicensed := by
    simpa [independentCompetition, CompetingBeliefs.RevisionLicensed,
      Mettapedia.Evidence.SourceScoped.Independent,
      Mettapedia.Evidence.SourceScope.Independent] using disjoint_scopes
  exact ⟨licensed, reconcile_eq_revised_of_disjoint independentCompetition licensed⟩

theorem overlapping_competition_chooses_direct :
    reconcile overlappingCompetition = .chosen directBelief := by
  have overlap : ¬ overlappingCompetition.RevisionLicensed := by
    simpa [overlappingCompetition, CompetingBeliefs.RevisionLicensed,
      Mettapedia.Evidence.SourceScoped.Independent,
      Mettapedia.Evidence.SourceScope.Independent] using overlapping_scopes
  rw [reconcile_eq_chosen_of_overlap overlappingCompetition overlap]
  norm_num [chooseMoreConfident, overlappingCompetition, directBelief, directTruth,
    overlappingDeductiveBelief, deductiveTruth, premiseTruth, truthDeduction]

end PathWitness

#print axioms PathWitness.no_single_event_probability_realizes_both
#print axioms PathWitness.independent_competition_revises
#print axioms PathWitness.overlapping_competition_chooses_direct

end Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
