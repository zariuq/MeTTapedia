import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.WorldModel.Generative

/-!
# Gibbs completions as residual world-model realizations

An infinite Gibbs/MLN specification may have several sigma-additive DLR
completions.  This file treats a completion as residual boundary data for a
single relational generative model.  A finite-query probability is stable
exactly when it does not depend on that residual choice.

The positive bridge reuses Dobrushin uniqueness: uniform small total influence
makes every finite-query observation stable.  The negative bridge reuses
strict DLR width: two completions then witness an observation leak.

This is a probabilistic residual-stability result.  It is not identified with
algorithmic independence of a residual parameter; connecting those notions
requires a separate algorithmic-information theorem.
-/

namespace Mettapedia.Logic.WorldModel.GibbsCompletion

open MeasureTheory
open scoped ENNReal

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.WorldModel.Generative

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A DLR completion is residual data; its underlying probability measure is
the realized world. -/
def completionSemantics
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    Semantics Unit (DLRCompletion M)
      (ProbabilityMeasure (InfiniteWorld Atom)) where
  admissible := fun _ _ => True
  realizes := fun _ residual world => world = residual.1
  realizes_admissible := by simp

theorem completionSemantics_productive
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    Productive (completionSemantics M) () := by
  intro residual _
  exact ⟨residual.1, rfl⟩

/-- The probability of a finite query, observed directly from a realized
probability measure. -/
noncomputable def queryObservation
    (q : ConstraintQuery Atom)
    (world : ProbabilityMeasure (InfiniteWorld Atom)) : ℝ :=
  ENNReal.toReal
    ((world : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q))

theorem queryObservation_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (completion : DLRCompletion M) :
    queryObservation q completion.1 =
      dlrCompletionQueryProb M q completion := by
  symm
  exact dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent M q completion

/-- Query determination is exactly observation stability of the generative
completion semantics. -/
theorem queryObservation_stable_iff_determined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    ObservationStable (completionSemantics M) () (queryObservation q) ↔
      dlrQueryDetermined M q := by
  constructor
  · intro stable μ ν
    have h := stable (leftResidual := μ) (rightResidual := ν)
      (leftWorld := μ.1) (rightWorld := ν.1) rfl rfl
    simpa [queryObservation_completion] using h
  · intro determined leftResidual rightResidual leftWorld rightWorld
      realizesLeft realizesRight
    subst leftWorld
    subst rightWorld
    simpa [queryObservation_completion] using
      determined leftResidual rightResidual

/-- When the DLR completion family is inhabited, a finite query is determined
exactly when the MLN specification entails one exact probability for that
query.  This is the completion-semantics instance of the generic
stable-observation/entailed-outcome equivalence. -/
theorem queryDetermined_iff_exists_entails_queryObservation_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    dlrQueryDetermined M q ↔
      ∃ value : ℝ,
        Entails (completionSemantics M) ()
          (fun world => queryObservation q world = value) := by
  have inhabited : HasAnyRealization (completionSemantics M) () := by
    obtain ⟨base⟩ := (inferInstance : Nonempty (DLRCompletion M))
    exact ⟨base, base.1, rfl⟩
  rw [← queryObservation_stable_iff_determined]
  exact observationStable_iff_exists_entails_eq inhabited

/-- Dobrushin uniqueness makes each finite-query observation insensitive to
the selected DLR completion. -/
theorem queryObservation_stable_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) :
    ObservationStable (completionSemantics M) () (queryObservation q) := by
  exact (queryObservation_stable_iff_determined M q).2
    (dlrQueryDetermined_of_uniform M hM q)

/-- With a chosen completion as witness, uniform Dobrushin uniqueness yields
an ordinary world-model consequence: every realization has its query value. -/
theorem entails_queryObservation_eq_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) (base : DLRCompletion M) :
    Entails (completionSemantics M) ()
      (fun world => queryObservation q world = queryObservation q base.1) := by
  intro residual world realizesWorld
  subst world
  exact queryObservation_stable_of_uniform M hM q
    (leftResidual := residual) (rightResidual := base)
    (leftWorld := residual.1) (rightWorld := base.1) rfl rfl

/-- Dobrushin uniqueness yields an exact query outcome entailed by the
specification, without requiring callers to choose which completion supplies
the value. -/
theorem exists_entails_queryObservation_eq_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) :
    ∃ value : ℝ,
      Entails (completionSemantics M) ()
        (fun world => queryObservation q world = value) := by
  exact (queryDetermined_iff_exists_entails_queryObservation_eq M q).1
    (dlrQueryDetermined_of_uniform M hM q)

/-- Strict DLR width is a concrete residual leak in the generative semantics. -/
theorem queryObservation_leaks_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ObservationLeaks (completionSemantics M) () (queryObservation q) := by
  obtain ⟨μ, ν, hμν⟩ := hWidth
  refine ⟨μ, ν, μ.1, ν.1, rfl, rfl, ?_⟩
  rw [queryObservation_completion, queryObservation_completion]
  exact ne_of_lt hμν

/-- Strict credal width and residual leakage are exactly the same condition at
the finite-query observation. -/
theorem queryObservation_leaks_iff_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    ObservationLeaks (completionSemantics M) () (queryObservation q) ↔
      dlrQueryHasStrictWidth M q := by
  constructor
  · rintro ⟨leftResidual, rightResidual, leftWorld, rightWorld,
      realizesLeft, realizesRight, differs⟩
    subst leftWorld
    subst rightWorld
    rw [queryObservation_completion, queryObservation_completion] at differs
    rcases lt_or_gt_of_ne differs with hlt | hgt
    · exact ⟨leftResidual, rightResidual, hlt⟩
    · exact ⟨rightResidual, leftResidual, hgt⟩
  · exact queryObservation_leaks_of_strictWidth M q

theorem queryObservation_not_stable_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ¬ ObservationStable (completionSemantics M) () (queryObservation q) :=
  observationLeaks_not_stable
    (queryObservation_leaks_of_strictWidth M q hWidth)

/-- Strict DLR width rules out every exact query value being entailed by the
specification.  Thus the positive theorem above genuinely depends on a
completion-stability premise. -/
theorem not_exists_entails_queryObservation_eq_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ¬ ∃ value : ℝ,
      Entails (completionSemantics M) ()
        (fun world => queryObservation q world = value) := by
  intro contained
  exact queryObservation_not_stable_of_strictWidth M q hWidth
    (observationStable_of_exists_entails_eq contained)

#print axioms queryObservation_stable_iff_determined
#print axioms queryDetermined_iff_exists_entails_queryObservation_eq
#print axioms queryObservation_stable_of_uniform
#print axioms entails_queryObservation_eq_of_uniform
#print axioms exists_entails_queryObservation_eq_of_uniform
#print axioms queryObservation_leaks_iff_strictWidth
#print axioms queryObservation_not_stable_of_strictWidth
#print axioms not_exists_entails_queryObservation_eq_of_strictWidth

end Mettapedia.Logic.WorldModel.GibbsCompletion
