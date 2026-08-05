import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting

/-!
# Exact invariance boundary for capped corpus views

The raw checker-backed ledger is immutable.  A capped view is safe for a
statistic only when its retained representatives are sufficient to recompute
that statistic.  This file proves both directions of that boundary for
shortest, fastest, and Pareto summaries, proves target coverage and target
exclusivity from coverage completeness, and supplies explicit counterexamples
for witness counts and program diversity.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT uM uA uW uL

section FiniteSelection

variable {Program : Type uP} {Target : Type uT}

/-- Restricting a solve relation cannot add a witness for a target. -/
theorem programsFor_mono [DecidableEq Program] [DecidableEq Target]
    {selected raw : SolveRelation Program Target}
    (hsubset : selected ⊆ raw) (target : Target) :
    programsFor selected target ⊆ programsFor raw target := by
  intro program hprogram
  simp only [programsFor, Finset.mem_image, Finset.mem_filter] at hprogram ⊢
  rcases hprogram with ⟨edge, ⟨hedge, htarget⟩, rfl⟩
  exact ⟨edge, ⟨hsubset hedge, htarget⟩, rfl⟩

/-- Retaining every raw shortest program is sufficient to preserve the exact
shortest-program set. -/
theorem shortestPrograms_eq_of_subset_of_retains
    (raw selected : Finset Program) (cost : Program → ProgramCost)
    (hsubset : selected ⊆ raw)
    (hretains : shortestPrograms raw cost ⊆ selected) :
    shortestPrograms selected cost = shortestPrograms raw cost := by
  classical
  ext program
  constructor
  · intro hselectedShortest
    rcases Finset.mem_filter.mp hselectedShortest with
      ⟨hprogramSelected, hminimalSelected⟩
    have hprogramRaw : program ∈ raw := hsubset hprogramSelected
    rcases Finset.exists_min_image raw (fun p ↦ (cost p).length)
        ⟨program, hprogramRaw⟩ with ⟨minimum, hminimumRaw, hminimum⟩
    have hminimumShortest : minimum ∈ shortestPrograms raw cost :=
      Finset.mem_filter.mpr ⟨hminimumRaw, hminimum⟩
    have hprogramLeMinimum :
        (cost program).length ≤ (cost minimum).length :=
      hminimalSelected minimum (hretains hminimumShortest)
    exact Finset.mem_filter.mpr ⟨hprogramRaw, fun other hother ↦
      hprogramLeMinimum.trans (hminimum other hother)⟩
  · intro hrawShortest
    rcases Finset.mem_filter.mp hrawShortest with ⟨hprogramRaw, hminimalRaw⟩
    exact Finset.mem_filter.mpr ⟨hretains hrawShortest, fun other hother ↦
      hminimalRaw other (hsubset hother)⟩

/-- The retention condition for shortest representatives is also necessary. -/
theorem shortestPrograms_eq_iff_retains
    (raw selected : Finset Program) (cost : Program → ProgramCost)
    (hsubset : selected ⊆ raw) :
    shortestPrograms selected cost = shortestPrograms raw cost ↔
      shortestPrograms raw cost ⊆ selected := by
  constructor
  · intro heq program hprogram
    have : program ∈ shortestPrograms selected cost := by
      rw [heq]
      exact hprogram
    exact shortestPrograms_subset selected cost this
  · exact shortestPrograms_eq_of_subset_of_retains raw selected cost hsubset

/-- Fastest representatives obey the same exact retention law. -/
theorem fastestPrograms_eq_of_subset_of_retains
    (raw selected : Finset Program) (cost : Program → ProgramCost)
    (hsubset : selected ⊆ raw)
    (hretains : fastestPrograms raw cost ⊆ selected) :
    fastestPrograms selected cost = fastestPrograms raw cost := by
  classical
  ext program
  constructor
  · intro hselectedFastest
    rcases Finset.mem_filter.mp hselectedFastest with
      ⟨hprogramSelected, hminimalSelected⟩
    have hprogramRaw : program ∈ raw := hsubset hprogramSelected
    rcases Finset.exists_min_image raw (fun p ↦ (cost p).runtime)
        ⟨program, hprogramRaw⟩ with ⟨minimum, hminimumRaw, hminimum⟩
    have hminimumFastest : minimum ∈ fastestPrograms raw cost :=
      Finset.mem_filter.mpr ⟨hminimumRaw, hminimum⟩
    have hprogramLeMinimum :
        (cost program).runtime ≤ (cost minimum).runtime :=
      hminimalSelected minimum (hretains hminimumFastest)
    exact Finset.mem_filter.mpr ⟨hprogramRaw, fun other hother ↦
      hprogramLeMinimum.trans (hminimum other hother)⟩
  · intro hrawFastest
    rcases Finset.mem_filter.mp hrawFastest with ⟨hprogramRaw, hminimalRaw⟩
    exact Finset.mem_filter.mpr ⟨hretains hrawFastest, fun other hother ↦
      hminimalRaw other (hsubset hother)⟩

theorem fastestPrograms_eq_iff_retains
    (raw selected : Finset Program) (cost : Program → ProgramCost)
    (hsubset : selected ⊆ raw) :
    fastestPrograms selected cost = fastestPrograms raw cost ↔
      fastestPrograms raw cost ⊆ selected := by
  constructor
  · intro heq program hprogram
    have : program ∈ fastestPrograms selected cost := by
      rw [heq]
      exact hprogram
    exact fastestPrograms_subset selected cost this
  · exact fastestPrograms_eq_of_subset_of_retains raw selected cost hsubset

/-- A Pareto selection is sound when every selected point dominated in the raw
set still has a dominating witness in the selected set.  This prevents an
excluded dominator from manufacturing a false frontier member. -/
def ParetoSoundSelection
    (raw selected : Finset Program) (cost : Program → ProgramCost) : Prop :=
  ∀ program ∈ selected,
    (∃ other ∈ raw, Dominates cost other program) →
      ∃ other ∈ selected, Dominates cost other program

/-- Exact Pareto preservation requires both retaining the raw frontier and not
manufacturing a new frontier by dropping every dominator of a selected point. -/
theorem paretoPrograms_eq_iff_retains_and_sound
    (raw selected : Finset Program) (cost : Program → ProgramCost)
    (hsubset : selected ⊆ raw) :
    paretoPrograms selected cost = paretoPrograms raw cost ↔
      paretoPrograms raw cost ⊆ selected ∧
        ParetoSoundSelection raw selected cost := by
  classical
  constructor
  · intro heq
    constructor
    · intro program hprogram
      have : program ∈ paretoPrograms selected cost := by
        rw [heq]
        exact hprogram
      exact paretoPrograms_subset selected cost this
    · intro program hprogramSelected hdominatedRaw
      have hprogramRaw : program ∈ raw := hsubset hprogramSelected
      have hnotRawPareto : program ∉ paretoPrograms raw cost := by
        simp only [paretoPrograms, Finset.mem_filter, not_and_or, not_not]
        exact Or.inr hdominatedRaw
      have hnotSelectedPareto : program ∉ paretoPrograms selected cost := by
        rw [heq]
        exact hnotRawPareto
      simp only [paretoPrograms, Finset.mem_filter, hprogramSelected, true_and,
        not_not] at hnotSelectedPareto
      exact hnotSelectedPareto
  · rintro ⟨hretains, hsound⟩
    ext program
    constructor
    · intro hselectedPareto
      rcases Finset.mem_filter.mp (show program ∈ selected.filter (fun candidate ↦
          ¬ ∃ other ∈ selected, Dominates cost other candidate) by
            simpa [paretoPrograms] using hselectedPareto) with
        ⟨hprogramSelected, hnotDominatedSelected⟩
      have hprogramRaw : program ∈ raw := hsubset hprogramSelected
      have hnotDominatedRaw : ¬ ∃ other ∈ raw, Dominates cost other program := by
        intro hdominatedRaw
        exact hnotDominatedSelected (hsound program hprogramSelected hdominatedRaw)
      change program ∈ raw.filter (fun candidate ↦
        ¬ ∃ other ∈ raw, Dominates cost other candidate)
      exact Finset.mem_filter.mpr ⟨hprogramRaw, hnotDominatedRaw⟩
    · intro hrawPareto
      rcases Finset.mem_filter.mp (show program ∈ raw.filter (fun candidate ↦
          ¬ ∃ other ∈ raw, Dominates cost other candidate) by
            simpa [paretoPrograms] using hrawPareto) with
        ⟨_hprogramRaw, hnotDominatedRaw⟩
      have hprogramSelected := hretains hrawPareto
      have hnotDominatedSelected :
          ¬ ∃ other ∈ selected, Dominates cost other program := by
        rintro ⟨other, hother, hdominates⟩
        exact hnotDominatedRaw ⟨other, hsubset hother, hdominates⟩
      change program ∈ selected.filter (fun candidate ↦
        ¬ ∃ other ∈ selected, Dominates cost other candidate)
      exact Finset.mem_filter.mpr ⟨hprogramSelected, hnotDominatedSelected⟩

end FiniteSelection

/-! ## Curated-view partition -/

section CuratedStatistics

variable {Program : Type uP} {Target : Type uT}
variable {Model : Type uM} {Arm : Type uA} {World : Type uW}
variable {Lineage : Type uL} {checker : Program → Target → Prop}
variable [DecidableEq Program] [DecidableEq Target]

local notation "ViewT" =>
  CuratedView (Program := Program) (Target := Target)
    (Model := Model) (Arm := Arm) (World := World)
    (Lineage := Lineage) (checker := checker)

/-- The raw distinct solve relation retained behind a curated view. -/
noncomputable def CuratedView.rawRelation (view : ViewT) :
    SolveRelation Program Target :=
  distinctEdges view.raw

def CuratedView.RetainsShortest
    (view : ViewT) (cost : Program → ProgramCost) : Prop :=
  ∀ target,
    shortestPrograms (programsFor view.rawRelation target) cost ⊆
      programsFor view.selected target

def CuratedView.RetainsFastest
    (view : ViewT) (cost : Program → ProgramCost) : Prop :=
  ∀ target,
    fastestPrograms (programsFor view.rawRelation target) cost ⊆
      programsFor view.selected target

def CuratedView.RetainsPareto
    (view : ViewT) (cost : Program → ProgramCost) : Prop :=
  ∀ target,
    paretoPrograms (programsFor view.rawRelation target) cost ⊆
      programsFor view.selected target

def CuratedView.ParetoSound
    (view : ViewT) (cost : Program → ProgramCost) : Prop :=
  ∀ target,
    ParetoSoundSelection (programsFor view.rawRelation target)
      (programsFor view.selected target) cost

/-- The exact representative contract sufficient for every cost summary. -/
structure CuratedView.RepresentativeComplete
    (view : ViewT) (cost : Program → ProgramCost) : Prop where
  shortest : view.RetainsShortest cost
  fastest : view.RetainsFastest cost
  pareto : view.RetainsPareto cost
  paretoSound : view.ParetoSound cost

theorem rawRelation_targetSet_eq_coveredTargets (view : ViewT) :
    targetSet view.rawRelation = coveredTargets view.raw := by
  classical
  ext target
  simpa [CuratedView.rawRelation, targetSet, Prod.ext_iff] using
    (target_projection_preserves_coverage view.raw target).symm

/-- Solved-at-all is invariant exactly under the existing coverage-complete
contract. -/
theorem curated_solved_iff_raw_solved
    (view : ViewT) (hcomplete : view.CoverageComplete) (target : Target) :
    target ∈ targetSet view.selected ↔ target ∈ coveredTargets view.raw := by
  rw [hcomplete]

theorem curated_shortestPrograms_preserved
    (view : ViewT) (cost : Program → ProgramCost)
    (hretains : view.RetainsShortest cost) (target : Target) :
    shortestPrograms (programsFor view.selected target) cost =
      shortestPrograms (programsFor view.rawRelation target) cost := by
  exact shortestPrograms_eq_of_subset_of_retains _ _ cost
    (programsFor_mono view.selected_subset_raw target) (hretains target)

theorem curated_shortestPrograms_preserved_iff
    (view : ViewT) (cost : Program → ProgramCost) (target : Target) :
    shortestPrograms (programsFor view.selected target) cost =
        shortestPrograms (programsFor view.rawRelation target) cost ↔
      shortestPrograms (programsFor view.rawRelation target) cost ⊆
        programsFor view.selected target :=
  shortestPrograms_eq_iff_retains _ _ cost
    (programsFor_mono view.selected_subset_raw target)

theorem curated_fastestPrograms_preserved
    (view : ViewT) (cost : Program → ProgramCost)
    (hretains : view.RetainsFastest cost) (target : Target) :
    fastestPrograms (programsFor view.selected target) cost =
      fastestPrograms (programsFor view.rawRelation target) cost := by
  exact fastestPrograms_eq_of_subset_of_retains _ _ cost
    (programsFor_mono view.selected_subset_raw target) (hretains target)

theorem curated_fastestPrograms_preserved_iff
    (view : ViewT) (cost : Program → ProgramCost) (target : Target) :
    fastestPrograms (programsFor view.selected target) cost =
        fastestPrograms (programsFor view.rawRelation target) cost ↔
      fastestPrograms (programsFor view.rawRelation target) cost ⊆
        programsFor view.selected target :=
  fastestPrograms_eq_iff_retains _ _ cost
    (programsFor_mono view.selected_subset_raw target)

theorem curated_paretoPrograms_preserved_iff
    (view : ViewT) (cost : Program → ProgramCost) (target : Target) :
    paretoPrograms (programsFor view.selected target) cost =
        paretoPrograms (programsFor view.rawRelation target) cost ↔
      paretoPrograms (programsFor view.rawRelation target) cost ⊆
          programsFor view.selected target ∧
        ParetoSoundSelection (programsFor view.rawRelation target)
          (programsFor view.selected target) cost :=
  paretoPrograms_eq_iff_retains_and_sound _ _ cost
    (programsFor_mono view.selected_subset_raw target)

theorem curated_paretoPrograms_preserved
    (view : ViewT) (cost : Program → ProgramCost)
    (hcomplete : view.RepresentativeComplete cost) (target : Target) :
    paretoPrograms (programsFor view.selected target) cost =
      paretoPrograms (programsFor view.rawRelation target) cost :=
  (curated_paretoPrograms_preserved_iff view cost target).2
    ⟨hcomplete.pareto target, hcomplete.paretoSound target⟩

/-- Target exclusivity between two arms is invariant when both capped views
are coverage-complete.  This is target exclusivity, not program exclusivity. -/
theorem curated_exclusiveTargetsLeft_preserved
    (left right : ViewT)
    (hleft : left.CoverageComplete) (hright : right.CoverageComplete) :
    exclusiveTargetsLeft left.selected right.selected =
      exclusiveTargetsLeft left.rawRelation right.rawRelation := by
  unfold exclusiveTargetsLeft
  rw [hleft, hright, rawRelation_targetSet_eq_coveredTargets,
    rawRelation_targetSet_eq_coveredTargets]

end CuratedStatistics

/-! ## Positive and negative fixtures -/

namespace CapInvarianceFixtures

open Fixtures AccountingFixtures

def capTwoView : CuratedView
    (Program := Fixtures.Program) (Target := Fixtures.Target)
    (Model := Bool) (Arm := Bool) (World := Bool)
    (Lineage := ℕ) (checker := Fixtures.checker) where
  raw := twoProgramsOneTarget
  cap := 2
  selected := {(.alpha, .first), (.beta, .first)}
  selected_subset_raw := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact (mem_distinctEdges_iff twoProgramsOneTarget .alpha .first).2
        ⟨alphaFirst, by simp [twoProgramsOneTarget], rfl, rfl⟩
    · exact (mem_distinctEdges_iff twoProgramsOneTarget .beta .first).2
        ⟨betaFirst, by simp [twoProgramsOneTarget], rfl, rfl⟩
  perTargetCap := by
    intro target
    cases target <;> decide +kernel

theorem capTwo_coverageComplete : capTwoView.CoverageComplete := by
  classical
  simp [CuratedView.CoverageComplete, capTwoView, targetSet, coveredTargets,
    twoProgramsOneTarget, alphaFirst, betaFirst]

/-- Negative fixture: two coverage-complete views of the same raw ledger can
report different selected witness multiplicities. -/
theorem selected_witness_count_not_cap_invariant :
    capOneView.CoverageComplete ∧ capTwoView.CoverageComplete ∧
      (programsFor capOneView.selected Fixtures.Target.first).card ≠
        (programsFor capTwoView.selected Fixtures.Target.first).card := by
  refine ⟨cap_preserves_coverage_not_multiplicity.1,
    capTwo_coverageComplete, ?_⟩
  decide +kernel

/-- Program-diversity statistics are likewise corrupted by the capped view,
even though target coverage is unchanged. -/
theorem selected_program_diversity_not_cap_invariant :
    targetCoverage capOneView.selected = targetCoverage capTwoView.selected ∧
      programCoverage capOneView.selected ≠ programCoverage capTwoView.selected := by
  decide +kernel

def representativeCost : Fixtures.Program → ProgramCost
  | .alpha => ⟨1, 1⟩
  | .beta => ⟨2, 2⟩

/-- Positive fixture: a cap-one view is sufficient when the retained program
is simultaneously the unique shortest, fastest, and Pareto representative. -/
theorem capOne_representative_complete :
    capOneView.RepresentativeComplete representativeCost := by
  classical
  have hrawFirst :
      programsFor capOneView.rawRelation Fixtures.Target.first =
        {.alpha, .beta} := by
    ext program
    cases program <;>
      simp [CuratedView.rawRelation, capOneView, programsFor, distinctEdges,
        CheckedObservation.edge, twoProgramsOneTarget, alphaFirst, betaFirst]
  have hrawSecond :
      programsFor capOneView.rawRelation Fixtures.Target.second = ∅ := by
    ext program
    cases program <;>
      simp [CuratedView.rawRelation, capOneView, programsFor, distinctEdges,
        CheckedObservation.edge, twoProgramsOneTarget, alphaFirst, betaFirst]
  have hselectedFirst :
      programsFor capOneView.selected Fixtures.Target.first = {.alpha} := by
    ext program
    cases program <;> simp [capOneView, programsFor]
  have hselectedSecond :
      programsFor capOneView.selected Fixtures.Target.second = ∅ := by
    ext program
    cases program <;> simp [capOneView, programsFor]
  have hparetoFirst :
      paretoPrograms ({.alpha, .beta} : Finset Fixtures.Program)
          representativeCost = {.alpha} := by
    ext program
    cases program <;>
      simp [paretoPrograms, Dominates, representativeCost]
  constructor
  · intro target
    cases target
    · rw [hrawFirst, hselectedFirst]
      decide +kernel
    · rw [hrawSecond, hselectedSecond]
      decide +kernel
  · intro target
    cases target
    · rw [hrawFirst, hselectedFirst]
      decide +kernel
    · rw [hrawSecond, hselectedSecond]
      decide +kernel
  · intro target
    cases target
    · rw [hrawFirst, hselectedFirst]
      rw [hparetoFirst]
    · rw [hrawSecond, hselectedSecond]
      decide +kernel
  · intro target
    cases target
    · rw [hrawFirst, hselectedFirst]
      intro program hprogram hdominated
      cases program
      · rcases hdominated with ⟨other, _hother, hdominates⟩
        cases other <;> simp [Dominates, representativeCost] at hdominates
      · simp at hprogram
    · rw [hrawSecond, hselectedSecond]
      intro program hprogram
      simp at hprogram

theorem capOne_cost_summaries_preserved :
    shortestPrograms
        (programsFor capOneView.selected Fixtures.Target.first) representativeCost =
      shortestPrograms
        (programsFor capOneView.rawRelation Fixtures.Target.first) representativeCost ∧
    fastestPrograms
        (programsFor capOneView.selected Fixtures.Target.first) representativeCost =
      fastestPrograms
        (programsFor capOneView.rawRelation Fixtures.Target.first) representativeCost ∧
    paretoPrograms
        (programsFor capOneView.selected Fixtures.Target.first) representativeCost =
      paretoPrograms
        (programsFor capOneView.rawRelation Fixtures.Target.first) representativeCost := by
  exact ⟨curated_shortestPrograms_preserved capOneView representativeCost
      capOne_representative_complete.shortest .first,
    curated_fastestPrograms_preserved capOneView representativeCost
      capOne_representative_complete.fastest .first,
    curated_paretoPrograms_preserved capOneView representativeCost
      capOne_representative_complete .first⟩

end CapInvarianceFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
