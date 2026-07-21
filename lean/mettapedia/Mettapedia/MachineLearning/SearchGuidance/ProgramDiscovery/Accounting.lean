import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EquivalenceLadder

/-!
# Coverage, diversity, longitudinal accounting, and derived curation

The raw ledger retains occurrences.  This file performs finite accounting on
its distinct program-target relation and proves which quantities are preserved
by unions and by a bounded, non-destructive representative view.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT uM uA uW uL

/-- A finite distinct solve relation. -/
abbrev SolveRelation (Program : Type uP) (Target : Type uT) :=
  Finset (Program × Target)

section RelationAccounting

variable {Program : Type uP} {Target : Type uT}
variable [DecidableEq Program] [DecidableEq Target]

def targetSet (relation : SolveRelation Program Target) : Finset Target :=
  relation.image Prod.snd

def programSet (relation : SolveRelation Program Target) : Finset Program :=
  relation.image Prod.fst

def programsFor
    (relation : SolveRelation Program Target) (target : Target) : Finset Program :=
  (relation.filter (fun edge ↦ edge.2 = target)).image Prod.fst

def targetCoverage (relation : SolveRelation Program Target) : ℕ :=
  (targetSet relation).card

def programCoverage (relation : SolveRelation Program Target) : ℕ :=
  (programSet relation).card

def edgeCoverage (relation : SolveRelation Program Target) : ℕ :=
  relation.card

def witnessMultiplicity
    (relation : SolveRelation Program Target) (target : Target) : ℕ :=
  (programsFor relation target).card

def sharedTargets
    (left right : SolveRelation Program Target) : Finset Target :=
  targetSet left ∩ targetSet right

def exclusiveTargetsLeft
    (left right : SolveRelation Program Target) : Finset Target :=
  targetSet left \ targetSet right

def sharedPrograms
    (left right : SolveRelation Program Target) : Finset Program :=
  programSet left ∩ programSet right

def exclusiveProgramsLeft
    (left right : SolveRelation Program Target) : Finset Program :=
  programSet left \ programSet right

def marginalTargetContribution
    (base addition : SolveRelation Program Target) : ℕ :=
  (targetSet addition \ targetSet base).card

def marginalProgramContribution
    (base addition : SolveRelation Program Target) : ℕ :=
  (programSet addition \ programSet base).card

def newEdges
    (known observed : SolveRelation Program Target) : SolveRelation Program Target :=
  observed \ known

def refoundEdges
    (known observed : SolveRelation Program Target) : SolveRelation Program Target :=
  observed ∩ known

/-- Cumulative solve relation across a list of generations. -/
def cumulativeRelation
    (generations : List (SolveRelation Program Target)) : SolveRelation Program Target :=
  generations.foldl (fun accumulated generation ↦ accumulated ∪ generation) ∅

theorem targetSet_union
    (left right : SolveRelation Program Target) :
    targetSet (left ∪ right) = targetSet left ∪ targetSet right := by
  ext target
  simp only [targetSet, Finset.mem_image, Finset.mem_union]
  aesop

theorem programSet_union
    (left right : SolveRelation Program Target) :
    programSet (left ∪ right) = programSet left ∪ programSet right := by
  ext program
  simp only [programSet, Finset.mem_image, Finset.mem_union]
  aesop

omit [DecidableEq Program] in
theorem targetSet_mono {left right : SolveRelation Program Target}
    (h : left ⊆ right) : targetSet left ⊆ targetSet right := by
  intro target htarget
  rcases Finset.mem_image.mp htarget with ⟨edge, hedge, rfl⟩
  exact Finset.mem_image.mpr ⟨edge, h hedge, rfl⟩

omit [DecidableEq Target] in
theorem programSet_mono {left right : SolveRelation Program Target}
    (h : left ⊆ right) : programSet left ⊆ programSet right := by
  intro program hprogram
  rcases Finset.mem_image.mp hprogram with ⟨edge, hedge, rfl⟩
  exact Finset.mem_image.mpr ⟨edge, h hedge, rfl⟩

omit [DecidableEq Program] in
/-- Cumulative target coverage is monotone under relation extension. -/
theorem targetCoverage_mono {left right : SolveRelation Program Target}
    (h : left ⊆ right) : targetCoverage left ≤ targetCoverage right :=
  Finset.card_le_card (targetSet_mono h)

omit [DecidableEq Target] in
theorem programCoverage_mono {left right : SolveRelation Program Target}
    (h : left ⊆ right) : programCoverage left ≤ programCoverage right :=
  Finset.card_le_card (programSet_mono h)

/-- Seed/model target counts dominate their union count. -/
theorem target_union_le_sum (left right : SolveRelation Program Target) :
    targetCoverage (left ∪ right) ≤ targetCoverage left + targetCoverage right := by
  classical
  rw [targetCoverage, targetSet_union]
  exact Finset.card_union_le _ _

/-- Equality holds exactly when the two target footprints are disjoint. -/
theorem target_union_eq_sum_iff (left right : SolveRelation Program Target) :
    targetCoverage (left ∪ right) = targetCoverage left + targetCoverage right ↔
      Disjoint (targetSet left) (targetSet right) := by
  classical
  rw [targetCoverage, targetSet_union]
  exact Finset.card_union_eq_card_add_card

/-- Inclusion-exclusion for covered targets. -/
theorem target_inclusion_exclusion (left right : SolveRelation Program Target) :
    targetCoverage (left ∪ right) + (sharedTargets left right).card =
      targetCoverage left + targetCoverage right := by
  classical
  simpa [targetCoverage, sharedTargets, targetSet_union] using
    Finset.card_union_add_card_inter (targetSet left) (targetSet right)

/-- Inclusion-exclusion separately for distinct program witnesses. -/
theorem program_inclusion_exclusion (left right : SolveRelation Program Target) :
    programCoverage (left ∪ right) + (sharedPrograms left right).card =
      programCoverage left + programCoverage right := by
  classical
  simpa [programCoverage, sharedPrograms, programSet_union] using
    Finset.card_union_add_card_inter (programSet left) (programSet right)

theorem new_refound_partition
    (known observed : SolveRelation Program Target) :
    newEdges known observed ∪ refoundEdges known observed = observed := by
  ext edge
  simp only [newEdges, refoundEdges, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter]
  constructor
  · rintro (⟨hobs, hnot⟩ | ⟨hobs, hknown⟩) <;> exact hobs
  · intro hobs
    by_cases hknown : edge ∈ known
    · exact Or.inr ⟨hobs, hknown⟩
    · exact Or.inl ⟨hobs, hknown⟩

theorem new_refound_disjoint
    (known observed : SolveRelation Program Target) :
    Disjoint (newEdges known observed) (refoundEdges known observed) := by
  apply Finset.disjoint_left.mpr
  intro edge hnew hrefound
  exact (Finset.mem_sdiff.mp hnew).2 (Finset.mem_inter.mp hrefound).2

theorem new_refound_count
    (known observed : SolveRelation Program Target) :
    (newEdges known observed).card + (refoundEdges known observed).card = observed.card := by
  rw [← Finset.card_union_of_disjoint (new_refound_disjoint known observed),
    new_refound_partition]

end RelationAccounting

/-! ## Shortest, fastest, and Pareto representative views -/

section Pareto

variable {Program : Type uP}
variable [DecidableEq Program]

structure ProgramCost where
  length : ℕ
  runtime : ℕ
  deriving DecidableEq, Repr

def Dominates (cost : Program → ProgramCost) (left right : Program) : Prop :=
  (cost left).length ≤ (cost right).length ∧
    (cost left).runtime ≤ (cost right).runtime ∧
    ((cost left).length < (cost right).length ∨
      (cost left).runtime < (cost right).runtime)

def shortestPrograms
    (programs : Finset Program) (cost : Program → ProgramCost) : Finset Program :=
  programs.filter fun program ↦
    ∀ other ∈ programs, (cost program).length ≤ (cost other).length

def fastestPrograms
    (programs : Finset Program) (cost : Program → ProgramCost) : Finset Program :=
  programs.filter fun program ↦
    ∀ other ∈ programs, (cost program).runtime ≤ (cost other).runtime

noncomputable def paretoPrograms
    (programs : Finset Program) (cost : Program → ProgramCost) : Finset Program := by
  classical
  exact programs.filter fun program ↦
    ¬ ∃ other ∈ programs, Dominates cost other program

omit [DecidableEq Program] in
theorem shortestPrograms_subset
    (programs : Finset Program) (cost : Program → ProgramCost) :
    shortestPrograms programs cost ⊆ programs := by
  classical
  intro program h
  exact (Finset.mem_filter.mp h).1

omit [DecidableEq Program] in
theorem fastestPrograms_subset
    (programs : Finset Program) (cost : Program → ProgramCost) :
    fastestPrograms programs cost ⊆ programs := by
  classical
  intro program h
  exact (Finset.mem_filter.mp h).1

omit [DecidableEq Program] in
theorem paretoPrograms_subset
    (programs : Finset Program) (cost : Program → ProgramCost) :
    paretoPrograms programs cost ⊆ programs := by
  classical
  intro program h
  exact (Finset.mem_filter.mp (show program ∈ programs.filter (fun program ↦
    ¬ ∃ other ∈ programs, Dominates cost other program) by
      simpa [paretoPrograms] using h)).1

end Pareto

/-! ## Bounded curation is a derived view -/

section Curation

variable {Program : Type uP} {Target : Type uT}
variable {Model : Type uM} {Arm : Type uA} {World : Type uW}
variable {Lineage : Type uL} {checker : Program → Target → Prop}
variable [DecidableEq Program] [DecidableEq Target]

local notation "LedgerT" =>
  DiscoveryLedger Program Target Model Arm World Lineage checker

/-- A capped representative view retains its immutable raw occurrence ledger
and selects only authenticated distinct edges. -/
structure CuratedView where
  raw : LedgerT
  cap : ℕ
  selected : SolveRelation Program Target
  selected_subset_raw : selected ⊆ distinctEdges raw
  perTargetCap : ∀ target, (programsFor selected target).card ≤ cap

local notation "ViewT" =>
  CuratedView (Program := Program) (Target := Target)
    (Model := Model) (Arm := Arm) (World := World)
    (Lineage := Lineage) (checker := checker)

def CuratedView.CoverageComplete (view : ViewT) : Prop :=
  targetSet view.selected = coveredTargets view.raw

theorem curated_selected_edges_are_raw (view : ViewT) :
    view.selected ⊆ distinctEdges view.raw :=
  view.selected_subset_raw

/-- Curation can only remove representatives from the selected view; it cannot
add an unauthenticated edge. -/
theorem curated_selected_card_le_raw_edges (view : ViewT) :
    view.selected.card ≤ (distinctEdges view.raw).card :=
  Finset.card_le_card view.selected_subset_raw

/-- Two curated views over the same raw ledger have the same raw occurrence
counts even when their caps or selections differ. -/
theorem curated_views_same_raw_occurrence_count
    (left right : ViewT) (hraw : left.raw = right.raw)
    (program : Program) (target : Target) :
    occurrenceCount left.raw program target =
      occurrenceCount right.raw program target := by
  rw [hraw]

/-- The same raw-ledger identity also fixes distinct witness multiplicity. -/
theorem curated_views_same_raw_witness_count
    (left right : ViewT) (hraw : left.raw = right.raw)
    (target : Target) :
    (witnessPrograms left.raw target).card =
      (witnessPrograms right.raw target).card := by
  rw [hraw]

/-- A coverage-complete curated view preserves the covered-target statistic. -/
theorem curated_target_coverage_preserved
    (view : ViewT) (hcomplete : view.CoverageComplete) :
    targetCoverage view.selected = (coveredTargets view.raw).card := by
  exact congrArg Finset.card hcomplete

end Curation

/-! ## Connection to the fixed-budget categorical coverage theory -/

section ExistingCoverageBridge

open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

noncomputable def categoricalSolveRelation {k n : ℕ}
    (word : Fin n → Fin k) (accepted : Finset (Fin k)) :
    SolveRelation Unit (Fin k) := by
  classical
  exact (accepted.filter (wordContains word)).image (fun target ↦ ((), target))

theorem categoricalSolveRelation_targetCoverage_eq {k n : ℕ}
    (word : Fin n → Fin k) (accepted : Finset (Fin k)) :
    targetCoverage (categoricalSolveRelation word accepted) =
      distinctVerifiedCoverage word accepted := by
  classical
  have htargets :
      targetSet (categoricalSolveRelation word accepted) =
        accepted.filter (wordContains word) := by
    ext target
    simp [targetSet, categoricalSolveRelation]
  rw [targetCoverage, htargets]
  unfold distinctVerifiedCoverage
  induction accepted using Finset.induction with
  | empty => simp
  | @insert target accepted hnot ih =>
      simp

noncomputable def categoricalPortfolioRelation {k n₁ n₂ : ℕ}
    (left : Fin n₁ → Fin k) (right : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) : SolveRelation Unit (Fin k) :=
  categoricalSolveRelation left accepted ∪ categoricalSolveRelation right accepted

theorem categoricalPortfolioRelation_targetCoverage_eq {k n₁ n₂ : ℕ}
    (left : Fin n₁ → Fin k) (right : Fin n₂ → Fin k)
    (accepted : Finset (Fin k)) :
    targetCoverage (categoricalPortfolioRelation left right accepted) =
      twoArmUnionCoverage left right accepted := by
  classical
  have htargets :
      targetSet (categoricalPortfolioRelation left right accepted) =
        accepted.filter (fun target ↦
          wordContains left target ∨ wordContains right target) := by
    ext target
    simp only [categoricalPortfolioRelation, Finset.mem_union,
      targetSet, categoricalSolveRelation, Finset.mem_image, Finset.mem_filter]
    constructor <;> aesop
  rw [targetCoverage, htargets]
  unfold twoArmUnionCoverage
  induction accepted using Finset.induction with
  | empty => simp
  | @insert target accepted hnot ih =>
      simp

end ExistingCoverageBridge

/-! ## Concrete accounting and curation counterexamples -/

namespace AccountingFixtures

inductive Program where
  | p0 | p1 | p2 | p3
  deriving DecidableEq, Repr

inductive Target where
  | t0 | t1 | t2 | t3
  deriving DecidableEq, Repr

def spreadPrograms : SolveRelation Program Target :=
  {(.p0, .t0), (.p1, .t1)}

def sharedProgram : SolveRelation Program Target :=
  {(.p0, .t0), (.p0, .t1)}

def overlapArm : SolveRelation Program Target :=
  {(.p2, .t0), (.p3, .t1)}

def complementaryArm : SolveRelation Program Target :=
  {(.p2, .t2), (.p3, .t3)}

theorem equal_target_yield_different_program_diversity :
    targetCoverage spreadPrograms = targetCoverage sharedProgram ∧
      programCoverage spreadPrograms ≠ programCoverage sharedProgram := by
  decide +kernel

theorem equal_standalone_yield_different_complementarity :
    targetCoverage overlapArm = targetCoverage complementaryArm ∧
      marginalTargetContribution spreadPrograms overlapArm = 0 ∧
      marginalTargetContribution spreadPrograms complementaryArm = 2 := by
  decide +kernel

def cost : Program → ProgramCost
  | .p0 => ⟨2, 9⟩
  | .p1 => ⟨5, 3⟩
  | .p2 => ⟨4, 7⟩
  | .p3 => ⟨6, 10⟩

theorem shortest_fastest_disagree_and_pareto_nontrivial :
    shortestPrograms {.p0, .p1, .p2, .p3} cost = {.p0} ∧
      fastestPrograms {.p0, .p1, .p2, .p3} cost = {.p1} ∧
      paretoPrograms {.p0, .p1, .p2, .p3} cost = {.p0, .p1, .p2} := by
  classical
  constructor
  · ext program
    cases program <;> simp [shortestPrograms, cost]
  · constructor
    · ext program
      cases program <;> simp [fastestPrograms, cost]
    · ext program
      cases program <;> simp [paretoPrograms, Dominates, cost]

/-- An empty bounded search can miss a retained capability; absence alone is
not semantic forgetting. -/
theorem finite_budget_absence_not_forgetting_fixture :
    ∃ (previous capability search : SolveRelation Program Target) (edge : Program × Target),
      edge ∈ previous ∧ edge ∈ capability ∧ edge ∉ search := by
  exact ⟨{(.p0, .t0)}, {(.p0, .t0)}, ∅, (.p0, .t0), by simp⟩

open Fixtures

def capOneView : CuratedView
    (Program := Fixtures.Program) (Target := Fixtures.Target)
    (Model := Bool) (Arm := Bool) (World := Bool)
    (Lineage := ℕ) (checker := Fixtures.checker) where
  raw := twoProgramsOneTarget
  cap := 1
  selected := {(.alpha, .first)}
  selected_subset_raw := by
    intro edge hedge
    simp at hedge
    subst edge
    exact (mem_distinctEdges_iff twoProgramsOneTarget .alpha .first).2
      ⟨alphaFirst, by simp [twoProgramsOneTarget], rfl, rfl⟩
  perTargetCap := by
    intro target
    cases target <;> decide +kernel

/-- A cap-one view can preserve target coverage while losing witness
multiplicity; the raw count remains available in the same object. -/
theorem cap_preserves_coverage_not_multiplicity_fixture :
    capOneView.CoverageComplete ∧
      (programsFor capOneView.selected Fixtures.Target.first).card = 1 ∧
      (witnessPrograms capOneView.raw Fixtures.Target.first).card = 2 := by
  classical
  constructor
  · simp [CuratedView.CoverageComplete, capOneView, targetSet, coveredTargets,
      twoProgramsOneTarget, alphaFirst, betaFirst]
  · constructor
    · change (programsFor {(.alpha, .first)} Fixtures.Target.first).card = 1
      decide +kernel
    · change (witnessPrograms twoProgramsOneTarget Fixtures.Target.first).card = 2
      rw [two_programs_one_target_fixture.1]
      decide +kernel

end AccountingFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
