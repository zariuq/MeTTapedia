import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EquivalenceLadder

/-!
# Coverage, diversity, longitudinal accounting, and derived curation

The raw ledger retains occurrences.  This file performs finite accounting on
its distinct program-target relation and proves which quantities are preserved
by unions and by a bounded, non-destructive representative view.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT uM uA uW uL

/-! ## Finite projected-event accounting

The primitive finite evidence object is a set of distinct atomic events.
Coverage and diversity are valuations only after a projection from those atoms
has been fixed.  The same verified event set may therefore support several
different, individually valid counts; these counts must not be mixed as though
they had the same atomic unit.
-/

section ProjectedEventAccounting

variable {Atom : Type*} {Feature : Type*}
variable [DecidableEq Atom] [DecidableEq Feature]

/-- The distinct observable features induced by projecting atomic events. -/
def projectedSet (projection : Atom → Feature) (events : Finset Atom) : Finset Feature :=
  events.image projection

/-- Cardinality after fixing an event-to-feature projection. -/
def projectedCoverage (projection : Atom → Feature) (events : Finset Atom) : ℕ :=
  (projectedSet projection events).card

theorem projectedSet_union (projection : Atom → Feature) (left right : Finset Atom) :
    projectedSet projection (left ∪ right) =
      projectedSet projection left ∪ projectedSet projection right := by
  exact Finset.image_union left right

omit [DecidableEq Atom] in
theorem projectedSet_mono (projection : Atom → Feature)
    {left right : Finset Atom} (h : left ⊆ right) :
    projectedSet projection left ⊆ projectedSet projection right := by
  exact Finset.image_mono projection h

/-- Projected coverage is subadditive because distinct source atoms may
collide after projection. -/
theorem projected_union_le_sum
    (projection : Atom → Feature) (left right : Finset Atom) :
    projectedCoverage projection (left ∪ right) ≤
      projectedCoverage projection left + projectedCoverage projection right := by
  rw [projectedCoverage, projectedSet_union]
  exact Finset.card_union_le _ _

/-- Additivity after projection holds exactly when the projected footprints
are disjoint, not merely when the source event sets are disjoint. -/
theorem projected_union_eq_sum_iff
    (projection : Atom → Feature) (left right : Finset Atom) :
    projectedCoverage projection (left ∪ right) =
        projectedCoverage projection left + projectedCoverage projection right ↔
      Disjoint (projectedSet projection left) (projectedSet projection right) := by
  rw [projectedCoverage, projectedSet_union]
  exact Finset.card_union_eq_card_add_card

/-- Inclusion--exclusion is the exact correction for collisions introduced by
a finite projection. -/
theorem projected_inclusion_exclusion
    (projection : Atom → Feature) (left right : Finset Atom) :
    projectedCoverage projection (left ∪ right) +
        (projectedSet projection left ∩ projectedSet projection right).card =
      projectedCoverage projection left + projectedCoverage projection right := by
  simpa [projectedCoverage, projectedSet_union] using
    Finset.card_union_add_card_inter
      (projectedSet projection left) (projectedSet projection right)

omit [DecidableEq Atom] in
/-- A single cross-set projection collision is enough to invalidate projected
additivity, even when the underlying atomic events are distinct. -/
theorem projected_not_disjoint_of_collision
    (projection : Atom → Feature) {left right : Finset Atom} {x y : Atom}
    (hx : x ∈ left) (hy : y ∈ right) (hcollision : projection x = projection y) :
    ¬ Disjoint (projectedSet projection left) (projectedSet projection right) := by
  intro hdisjoint
  have hleft : projection x ∈ projectedSet projection left :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hright : projection x ∈ projectedSet projection right := by
    rw [hcollision]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  exact (Finset.disjoint_left.mp hdisjoint) hleft hright

omit [DecidableEq Atom] in
/-- Conversely, an explicit absence of cross-set projection collisions is a
sufficient license for additive projected evidence. -/
theorem projected_disjoint_of_cross_ne
    (projection : Atom → Feature) {left right : Finset Atom}
    (hcross : ∀ x ∈ left, ∀ y ∈ right, projection x ≠ projection y) :
    Disjoint (projectedSet projection left) (projectedSet projection right) := by
  refine Finset.disjoint_left.mpr ?_
  intro feature hleft hright
  rcases Finset.mem_image.mp hleft with ⟨x, hx, hxfeature⟩
  rcases Finset.mem_image.mp hright with ⟨y, hy, hyfeature⟩
  exact hcross x hx y hy (hxfeature.trans hyfeature.symm)

/-- General observation-collision boundary: if two worlds have the same
observable image but different estimands, no estimator of that image recovers
the estimand uniformly. -/
theorem no_uniform_recovery_of_observation_collision
    {World Observation Estimand : Type*}
    (observe : World → Observation) (estimand : World → Estimand)
    {left right : World} (hobservation : observe left = observe right)
    (hestimand : estimand left ≠ estimand right) :
    ¬ ∃ recover : Observation → Estimand,
      ∀ world, recover (observe world) = estimand world := by
  rintro ⟨recover, hrecovers⟩
  apply hestimand
  rw [← hrecovers left, hobservation, hrecovers right]

end ProjectedEventAccounting

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

/-- Targets witnessed by one program identity.  This is the program-side
degree footprint of the bipartite solve relation. -/
def targetsForProgram
    (relation : SolveRelation Program Target) (program : Program) : Finset Target :=
  (relation.filter (fun edge ↦ edge.1 = program)).image Prod.snd

/-- The number of distinct targets witnessed by one program. -/
def programTargetDegree
    (relation : SolveRelation Program Target) (program : Program) : ℕ :=
  (targetsForProgram relation program).card

/-- Remove every edge carrying one program identity. -/
def withoutProgram
    (relation : SolveRelation Program Target) (program : Program) :
    SolveRelation Program Target :=
  relation.filter (fun edge ↦ edge.1 ≠ program)

/-- Targets lost when one program identity is removed.  Unlike raw degree,
this charges only targets for which the program is the sole remaining
witness. -/
def exclusiveTargetContribution
    (relation : SolveRelation Program Target) (program : Program) : ℕ :=
  (targetSet relation \ targetSet (withoutProgram relation program)).card

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

/-- New edges whose program identity already occurs in the known relation. -/
def reusedProgramNewEdges
    (known observed : SolveRelation Program Target) : SolveRelation Program Target :=
  (newEdges known observed).filter (fun edge ↦ edge.1 ∈ programSet known)

/-- New edges whose program identity is absent from the known relation. -/
def freshProgramNewEdges
    (known observed : SolveRelation Program Target) : SolveRelation Program Target :=
  (newEdges known observed).filter (fun edge ↦ edge.1 ∉ programSet known)

/-- Program identities newly introduced by the observed relation. -/
def freshProgramIdentities
    (known observed : SolveRelation Program Target) : Finset Program :=
  programSet observed \ programSet known

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

theorem targetSet_withoutProgram_subset
    (relation : SolveRelation Program Target) (program : Program) :
    targetSet (withoutProgram relation program) ⊆ targetSet relation := by
  intro target htarget
  rcases Finset.mem_image.mp htarget with ⟨edge, hedge, rfl⟩
  exact Finset.mem_image.mpr ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩

theorem targetsForProgram_subset_targetSet
    (relation : SolveRelation Program Target) (program : Program) :
    targetsForProgram relation program ⊆ targetSet relation := by
  intro target htarget
  rcases Finset.mem_image.mp htarget with ⟨edge, hedge, rfl⟩
  exact Finset.mem_image.mpr ⟨edge, (Finset.mem_filter.mp hedge).1, rfl⟩

/-- Removing one program partitions target coverage into retained targets and
targets exclusively carried by that program. -/
theorem targetCoverage_withoutProgram_add_exclusive
    (relation : SolveRelation Program Target) (program : Program) :
    targetCoverage (withoutProgram relation program) +
        exclusiveTargetContribution relation program =
      targetCoverage relation := by
  have hsubset :
      targetSet (withoutProgram relation program) ⊆ targetSet relation :=
    targetSet_withoutProgram_subset relation program
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  unfold targetCoverage exclusiveTargetContribution at *
  omega

/-- A program can be essential for no more targets than it witnesses.  The
inequality may be strict when other programs cover the same targets. -/
theorem exclusiveTargetContribution_le_programTargetDegree
    (relation : SolveRelation Program Target) (program : Program) :
    exclusiveTargetContribution relation program ≤
      programTargetDegree relation program := by
  apply Finset.card_le_card
  intro target htarget
  rcases Finset.mem_sdiff.mp htarget with ⟨hin, hnotWithout⟩
  rcases Finset.mem_image.mp hin with ⟨edge, hedge, hedgeTarget⟩
  by_cases hprogram : edge.1 = program
  · exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_filter.mpr ⟨hedge, hprogram⟩, hedgeTarget⟩
  · exfalso
    apply hnotWithout
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_filter.mpr ⟨hedge, hprogram⟩, hedgeTarget⟩

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

/-- Edge novelty separates exactly into reuse of known program identities and
genuinely fresh program identities. -/
theorem reused_fresh_newEdges_partition
    (known observed : SolveRelation Program Target) :
    reusedProgramNewEdges known observed ∪ freshProgramNewEdges known observed =
      newEdges known observed := by
  ext edge
  simp only [reusedProgramNewEdges, freshProgramNewEdges, Finset.mem_union,
    Finset.mem_filter]
  by_cases hknown : edge.1 ∈ programSet known <;> simp [hknown]

theorem reused_fresh_newEdges_disjoint
    (known observed : SolveRelation Program Target) :
    Disjoint (reusedProgramNewEdges known observed)
      (freshProgramNewEdges known observed) := by
  refine Finset.disjoint_left.mpr ?_
  intro edge hreused hfresh
  exact (Finset.mem_filter.mp hfresh).2 (Finset.mem_filter.mp hreused).2

theorem reused_fresh_newEdges_count
    (known observed : SolveRelation Program Target) :
    (reusedProgramNewEdges known observed).card +
        (freshProgramNewEdges known observed).card =
      (newEdges known observed).card := by
  rw [← Finset.card_union_of_disjoint
      (reused_fresh_newEdges_disjoint known observed),
    reused_fresh_newEdges_partition]

/-- Projecting the fresh-edge partition to programs recovers exactly the set
of fresh program identities. -/
theorem programSet_freshProgramNewEdges
    (known observed : SolveRelation Program Target) :
    programSet (freshProgramNewEdges known observed) =
      freshProgramIdentities known observed := by
  ext program
  constructor
  · intro hprogram
    rcases Finset.mem_image.mp hprogram with ⟨edge, hedge, rfl⟩
    rcases Finset.mem_filter.mp hedge with ⟨hnew, hnotKnownProgram⟩
    exact Finset.mem_sdiff.mpr ⟨
      Finset.mem_image.mpr ⟨edge, (Finset.mem_sdiff.mp hnew).1, rfl⟩,
      hnotKnownProgram⟩
  · intro hprogram
    rcases Finset.mem_sdiff.mp hprogram with ⟨hobserved, hnotKnownProgram⟩
    rcases Finset.mem_image.mp hobserved with ⟨edge, hedgeObserved, rfl⟩
    have hedgeNotKnown : edge ∉ known := by
      intro hedgeKnown
      exact hnotKnownProgram (Finset.mem_image.mpr ⟨edge, hedgeKnown, rfl⟩)
    exact Finset.mem_image.mpr ⟨edge,
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨hedgeObserved, hedgeNotKnown⟩, hnotKnownProgram⟩,
      rfl⟩

theorem programSet_reusedProgramNewEdges_subset
    (known observed : SolveRelation Program Target) :
    programSet (reusedProgramNewEdges known observed) ⊆ programSet known := by
  intro program hprogram
  rcases Finset.mem_image.mp hprogram with ⟨edge, hedge, rfl⟩
  exact (Finset.mem_filter.mp hedge).2

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

/-! ## Unit tests as a coverage relation

A test suite has the same bipartite shape as program discovery: tests witness
coverage obligations.  Test count, covered-obligation count, and individual
test--obligation edges are therefore three different projections of one
relation, not interchangeable Bernoulli sample sizes.
-/

namespace TestCoverage

abbrev Relation (Test : Type*) (Obligation : Type*) :=
  SolveRelation Test Obligation

variable {Test Obligation : Type*}
variable [DecidableEq Test] [DecidableEq Obligation]

def coveredObligations (relation : Relation Test Obligation) : Finset Obligation :=
  targetSet relation

def contributingTests (relation : Relation Test Obligation) : Finset Test :=
  programSet relation

def coverageEdges (relation : Relation Test Obligation) : ℕ :=
  edgeCoverage relation

theorem coveredObligations_union (left right : Relation Test Obligation) :
    coveredObligations (left ∪ right) =
      coveredObligations left ∪ coveredObligations right :=
  targetSet_union left right

/-- Obligation coverage is additive exactly when the suites cover disjoint
obligation footprints.  Disjoint test identities alone are insufficient. -/
theorem obligationCoverage_union_eq_sum_iff
    (left right : Relation Test Obligation) :
    (coveredObligations (left ∪ right)).card =
        (coveredObligations left).card + (coveredObligations right).card ↔
      Disjoint (coveredObligations left) (coveredObligations right) := by
  simpa [coveredObligations, targetCoverage] using
    target_union_eq_sum_iff left right

end TestCoverage

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

def redundantPrograms : SolveRelation Program Target :=
  {(.p0, .t0), (.p0, .t1), (.p1, .t0), (.p1, .t1)}

def overlapArm : SolveRelation Program Target :=
  {(.p2, .t0), (.p3, .t1)}

def complementaryArm : SolveRelation Program Target :=
  {(.p2, .t2), (.p3, .t3)}

theorem equal_target_yield_different_program_diversity :
    targetCoverage spreadPrograms = targetCoverage sharedProgram ∧
      programCoverage spreadPrograms ≠ programCoverage sharedProgram := by
  decide +kernel

/-- Equal program degree does not identify architectural dependence on that
program: redundant witnesses can make its exclusive contribution zero. -/
theorem equal_program_degree_different_exclusive_target_contribution :
    programTargetDegree sharedProgram .p0 = 2 ∧
      exclusiveTargetContribution sharedProgram .p0 = 2 ∧
      programTargetDegree redundantPrograms .p0 = 2 ∧
      exclusiveTargetContribution redundantPrograms .p0 = 0 := by
  decide +kernel

/-- Disjoint verified edges can still collide after projection to targets. -/
theorem disjoint_edges_not_disjoint_target_evidence :
    Disjoint spreadPrograms overlapArm ∧
      ¬ Disjoint (targetSet spreadPrograms) (targetSet overlapArm) := by
  decide +kernel

/-- Consequently, target coverage cannot uniformly recover program diversity:
the two counts live on different projected event spaces. -/
theorem target_observation_does_not_identify_program_coverage :
    ¬ ∃ recover : Finset Target → ℕ,
      ∀ relation : SolveRelation Program Target,
        recover (targetSet relation) = programCoverage relation := by
  apply no_uniform_recovery_of_observation_collision targetSet programCoverage
    (left := spreadPrograms) (right := sharedProgram)
  · decide +kernel
  · exact equal_target_yield_different_program_diversity.2

def knownPrograms : SolveRelation Program Target :=
  {(.p0, .t0)}

def observedNovelty : SolveRelation Program Target :=
  {(.p0, .t1), (.p1, .t2), (.p1, .t3)}

/-- Positive fixture: relational novelty distinguishes one reused-program fact
from two fresh-program facts carrying only one new program identity. -/
theorem relational_novelty_has_distinct_edge_and_identity_counts :
    (reusedProgramNewEdges knownPrograms observedNovelty).card = 1 ∧
      (freshProgramNewEdges knownPrograms observedNovelty).card = 2 ∧
      (freshProgramIdentities knownPrograms observedNovelty).card = 1 := by
  decide +kernel

/-- Unit-test reading of the same fixture: equal obligation coverage does not
identify how many distinct tests contributed. -/
theorem equal_test_coverage_does_not_identify_test_diversity :
    (TestCoverage.coveredObligations spreadPrograms).card =
        (TestCoverage.coveredObligations sharedProgram).card ∧
      (TestCoverage.contributingTests spreadPrograms).card ≠
        (TestCoverage.contributingTests sharedProgram).card :=
  equal_target_yield_different_program_diversity

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
theorem finite_budget_absence_not_forgetting :
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
theorem cap_preserves_coverage_not_multiplicity :
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
      rw [two_programs_one_target.1]
      decide +kernel

end AccountingFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
