import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting

/-!
# Addressable evidence memory

Aggregate signature counts and addressable memory are different projections of
one provenance relation.  This file fixes the atomic event before counting,
proves the information lost by aggregation, and separates availability from
successful routing and direct-target retrieval.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uM uS uQ uP uT uPol uL

/-- One verified, lineage-bound memory fact.  The atom contains both the
aggregate-table coordinates and the identities needed to audit competence and
routing. -/
structure MemoryFact
    (Memory : Type uM) (Signature : Type uS) (Query : Type uQ)
    (Program : Type uP) (Target : Type uT) (Polarity : Type uPol)
    (Lineage : Type uL) where
  memory : Memory
  signature : Signature
  query : Query
  program : Program
  solvedTarget : Target
  polarity : Polarity
  lineage : Lineage
  deriving DecidableEq

/-- The aggregate evidence table retains only signature and polarity. -/
def MemoryFact.aggregateKey
    {Memory : Type uM} {Signature : Type uS} {Query : Type uQ}
    {Program : Type uP} {Target : Type uT} {Polarity : Type uPol}
    {Lineage : Type uL}
    (fact : MemoryFact Memory Signature Query Program Target Polarity Lineage) :
    Signature × Polarity :=
  (fact.signature, fact.polarity)

/-- The competence edge retained by a witness-complete program/target ledger. -/
def MemoryFact.competenceEdge
    {Memory : Type uM} {Signature : Type uS} {Query : Type uQ}
    {Program : Type uP} {Target : Type uT} {Polarity : Type uPol}
    {Lineage : Type uL}
    (fact : MemoryFact Memory Signature Query Program Target Polarity Lineage) :
    Program × Target :=
  (fact.program, fact.solvedTarget)

/-- The address edge needed to ask which program was made reachable for a
query. -/
def MemoryFact.addressEdge
    {Memory : Type uM} {Signature : Type uS} {Query : Type uQ}
    {Program : Type uP} {Target : Type uT} {Polarity : Type uPol}
    {Lineage : Type uL}
    (fact : MemoryFact Memory Signature Query Program Target Polarity Lineage) :
    Query × Program :=
  (fact.query, fact.program)

section AggregateProjection

variable {Memory : Type uM} {Signature : Type uS} {Query : Type uQ}
variable {Program : Type uP} {Target : Type uT} {Polarity : Type uPol}
variable {Lineage : Type uL}
local notation "EvidenceMemory" =>
  Finset (MemoryFact Memory Signature Query Program Target Polarity Lineage)

/-- Count atomic facts after projecting them to the aggregate-table key. -/
noncomputable def aggregateEvidenceCount
    (memory : EvidenceMemory) (key : Signature × Polarity) : ℕ :=
  by
    classical
    exact (memory.filter (fun fact ↦ fact.aggregateKey = key)).card

@[simp] theorem aggregateEvidenceCount_singleton_at_key
    (fact : MemoryFact Memory Signature Query Program Target Polarity Lineage) :
    aggregateEvidenceCount {fact} fact.aggregateKey = 1 := by
  classical
  unfold aggregateEvidenceCount
  rw [Finset.filter_eq_self.mpr]
  · simp
  · intro candidate candidateIn
    have : candidate = fact := Finset.mem_singleton.mp candidateIn
    subst candidate
    rfl

@[simp] theorem aggregateEvidenceCount_singleton_away
    (fact : MemoryFact Memory Signature Query Program Target Polarity Lineage)
    (key : Signature × Polarity) (hne : fact.aggregateKey ≠ key) :
    aggregateEvidenceCount {fact} key = 0 := by
  classical
  simp [aggregateEvidenceCount, hne]

/-- An estimand respects aggregate collisions when any two facts sharing an
aggregate key receive the same value. -/
def RespectsAggregateCollisions {Estimand : Type*}
    (estimand :
      MemoryFact Memory Signature Query Program Target Polarity Lineage → Estimand) :
    Prop :=
  ∀ left right : MemoryFact Memory Signature Query Program Target Polarity Lineage,
    left.aggregateKey = right.aggregateKey → estimand left = estimand right

/-- Universal property of the aggregate projection.  An estimand is recoverable
from the aggregate key *exactly* when it respects aggregate collisions.  The
forward direction is the reason each negative result below needs only one
colliding pair; the reverse direction constructs the decoder rather than
assuming one, so the positive boundary is not a restatement of its own
hypothesis. -/
theorem recoverable_iff_respectsAggregateCollisions
    {Estimand : Type*} [Nonempty Estimand]
    (estimand :
      MemoryFact Memory Signature Query Program Target Polarity Lineage → Estimand) :
    (∃ decoder : Signature × Polarity → Estimand,
        ∀ fact, decoder fact.aggregateKey = estimand fact) ↔
      RespectsAggregateCollisions estimand := by
  classical
  constructor
  · rintro ⟨decoder, decodes⟩ left right sameKey
    rw [← decodes left, ← decodes right, sameKey]
  · intro respects
    refine ⟨fun key ↦
      if witnessed :
          ∃ candidate :
            MemoryFact Memory Signature Query Program Target Polarity Lineage,
            candidate.aggregateKey = key
        then estimand witnessed.choose
        else Classical.arbitrary Estimand, ?_⟩
    intro fact
    dsimp only
    split
    · next witnessed => exact respects _ _ witnessed.choose_spec
    · next unwitnessed => exact absurd ⟨fact, rfl⟩ unwitnessed

/-- Aggregate equality cannot uniformly recover program identity when two
facts collide at the same signature/polarity key. -/
theorem aggregateKey_does_not_recover_program
    {left right :
      MemoryFact Memory Signature Query Program Target Polarity Lineage}
    (sameAggregate : left.aggregateKey = right.aggregateKey)
    (differentProgram : left.program ≠ right.program) :
    ¬ ∃ recover : Signature × Polarity → Program,
      ∀ fact : MemoryFact Memory Signature Query Program Target Polarity Lineage,
        recover fact.aggregateKey = fact.program := by
  exact no_uniform_recovery_of_observation_collision
    MemoryFact.aggregateKey MemoryFact.program sameAggregate differentProgram

/-- The same collision boundary applies to competence, which contains both
program identity and the solved target. -/
theorem aggregateKey_does_not_recover_competence
    {left right :
      MemoryFact Memory Signature Query Program Target Polarity Lineage}
    (sameAggregate : left.aggregateKey = right.aggregateKey)
    (differentCompetence : left.competenceEdge ≠ right.competenceEdge) :
    ¬ ∃ recover : Signature × Polarity → Program × Target,
      ∀ fact : MemoryFact Memory Signature Query Program Target Polarity Lineage,
        recover fact.aggregateKey = fact.competenceEdge := by
  exact no_uniform_recovery_of_observation_collision
    MemoryFact.aggregateKey MemoryFact.competenceEdge
    sameAggregate differentCompetence

/-- Aggregate counts also erase query-to-program accessibility. -/
theorem aggregateKey_does_not_recover_accessibility
    {left right :
      MemoryFact Memory Signature Query Program Target Polarity Lineage}
    (sameAggregate : left.aggregateKey = right.aggregateKey)
    (differentAddress : left.addressEdge ≠ right.addressEdge) :
    ¬ ∃ recover : Signature × Polarity → Query × Program,
      ∀ fact : MemoryFact Memory Signature Query Program Target Polarity Lineage,
        recover fact.aggregateKey = fact.addressEdge := by
  exact no_uniform_recovery_of_observation_collision
    MemoryFact.aggregateKey MemoryFact.addressEdge
    sameAggregate differentAddress

/-- Lineage provenance is likewise not recoverable from the aggregate key. -/
theorem aggregateKey_does_not_recover_lineage
    {left right :
      MemoryFact Memory Signature Query Program Target Polarity Lineage}
    (sameAggregate : left.aggregateKey = right.aggregateKey)
    (differentLineage : left.lineage ≠ right.lineage) :
    ¬ ∃ recover : Signature × Polarity → Lineage,
      ∀ fact : MemoryFact Memory Signature Query Program Target Polarity Lineage,
        recover fact.aggregateKey = fact.lineage := by
  exact no_uniform_recovery_of_observation_collision
    MemoryFact.aggregateKey MemoryFact.lineage
    sameAggregate differentLineage

/-! ## Availability, routing, and direct-target coverage -/

/-- All competence targets present in storage, independently of routing. -/
noncomputable def availableTargets (memory : EvidenceMemory) : Finset Target := by
  classical
  exact memory.image MemoryFact.solvedTarget

/-- Facts whose program is actually selected by the router for their query. -/
noncomputable def routedMemory
    (memory : EvidenceMemory) (router : Query → Finset Program) : EvidenceMemory :=
  by
    classical
    exact memory.filter (fun fact ↦ fact.program ∈ router fact.query)

noncomputable def routedTargets
    (memory : EvidenceMemory) (router : Query → Finset Program) : Finset Target :=
  availableTargets (routedMemory memory router)

/-- Every available target has at least one stored witness selected at its
recorded query. -/
def WitnessCompleteRouting
    (memory : EvidenceMemory) (router : Query → Finset Program) : Prop :=
  ∀ target ∈ availableTargets memory,
    ∃ fact ∈ memory,
      fact.solvedTarget = target ∧ fact.program ∈ router fact.query

theorem routedTargets_subset_availableTargets
    (memory : EvidenceMemory) (router : Query → Finset Program) :
    routedTargets memory router ⊆ availableTargets memory := by
  classical
  intro target targetRouted
  rcases Finset.mem_image.mp targetRouted with ⟨fact, factRouted, rfl⟩
  exact Finset.mem_image.mpr
    ⟨fact, (Finset.mem_filter.mp factRouted).1, rfl⟩

/-- Routing attains all stored competence exactly when it is witness-complete. -/
theorem routedTargets_eq_availableTargets_iff
    (memory : EvidenceMemory) (router : Query → Finset Program) :
    routedTargets memory router = availableTargets memory ↔
      WitnessCompleteRouting memory router := by
  classical
  constructor
  · intro equality target targetAvailable
    have targetRouted : target ∈ routedTargets memory router := by
      rw [equality]
      exact targetAvailable
    rcases Finset.mem_image.mp targetRouted with ⟨fact, factRouted, factTarget⟩
    have routedParts := Finset.mem_filter.mp factRouted
    exact ⟨fact, routedParts.1, factTarget, routedParts.2⟩
  · intro complete
    apply Finset.Subset.antisymm
      (routedTargets_subset_availableTargets memory router)
    intro target targetAvailable
    rcases complete target targetAvailable with
      ⟨fact, factStored, factTarget, factSelected⟩
    exact Finset.mem_image.mpr
      ⟨fact, Finset.mem_filter.mpr ⟨factStored, factSelected⟩, factTarget⟩

/-- Facts whose originating query names the target they solve.  Collateral
discoveries remain available facts but are not direct-target hits. -/
noncomputable def directTargetMemory
    (memory : EvidenceMemory) (queryTarget : Query → Target) : EvidenceMemory :=
  by
    classical
    exact memory.filter (fun fact ↦ queryTarget fact.query = fact.solvedTarget)

noncomputable def directTargetCoverage
    (memory : EvidenceMemory) (queryTarget : Query → Target) : ℕ :=
  (availableTargets (directTargetMemory memory queryTarget)).card

theorem directTargetTargets_subset_availableTargets
    (memory : EvidenceMemory) (queryTarget : Query → Target) :
    availableTargets (directTargetMemory memory queryTarget) ⊆
      availableTargets memory := by
  classical
  intro target targetDirect
  rcases Finset.mem_image.mp targetDirect with ⟨fact, factDirect, rfl⟩
  exact Finset.mem_image.mpr
    ⟨fact, (Finset.mem_filter.mp factDirect).1, rfl⟩

end AggregateProjection

/-! ## Hub concentration fixture -/

/-- One program covers two targets while a second program covers one. -/
def hubSolveRelation : SolveRelation Bool ℕ :=
  {(false, 0), (false, 1), (true, 2)}

theorem hubSolveRelation_degree :
    programTargetDegree hubSolveRelation false = 2 := by
  decide

theorem hubSolveRelation_coverage :
    targetCoverage hubSolveRelation = 3 := by
  decide

/-- Leave-one-program-out removes two of the three covered targets: broad
aggregate coverage can therefore be carried by one reusable program. -/
theorem hubSolveRelation_leaveOneProgram :
    targetCoverage (withoutProgram hubSolveRelation false) = 1 ∧
      exclusiveTargetContribution hubSolveRelation false = 2 := by
  decide

/-- The generic accounting identity exactly decomposes this hub fixture. -/
theorem hubSolveRelation_coverage_decomposition :
    targetCoverage (withoutProgram hubSolveRelation false) +
        exclusiveTargetContribution hubSolveRelation false =
      targetCoverage hubSolveRelation := by
  exact targetCoverage_withoutProgram_add_exclusive hubSolveRelation false

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
