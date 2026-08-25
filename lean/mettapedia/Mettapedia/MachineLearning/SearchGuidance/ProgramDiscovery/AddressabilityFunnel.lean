import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AddressableEvidenceMemory

/-!
# The addressability funnel

Stored competence and selected search results are the endpoints of a sequence
of distinct interventions.  This module keeps the five target projections
separate and proves the exact cardinal accounting between them.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

/-- Target sets observed at the five addressability stages.  Each transition
may discard targets but may not manufacture a target absent from its input. -/
structure AddressabilityFunnel (Target : Type*) [DecidableEq Target] where
  stored : Finset Target
  retrieved : Finset Target
  used : Finset Target
  entersBeam : Finset Target
  selected : Finset Target
  retrieved_subset_stored : retrieved ⊆ stored
  used_subset_retrieved : used ⊆ retrieved
  entersBeam_subset_used : entersBeam ⊆ used
  selected_subset_entersBeam : selected ⊆ entersBeam

namespace AddressabilityFunnel

variable {Target : Type*} [DecidableEq Target]

/-- Every selected target was present in storage. -/
theorem selected_subset_stored (funnel : AddressabilityFunnel Target) :
    funnel.selected ⊆ funnel.stored :=
  funnel.selected_subset_entersBeam.trans
    (funnel.entersBeam_subset_used.trans
      (funnel.used_subset_retrieved.trans funnel.retrieved_subset_stored))

/-- Loss at one stage is the cardinality removed at that transition. -/
def stageGap (upstream downstream : Finset Target) : ℕ :=
  upstream.card - downstream.card

/-- The four stage losses telescope exactly to stored-minus-selected. -/
theorem gap_decomposition (funnel : AddressabilityFunnel Target) :
    stageGap funnel.stored funnel.retrieved +
        stageGap funnel.retrieved funnel.used +
        stageGap funnel.used funnel.entersBeam +
        stageGap funnel.entersBeam funnel.selected =
      stageGap funnel.stored funnel.selected := by
  have hsr : funnel.retrieved.card ≤ funnel.stored.card :=
    Finset.card_le_card funnel.retrieved_subset_stored
  have hru : funnel.used.card ≤ funnel.retrieved.card :=
    Finset.card_le_card funnel.used_subset_retrieved
  have hub : funnel.entersBeam.card ≤ funnel.used.card :=
    Finset.card_le_card funnel.entersBeam_subset_used
  have hbs : funnel.selected.card ≤ funnel.entersBeam.card :=
    Finset.card_le_card funnel.selected_subset_entersBeam
  unfold stageGap
  omega

/-- Retrieval loses nothing exactly when every stored target is retrieved. -/
theorem retrieved_eq_stored_iff (funnel : AddressabilityFunnel Target) :
    funnel.retrieved = funnel.stored ↔
      ∀ target ∈ funnel.stored, target ∈ funnel.retrieved := by
  constructor
  · intro equality target targetStored
    rwa [equality]
  · intro complete
    apply Finset.Subset.antisymm funnel.retrieved_subset_stored
    intro target targetStored
    exact complete target targetStored

/-- Use loses nothing exactly when every retrieved target is used. -/
theorem used_eq_retrieved_iff (funnel : AddressabilityFunnel Target) :
    funnel.used = funnel.retrieved ↔
      ∀ target ∈ funnel.retrieved, target ∈ funnel.used := by
  constructor
  · intro equality target targetRetrieved
    rwa [equality]
  · intro complete
    apply Finset.Subset.antisymm funnel.used_subset_retrieved
    intro target targetRetrieved
    exact complete target targetRetrieved

/-- Beam entry loses nothing exactly when every used target enters the beam. -/
theorem entersBeam_eq_used_iff (funnel : AddressabilityFunnel Target) :
    funnel.entersBeam = funnel.used ↔
      ∀ target ∈ funnel.used, target ∈ funnel.entersBeam := by
  constructor
  · intro equality target targetUsed
    rwa [equality]
  · intro complete
    apply Finset.Subset.antisymm funnel.entersBeam_subset_used
    intro target targetUsed
    exact complete target targetUsed

/-- Selection loses nothing exactly when every beam-entering target wins. -/
theorem selected_eq_entersBeam_iff (funnel : AddressabilityFunnel Target) :
    funnel.selected = funnel.entersBeam ↔
      ∀ target ∈ funnel.entersBeam, target ∈ funnel.selected := by
  constructor
  · intro equality target targetInBeam
    rwa [equality]
  · intro complete
    apply Finset.Subset.antisymm funnel.selected_subset_entersBeam
    intro target targetInBeam
    exact complete target targetInBeam

end AddressabilityFunnel

section MemoryFunnel

universe uM uS uQ uP uT uPol uL

variable {Memory : Type uM} {Signature : Type uS} {Query : Type uQ}
variable {Program : Type uP} {Target : Type uT} {Polarity : Type uPol}
variable {Lineage : Type uL}

local notation "EvidenceMemory" =>
  Finset (MemoryFact Memory Signature Query Program Target Polarity Lineage)

/-- Start a five-stage funnel from the existing stored and routed projections.
The later stages remain explicit observations rather than being inferred. -/
noncomputable def memoryAddressabilityFunnel
    [DecidableEq Target]
    (memory : EvidenceMemory) (router : Query → Finset Program)
    (used entersBeam selected : Finset Target)
    (usedSubset : used ⊆ routedTargets memory router)
    (beamSubset : entersBeam ⊆ used)
    (selectedSubset : selected ⊆ entersBeam) :
    AddressabilityFunnel Target where
  stored := availableTargets memory
  retrieved := routedTargets memory router
  used := used
  entersBeam := entersBeam
  selected := selected
  retrieved_subset_stored := routedTargets_subset_availableTargets memory router
  used_subset_retrieved := usedSubset
  entersBeam_subset_used := beamSubset
  selected_subset_entersBeam := selectedSubset

/-- The first stage is lossless exactly at the existing witness-complete
routing boundary. -/
theorem memoryFunnel_retrieved_eq_stored_iff
    [DecidableEq Target]
    (memory : EvidenceMemory) (router : Query → Finset Program)
    (used entersBeam selected : Finset Target)
    (usedSubset : used ⊆ routedTargets memory router)
    (beamSubset : entersBeam ⊆ used)
    (selectedSubset : selected ⊆ entersBeam) :
    (memoryAddressabilityFunnel memory router used entersBeam selected
        usedSubset beamSubset selectedSubset).retrieved =
          (memoryAddressabilityFunnel memory router used entersBeam selected
            usedSubset beamSubset selectedSubset).stored ↔
      WitnessCompleteRouting memory router := by
  simpa [memoryAddressabilityFunnel] using
    routedTargets_eq_availableTargets_iff memory router

end MemoryFunnel

/-! ## Stage-separation counterexample -/

/-- Two interventions with separate before/after target projections. -/
structure RerankGenerationWorld (Target : Type*) [DecidableEq Target] where
  frozenBefore : Finset Target
  frozenAfter : Finset Target
  generatedBefore : Finset Target
  generatedAfter : Finset Target
  frozenBefore_subset_after : frozenBefore ⊆ frozenAfter
  generatedBefore_subset_after : generatedBefore ⊆ generatedAfter

namespace RerankGenerationWorld

variable {Target : Type*} [DecidableEq Target]

def frozenRerankingGain (world : RerankGenerationWorld Target) : ℕ :=
  world.frozenAfter.card - world.frozenBefore.card

def generationRetrievalGain (world : RerankGenerationWorld Target) : ℕ :=
  world.generatedAfter.card - world.generatedBefore.card

end RerankGenerationWorld

/-- Frozen-beam reranking changes nothing, while generation-time retrieval
introduces one reachable target. -/
def rerankGenerationSeparationFixture : RerankGenerationWorld Bool where
  frozenBefore := {false}
  frozenAfter := {false}
  generatedBefore := ∅
  generatedAfter := {true}
  frozenBefore_subset_after := by simp
  generatedBefore_subset_after := by simp

theorem rerank_zero_generation_positive_fixture :
    rerankGenerationSeparationFixture.frozenRerankingGain = 0 ∧
      rerankGenerationSeparationFixture.generationRetrievalGain = 1 := by
  decide

/-- A zero frozen-beam oracle is not an obstruction theorem for a retrieval
intervention performed during generation. -/
theorem frozenReranking_zero_does_not_force_generation_zero :
    ¬ ∀ world : RerankGenerationWorld Bool,
      world.frozenRerankingGain = 0 →
        world.generationRetrievalGain = 0 := by
  intro obstruction
  have falseConclusion := obstruction rerankGenerationSeparationFixture
    rerank_zero_generation_positive_fixture.1
  have positiveConclusion := rerank_zero_generation_positive_fixture.2
  omega

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
